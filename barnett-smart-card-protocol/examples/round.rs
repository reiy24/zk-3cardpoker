#![allow(warnings, unused)]

use barnett_smart_card_protocol::discrete_log_cards;
use barnett_smart_card_protocol::BarnettSmartProtocol;

use std::io;
use anyhow;
use std::cmp;
use ark_ff::{to_bytes, UniformRand};
use ark_std::{rand::Rng, One};
use proof_essentials::utils::permutation::Permutation;
use proof_essentials::utils::rand::sample_vector;
use proof_essentials::zkp::proofs::{chaum_pedersen_dl_equality, schnorr_identification};
use rand::thread_rng;
use std::collections::HashMap;
use std::iter::Iterator;
use thiserror::Error;

// Choose elliptic curve setting
type Curve = starknet_curve::Projective;
type Scalar = starknet_curve::Fr;

// Instantiate concrete type for our card protocol
type CardProtocol<'a> = discrete_log_cards::DLCards<'a, Curve>;
type CardParameters = discrete_log_cards::Parameters<Curve>;
type PublicKey = discrete_log_cards::PublicKey<Curve>;
type SecretKey = discrete_log_cards::PlayerSecretKey<Curve>;

type Card = discrete_log_cards::Card<Curve>;
type MaskedCard = discrete_log_cards::MaskedCard<Curve>;
type RevealToken = discrete_log_cards::RevealToken<Curve>;

type ProofKeyOwnership = schnorr_identification::proof::Proof<Curve>;
type RemaskingProof = chaum_pedersen_dl_equality::proof::Proof<Curve>;
type RevealProof = chaum_pedersen_dl_equality::proof::Proof<Curve>;

#[derive(Error, Debug, PartialEq)]
pub enum GameErrors {
    #[error("No such card in hand")]
    CardNotFound,

    #[error("Invalid card")]
    InvalidCard,
}

#[derive(PartialEq, Clone, Copy, Eq, PartialOrd, Ord)]
pub enum Suite {
    Club,
    Diamond,
    Heart,
    Spade,
}

impl Suite {
    const VALUES: [Self; 4] = [Self::Club, Self::Diamond, Self::Heart, Self::Spade];
}

#[derive(PartialEq, PartialOrd, Clone, Copy, Eq, Ord)]
pub enum Value {
    Two,
    Three,
    Four,
    Five,
    Six,
    Seven,
    Eight,
    Nine,
    Ten,
    Jack,
    Queen,
    King,
    Ace,
}

impl Value {
    const VALUES: [Self; 13] = [
        Self::Two,
        Self::Three,
        Self::Four,
        Self::Five,
        Self::Six,
        Self::Seven,
        Self::Eight,
        Self::Nine,
        Self::Ten,
        Self::Jack,
        Self::Queen,
        Self::King,
        Self::Ace,
    ];
}

#[derive(PartialEq, Clone, Eq, Copy)]
pub struct ClassicPlayingCard {
    value: Value,
    suite: Suite,
}

impl ClassicPlayingCard {
    pub fn new(value: Value, suite: Suite) -> Self {
        Self { value, suite }
    }
}

impl std::fmt::Debug for ClassicPlayingCard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let suite = match self.suite {
            Suite::Club => "♣",
            Suite::Diamond => "♦",
            Suite::Heart => "♥",
            Suite::Spade => "♠",
        };

        let val = match self.value {
            Value::Two => "2",
            Value::Three => "3",
            Value::Four => "4",
            Value::Five => "5",
            Value::Six => "6",
            Value::Seven => "7",
            Value::Eight => "8",
            Value::Nine => "9",
            Value::Ten => "10",
            Value::Jack => "J",
            Value::Queen => "Q",
            Value::King => "K",
            Value::Ace => "A",
        };

        write!(f, "{}{}", val, suite)
    }
}

#[derive(Clone)]
struct Player {
    name: Vec<u8>,
    sk: SecretKey,
    pk: PublicKey,
    proof_key: ProofKeyOwnership,
    cards: Vec<MaskedCard>,
    opened_cards: Vec<Option<ClassicPlayingCard>>,
}

impl Player {
    pub fn new<R: Rng>(rng: &mut R, pp: &CardParameters, name: &Vec<u8>) -> anyhow::Result<Self> {
        let (pk, sk) = CardProtocol::player_keygen(rng, pp)?;
        let proof_key = CardProtocol::prove_key_ownership(rng, pp, &pk, &sk, name)?;
        Ok(Self {
            name: name.clone(),
            sk,
            pk,
            proof_key,
            cards: vec![],
            opened_cards: vec![],
        })
    }

    pub fn recieve_card(&mut self, card: MaskedCard) {
        self.cards.push(card);
        self.opened_cards.push(None);
    }

    pub fn peek_at_card(
        &mut self,
        parameters: &CardParameters,
        reveal_tokens: &mut Vec<(RevealToken, RevealProof, PublicKey)>,
        card_mappings: &HashMap<Card, ClassicPlayingCard>,
        card: &MaskedCard,
    ) -> Result<(), anyhow::Error> {
        let i = self.cards.iter().position(|&x| x == *card);

        let i = i.ok_or(GameErrors::CardNotFound)?;

        //TODO add function to create that without the proof
        let rng = &mut thread_rng();
        let own_reveal_token = self.compute_reveal_token(rng, parameters, card)?;
        reveal_tokens.push(own_reveal_token);

        let unmasked_card = CardProtocol::unmask(&parameters, reveal_tokens, card)?;
        let opened_card = card_mappings.get(&unmasked_card);
        let opened_card = opened_card.ok_or(GameErrors::InvalidCard)?;

        self.opened_cards[i] = Some(*opened_card);
        Ok(())
    }

    pub fn compute_reveal_token<R: Rng>(
        &self,
        rng: &mut R,
        pp: &CardParameters,
        card: &MaskedCard,
    ) -> anyhow::Result<(RevealToken, RevealProof, PublicKey)> {
        let (reveal_token, reveal_proof) =
            CardProtocol::compute_reveal_token(rng, &pp, &self.sk, &self.pk, card)?;

        Ok((reveal_token, reveal_proof, self.pk))
    }
}

//Every player will have to calculate this function for cards that are in play
pub fn open_card(
    parameters: &CardParameters,
    reveal_tokens: &Vec<(RevealToken, RevealProof, PublicKey)>,
    card_mappings: &HashMap<Card, ClassicPlayingCard>,
    card: &MaskedCard,
) -> Result<ClassicPlayingCard, anyhow::Error> {
    let unmasked_card = CardProtocol::unmask(&parameters, reveal_tokens, card)?;
    let opened_card = card_mappings.get(&unmasked_card);
    let opened_card = opened_card.ok_or(GameErrors::InvalidCard)?;

    Ok(*opened_card)
}

fn encode_cards<R: Rng>(rng: &mut R, num_of_cards: usize) -> HashMap<Card, ClassicPlayingCard> {
    let mut map: HashMap<Card, ClassicPlayingCard> = HashMap::new();
    let plaintexts = (0..num_of_cards)
        .map(|_| Card::rand(rng))
        .collect::<Vec<_>>();

    let mut i = 0;
    for value in Value::VALUES.iter().copied() {
        for suite in Suite::VALUES.iter().copied() {
            let current_card = ClassicPlayingCard::new(value, suite);
            map.insert(plaintexts[i], current_card);
            i += 1;
        }
    }

    map
}

fn main() -> anyhow::Result<()> {
    let m = 2;
    let n = 26;
    let num_of_cards = m * n;
    let rng = &mut thread_rng();

    let parameters = CardProtocol::setup(rng, m, n)?;
    let card_mapping = encode_cards(rng, num_of_cards);

    let mut dealer = Player::new(rng, &parameters, &to_bytes![b"Dealer"].unwrap())?;
    let mut player = Player::new(rng, &parameters, &to_bytes![b"Player"].unwrap())?;

    let mut dealer_balance: u32 = 100;
    let mut player_balance: u32 = 100;

    let players = vec![dealer.clone(), player.clone()];

    let key_proof_info = players
        .iter()
        .map(|p| (p.pk, p.proof_key, p.name.clone()))
        .collect::<Vec<_>>();

    // Each player should run this computation. Alternatively, it can be ran by a smart contract
    let joint_pk = CardProtocol::compute_aggregate_key(&parameters, &key_proof_info)?;

    // Each player should run this computation and verify that all players agree on the initial deck
    let deck_and_proofs: Vec<(MaskedCard, RemaskingProof)> = card_mapping
        .keys()
        .map(|card| CardProtocol::mask(rng, &parameters, &joint_pk, &card, &Scalar::one()))
        .collect::<Result<Vec<_>, _>>()?;

    let deck = deck_and_proofs
        .iter()
        .map(|x| x.0)
        .collect::<Vec<MaskedCard>>();

    // SHUFFLE TIME --------------
    // 1.a Dealer shuffles first
    let permutation = Permutation::new(rng, m * n);
    let masking_factors: Vec<Scalar> = sample_vector(rng, m * n);

    let (a_shuffled_deck, a_shuffle_proof) = CardProtocol::shuffle_and_remask(
        rng,
        &parameters,
        &joint_pk,
        &deck,
        &masking_factors,
        &permutation,
    )?;

    // 1.b everyone checks!
    CardProtocol::verify_shuffle(
        &parameters,
        &joint_pk,
        &deck,
        &a_shuffled_deck,
        &a_shuffle_proof,
    )?;

    //2.a Player 1 shuffles
    let permutation = Permutation::new(rng, m * n);
    let masking_factors: Vec<Scalar> = sample_vector(rng, m * n);

    let (k_shuffled_deck, k_shuffle_proof) = CardProtocol::shuffle_and_remask(
        rng,
        &parameters,
        &joint_pk,
        &a_shuffled_deck,
        &masking_factors,
        &permutation,
    )?;

    //2.b Everyone checks
    CardProtocol::verify_shuffle(
        &parameters,
        &joint_pk,
        &a_shuffled_deck,
        &k_shuffled_deck,
        &k_shuffle_proof,
    )?;

    // CARDS ARE SHUFFLED. ROUND OF THE GAME CAN BEGIN
    player.recieve_card(deck[0]);
    dealer.recieve_card(deck[1]);
    player.recieve_card(deck[2]);
    dealer.recieve_card(deck[3]);
    player.recieve_card(deck[4]);
    dealer.recieve_card(deck[5]);

    let player_rt_1 = player.compute_reveal_token(rng, &parameters, &deck[1])?;
    let player_rt_3 = player.compute_reveal_token(rng, &parameters, &deck[3])?;
    let player_rt_5 = player.compute_reveal_token(rng, &parameters, &deck[5])?;

    let dealer_rt_0 = dealer.compute_reveal_token(rng, &parameters, &deck[0])?;
    let dealer_rt_2 = dealer.compute_reveal_token(rng, &parameters, &deck[2])?;
    let dealer_rt_4 = dealer.compute_reveal_token(rng, &parameters, &deck[4])?;

    let mut rts_player_0 = vec![dealer_rt_0];
    let mut rts_player_2 = vec![dealer_rt_2];
    let mut rts_player_4 = vec![dealer_rt_4];
    let mut rts_dealer_1 = vec![player_rt_1];
    let mut rts_dealer_3 = vec![player_rt_3];
    let mut rts_dealer_5 = vec![player_rt_5];

    //At this moment players privately open their cards and only they know that values
    player.peek_at_card(&parameters, &mut rts_player_0, &card_mapping, &deck[0])?;
    dealer.peek_at_card(&parameters, &mut rts_dealer_1, &card_mapping, &deck[1])?;
    player.peek_at_card(&parameters, &mut rts_player_2, &card_mapping, &deck[2])?;
    dealer.peek_at_card(&parameters, &mut rts_dealer_3, &card_mapping, &deck[3])?;
    player.peek_at_card(&parameters, &mut rts_player_4, &card_mapping, &deck[4])?;
    dealer.peek_at_card(&parameters, &mut rts_dealer_5, &card_mapping, &deck[5])?;
    
    //Game Logic
    let ante: u32 = 10;
    let mut pot: u32 = 0;

    if player_balance >= ante && dealer_balance >= ante {
        player_balance = player_balance - ante;
        dealer_balance = dealer_balance - ante;
        pot = pot + 2 * ante;
        println!("You and the dealer have now bet an ante of {}.", ante);
    }
    else {
        println!("Insufficent funds!");
        return Ok(());
    }

    println!("Player: {:?} {:?} {:?}", player.opened_cards[0].unwrap(), player.opened_cards[1].unwrap(), player.opened_cards[2].unwrap());
    
    println!("How much would the player like to bet? Note that it must be greater than the ante of {}. Bet 0 to fold.", ante);

    let mut wager = String::new();
        
    io::stdin()
        .read_line(&mut wager)
        .expect("Failed to read line");

    let wager: u32 = match wager.trim().parse() {
        Ok(num) => num,
        Err(_) => return Ok(()),
    };

    if wager > ante && wager <= player_balance {
        player_balance = player_balance - wager;
        pot = pot + wager;
    }
    else if wager == 0 {
        dealer_balance = dealer_balance + pot;
        println!("Player folds. Dealer wins {}.", pot);
        pot = 0;
        return Ok(());
    }
    else {
        println!("Invalid bet.");
        return Ok(());
    }

    let dealer_values = [dealer.opened_cards[0].unwrap().value, 
                         dealer.opened_cards[1].unwrap().value, 
                         dealer.opened_cards[2].unwrap().value];
    
    // Dealer folds if high card is less than a Queen
    if dealer_values.iter().any(|v| v == &Value::Queen || v == &Value::King || v == &Value::Ace) && dealer_balance >= wager {
        dealer_balance = dealer_balance - wager;
        pot = pot + wager;
    }
    else {
        player_balance = player_balance + pot;
        println!("Dealer folds, as his best card is less than a Queen. Player wins {}.", pot);
        pot = 0;
        return Ok(());
    }

    //At this moment players reveal their cards to each other and everything becomes public

    //1.a everyone reveals the secret for their card
    let player_rt_0 = player.compute_reveal_token(rng, &parameters, &deck[0])?;
    let dealer_rt_1 = dealer.compute_reveal_token(rng, &parameters, &deck[1])?;
    let player_rt_2 = player.compute_reveal_token(rng, &parameters, &deck[2])?;
    let dealer_rt_3 = dealer.compute_reveal_token(rng, &parameters, &deck[3])?;
    let player_rt_4 = player.compute_reveal_token(rng, &parameters, &deck[4])?;
    let dealer_rt_5 = dealer.compute_reveal_token(rng, &parameters, &deck[5])?;

    //2. tokens for all other cards are exchanged
    //TODO add struct for this so that we can just clone
    let player_rt_1 = player.compute_reveal_token(rng, &parameters, &deck[1])?;
    let player_rt_3 = player.compute_reveal_token(rng, &parameters, &deck[3])?;
    let player_rt_5 = player.compute_reveal_token(rng, &parameters, &deck[5])?;

    let dealer_rt_0 = dealer.compute_reveal_token(rng, &parameters, &deck[0])?;
    let dealer_rt_2 = dealer.compute_reveal_token(rng, &parameters, &deck[2])?;
    let dealer_rt_4 = dealer.compute_reveal_token(rng, &parameters, &deck[4])?;

    let rt_0 = vec![player_rt_0, dealer_rt_0];
    let rt_1 = vec![player_rt_1, dealer_rt_1];
    let rt_2 = vec![player_rt_2, dealer_rt_2];
    let rt_3 = vec![player_rt_3, dealer_rt_3];
    let rt_4 = vec![player_rt_4, dealer_rt_4];
    let rt_5 = vec![player_rt_5, dealer_rt_5];

    //Everyone computes for each card (except for their own card):
    let player_card_0 = open_card(&parameters, &rt_0, &card_mapping, &deck[0])?;
    let dealer_card_0 = open_card(&parameters, &rt_1, &card_mapping, &deck[1])?;
    let player_card_1 = open_card(&parameters, &rt_2, &card_mapping, &deck[2])?;
    let dealer_card_1 = open_card(&parameters, &rt_3, &card_mapping, &deck[3])?;
    let player_card_2 = open_card(&parameters, &rt_4, &card_mapping, &deck[4])?;
    let dealer_card_2 = open_card(&parameters, &rt_5, &card_mapping, &deck[5])?;

    println!("Player: {:?} {:?} {:?}", player_card_0, player_card_1, player_card_2);
    println!("Dealer: {:?} {:?} {:?}", dealer_card_0, dealer_card_1, dealer_card_2);

    let mut player_values = vec![player_card_0.value, player_card_1.value, player_card_2.value];
    let mut dealer_values = vec![dealer_card_0.value, dealer_card_1.value, dealer_card_2.value];

    player_values.sort();
    dealer_values.sort();

    // Modularize process later. Add more complete tiebreaker logic.
    // TODO: Check whether either player has a straight flush.

    // Check whether either player has a three of a kind.
    if player_card_0.value == player_card_1.value && player_card_1.value == player_card_2.value {
        if dealer_card_0.value == dealer_card_1.value && dealer_card_1.value == dealer_card_2.value {
            if player_card_0.value > dealer_card_0.value {
                player_balance = player_balance + pot;
                println!("Player wins {} with higher 3 of a kind.", pot);
                pot = 0;
            } 
            else {
                dealer_balance = dealer_balance + pot;
                println!("Dealer wins {} with higher 3 of a kind.", pot);
                pot = 0;
            }
        }
        else {
            player_balance = player_balance + pot;
            println!("Player wins {} with 3 of a kind.", pot);
            pot = 0;
        }
    }
    else if dealer_card_0.value == dealer_card_1.value && dealer_card_1.value == dealer_card_2.value {
        dealer_balance = dealer_balance + pot;
        println!("Dealer wins {} with 3 of a kind.", pot);
        pot = 0;
    }

    // TODO: Check whether either player has a straight.

    // Check whether either player has a flush.
    if player_card_0.suite == player_card_1.suite && player_card_1.suite == player_card_2.suite {
        if dealer_card_0.suite == dealer_card_1.suite && dealer_card_1.suite == dealer_card_2.suite {
            if player_values[2] > dealer_values[2] {
                player_balance = player_balance + pot;
                println!("Player wins {} with higher flush.", pot);
                pot = 0;
            } 
            else {
                dealer_balance = dealer_balance + pot;
                println!("Dealer wins {} with higher flush.", pot);
                pot = 0;
            }
        }
        else {
            player_balance = player_balance + pot;
            println!("Player wins {} with flush.", pot);
            pot = 0;
        }
        return Ok(());
    }
    else if dealer_card_0.suite == dealer_card_1.suite && dealer_card_1.suite == dealer_card_2.suite {
        dealer_balance = dealer_balance + pot;
        println!("Dealer wins {} with flush.", pot);
        pot = 0;
        return Ok(());
    }

    // Check whether either player has a pair.
    if player_card_0.value == player_card_1.value || player_card_1.value == player_card_2.value {
        if dealer_card_0.value == dealer_card_1.value || dealer_card_1.value == dealer_card_2.value {
            if player_values[1] > dealer_values[1] {
                player_balance = player_balance + pot;
                println!("Player wins {} with higher pair.", pot);
                pot = 0;
            } 
            else {
                dealer_balance = dealer_balance + pot;
                println!("Dealer wins {} with higher pair.", pot);
                pot = 0;
            }
        }
        else {
            player_balance = player_balance + pot;
            println!("Player wins {} with pair.", pot);
            pot = 0;
        }
        return Ok(());
    }
    else if dealer_card_0.value == dealer_card_1.value || dealer_card_1.value == dealer_card_2.value {
        dealer_balance = dealer_balance + pot;
        println!("Dealer wins {} with pair.", pot);
        pot = 0;
        return Ok(());
    }

    // Check whether either player has a high card.
    if player_values[2] > dealer_values[2] {
        player_balance = player_balance + pot;
        println!("Player wins {} with high card.", pot);
        pot = 0;
    } 
    else {
        dealer_balance = dealer_balance + pot;
        println!("Dealer wins {} with high card.", pot);
        pot = 0;
    }

    Ok(())
}
