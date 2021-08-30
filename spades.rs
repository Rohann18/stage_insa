/* Version de l'alogo avec la preuve rand faite à la Schnorr*/

extern crate curve25519_dalek;
extern crate rand_core;
extern crate rand;
extern crate sha2;

use rand_core::OsRng;
use curve25519_dalek::constants;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use rand::seq::SliceRandom;
use rand::thread_rng;
use rand::Rng;
use std::convert::TryInto;
use std::time::Instant;
use sha2::Sha512;


struct Chiffre {
    x : RistrettoPoint,
    y : RistrettoPoint,
}

struct Carte {
    couleur : u16,
    valeur : u16,
}

struct Zkrand {
    g : RistrettoPoint,
    pkc : RistrettoPoint,
    g1 : RistrettoPoint,
    g2 : RistrettoPoint,
    pk1 : Vec<RistrettoPoint>,
    pk2 : Vec<RistrettoPoint>,
    y1 : Vec<RistrettoPoint>,
    y2 : Vec<RistrettoPoint>,
    z : Vec<Scalar>,
    c : Vec<Scalar>,
}

struct Zktheta {
    theta : RistrettoPoint,
    y : RistrettoPoint,
    z : Scalar,
    g : RistrettoPoint,
}

struct State {
    alpha : u16,
    suit : u16,
    u : Vec<Vec<usize>>,
}

// Valeurs à mettre dans le struct : la carte id, la clé publique pk, le chiffre ch, t1, t2, z, g

struct Zkpi0 {
    id : Carte,
    pk : RistrettoPoint,
    ch : Chiffre,
    t1 : RistrettoPoint,
    t2 : RistrettoPoint,
    z : Scalar,
    g : RistrettoPoint,
}

// Valeurs à retourner : g1, g2, pk1, pk2, y1, y2, z, c, l

struct Zkpij {
    b : bool,
    g1 : RistrettoPoint,
    g2 : RistrettoPoint,
    pk1 : RistrettoPoint,
    pk2 : Vec<RistrettoPoint>,
    y1 : Vec<RistrettoPoint>,
    y2 : Vec<RistrettoPoint>,
    z : Vec<Scalar>,
    c : Vec<Scalar>,
}

fn deck() -> Vec <Carte> {
    let mut deck : Vec <Carte> = Vec::new();
    for i in 0..52 {
        let j = i % 13;
        let k = i / 13;
        let carte = Carte { couleur : k+1, valeur : j+1};
        deck.push(carte);
    }
    deck
}

fn init() -> RistrettoPoint {
    let mut rng = OsRng;
    let g = RistrettoPoint::random(&mut rng);
    g
}

fn keygen(g : RistrettoPoint) -> (Scalar, RistrettoPoint){
    let mut rng = OsRng;
    let sk : Scalar = Scalar::random(&mut rng);
    let pk : RistrettoPoint = g * sk;
    (sk,pk)
}

fn fromcarte_to_nb(carte: &Carte) -> Scalar {
    let nb = carte.couleur * 100 + carte.valeur;
    let s : Scalar = Scalar::from(nb);
    s
}


fn gkeygen(mut ch : Vec <Chiffre> ,chiffre : &mut Vec<Chiffre>,  sk : &Vec <Scalar>, g : &RistrettoPoint, pkc : &RistrettoPoint) {
    let time2 = Instant::now();
    let mut rng = thread_rng();
    let mut rng2 = OsRng;
    let mut nums : Vec<usize> = (0..52).collect();
    let mut zk_r = Vec::new();
    for _j in 1..5 {
        // shuffle permet de mélanger tous les nombres de la variable nums aléatoirement
        nums.shuffle(&mut rng);
        let mut r : Vec<Scalar> = Vec::new();
        for _i in 0..52 {
            let ri : Scalar = Scalar::random(&mut rng2);
            r.push(ri);
        }
        ch = rand(ch,&nums,r,&mut zk_r,&g,&pkc);
    }
    for i in 0..4 {
        if verirand(&zk_r[i]) == 0 {
            eprintln!("Erreur : Vérification de la valeur de r fausse");
        }
    }
    let new_time2 = Instant::now();
    println!("{:?}", new_time2.duration_since(time2));
    let b = &constants::RISTRETTO_BASEPOINT_POINT;
    let mut theta : Vec <Vec<RistrettoPoint>> = vec![vec![*b; 52];4];
    let mut piij : Vec<Zktheta>= Vec::new();
    for j in 0..4 {
        caltheta(&mut theta,&ch,sk[j],j,&mut piij);
    }
    for _i in 0..4 {
        *chiffre = calci(&ch,&theta,&piij);
    }
}

// Fonction ou il y aura une preuve ZK en retour aussi
fn rand(mut ch : Vec<Chiffre>, nums : &Vec<usize>, r : Vec<Scalar>, zk_r : &mut Vec<Vec<Zkrand>>, g : &RistrettoPoint, pkc : &RistrettoPoint) -> Vec<Chiffre> {
    let mut ch2 : Vec <Chiffre> = Vec::new();
    for k in 0..52 {
        let c = Chiffre {x: ch[nums[k]].x + r[k] * g, y: ch[nums[k]].y + r[k] * pkc};
        ch2.push(c);
    }
    let zkr = zkrand(&ch,&ch2,&nums,r,&g,&pkc);
    zk_r.push(zkr);
    ch = ch2;
    ch
}

fn zkrand(che : &Vec<Chiffre>, chs : &Vec<Chiffre>, nums : &Vec<usize>, r : Vec<Scalar>, g : &RistrettoPoint, pkc : &RistrettoPoint) -> Vec<Zkrand> {
    let mut zkr = Vec::new();
    for i in 0..52{
        let mut rng = OsRng;
        let mut indice = 53usize;
        let b = &constants::RISTRETTO_BASEPOINT_POINT;
        let zero = Scalar::zero();
        let mut pk1 : Vec<RistrettoPoint> = vec![*b;52];
        let mut pk2 : Vec<RistrettoPoint> = vec![*b;52];
        let mut y1 : Vec<RistrettoPoint> = vec![*b;52];
        let mut y2 : Vec<RistrettoPoint> = vec![*b;52];
        let mut c : Vec<Scalar> = vec![zero;52];
        let mut z : Vec<Scalar> = vec![zero;52];
        let mut som : Scalar = Scalar::zero();
        let ra : Scalar = Scalar::random(&mut rng);
        for k in 0..52{
            if i == nums[k] {
                y1[k] = ra * g;
                y2[k] = ra * pkc;
                indice = k;
                pk1[k] = chs[k].x;
                pk2[k] = chs[k].y;
            } else {
                z[k]= Scalar::random(&mut rng);
                c[k] = Scalar::random(&mut rng);
                y1[k] = z[k] * g - c[k] * (chs[k].x - che[i].x);
                y2[k] = z[k] * pkc - c[k] * (chs[k].y - che[i].y);
                pk1[k] = chs[k].x;
                pk2[k] = chs[k].y;
            }
        }
        let mut s = Scalar::zero();
        for i in 0..52 {
            let t = Scalar::hash_from_bytes::<Sha512>(y1[i].compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(y2[i].compress().as_bytes());
            s = s + t;
        }
        s = Scalar::hash_from_bytes::<Sha512>(s.as_bytes());
        if indice != 53 {
            for i in 0..52{
                som = som + c[i];
            }
            c[indice] = s - som;
            z[indice] = ra + r[indice] * c[indice];
        }
        let pij = Zkrand{g : *g, pkc : *pkc, g1 : che[i].x, g2 : che[i].y, pk1 : pk1, pk2 : pk2, y1 : y1, y2 : y2, z : z, c : c};
        zkr.push(pij);
    }
    zkr
}

fn verirand(zkr : &Vec<Zkrand>) -> u8 {
    for i in 0..52{
        let mut s = Scalar::zero();
        for j in 0..52 {
            let t = Scalar::hash_from_bytes::<Sha512>(zkr[i].y1[j].compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(zkr[i].y2[j].compress().as_bytes());
            s = s + t;
        }
        s = Scalar::hash_from_bytes::<Sha512>(s.as_bytes());
        let mut som = Scalar::zero();
        for j in 0..52{
            if (zkr[i].z[j] * zkr[i].g != zkr[i].y1[j] + zkr[i].c[j] * (zkr[i].pk1[j] - zkr[i].g1)) {
                println!("chemin n°1");
                return 0
            }
            if (zkr[i].z[j] * zkr[i].pkc != zkr[i].y2[j] + zkr[i].c[j] * (zkr[i].pk2[j] - zkr[i].g2)) {
                println!("chemin n°2");
                return 0
            }
            som = som + zkr[i].c[j];
        }
        if som != s {
            println!("chemin n°3");
            return 0
        }
    }
    return 1
}
// Fonction ou il y aura une preuve ZK en retour aussi
fn caltheta(theta : &mut Vec <Vec<RistrettoPoint>> , ch : &Vec<Chiffre> , sk : Scalar , n : usize, piij : &mut Vec<Zktheta>) {
    let mut i = 0;
    let mut j = 0;
    while i < 52 {
        if i < 13 * n || 13 * (n+1) - 1 < i {
            let th = ch [i].x * sk;
            theta[n][j] = th;
            let pij = zktheta(&th,&sk,&ch[i].x);
            piij.push(pij);
        }
        i += 1;
        j += 1;
    }
}

fn zktheta(theta : &RistrettoPoint, sk : &Scalar, g : &RistrettoPoint) -> Zktheta {
    let mut rng = OsRng;
    let r : Scalar = Scalar::random(&mut rng);
    let y = r * g;
    let b = Scalar::hash_from_bytes::<Sha512>(g.compress().as_bytes());
    let z = r + sk * b;
    let pij = Zktheta{theta: *theta, y: y, z: z, g: *g};
    pij
    // Retourne dans une struct toutes les valeurs nécessaire pour la vérification
}

fn veritheta(zk : &Zktheta) -> u8 {
    let b = Scalar::hash_from_bytes::<Sha512>(zk.g.compress().as_bytes());
    if zk.z * zk.g == zk.y + b * zk.theta {
        return 1
    } else {
        return 0
    }
}

fn calci(ch : &Vec<Chiffre> , theta : &Vec<Vec<RistrettoPoint>> , piij : &Vec<Zktheta>) -> Vec<Chiffre> {
    let mut ci : Vec <Chiffre> = Vec::new();
    let mut ind = vec![0usize; 3];
    for l in 0..4 {
        for i in 13*l..13*(l+1) {
            let mut indice = 0;
            if l == 0 {
                indice = 1;
            }
            let mut the = theta[indice][i];
            for j in 0..piij.len(){
                if piij[j].theta == theta[indice][i] {
                    ind[0] = j;
                }
            }
            let mut e = 1;
            for k in 1..4 {
                if k != indice && k != l {
                    the = the + theta[k][i];
                    for j in 0..piij.len(){
                        if piij[j].theta == theta[k][i] {
                            ind[e] = j;
                            e += 1;
                        }
                    }
                }
            }
            for i in 0..3 {
                if veritheta(&piij[ind[i]]) == 0{
                    eprintln!("Erreur : Vérification de la valeur de theta fausse");
                }
            }
            let res = ch[i].y - the;
            let c = Chiffre {x: ch[i].x, y: res};
            ci.push(c);
        }
    }
    ci
}

fn dec(ch : &Vec<Chiffre>, sk : &Scalar, deck : &Vec<Carte>, n : usize, g : &RistrettoPoint) -> Carte {
    let valeur = ch[n].y - (sk * ch[n].x);
    let mut card = Carte {couleur : 0, valeur : 0};
    for k in 0..52 {
        let carte = Carte {couleur : deck[k].couleur, valeur : deck[k].valeur};
        let nb = fromcarte_to_nb(&carte);
        if valeur == g * nb{
            card.couleur = carte.couleur;
            card.valeur = carte.valeur;
            break;
        }
    }
    card
}

// Fonction de déchiffrement permettant de reconstruire le deck de cartes mélangé
fn get_hand(deck : &Vec<Carte> , ch : &Vec<Chiffre> , sk : &Scalar , n : usize, g : &RistrettoPoint) {
    let mut decksor : Vec<Carte> = Vec::new();
    for i in 13*n..13*(n+1) {
        decksor.push(dec(&ch,&sk,&deck,i,&g));
    }
    affichage(&decksor,13);
}

fn affichage(deck : &Vec<Carte>, n : usize){
    for i in 0..n {
        println!("{} , {}",deck[i].couleur,deck[i].valeur);
    }
}

fn play(n : usize, sk : &Scalar, pk : &Vec<RistrettoPoint>, chiffre : &Vec<Chiffre>, state : &State, state2 : &mut State, deck : &Vec<Carte>, tour : usize, g : &RistrettoPoint, jt : &mut Vec<usize>) -> (usize,Carte,Zkpi0,Vec<Zkpij>,Vec<usize>) {
    let mut rng = thread_rng();
    let mut t = rng.gen_range(0..jt.len());
    while (ine(&state.u[n],&jt[t]) == 1){
        jt.remove(t);
        t = rng.gen_range(0..jt.len());
    }
    state2.u[n][tour] = jt[t].try_into().unwrap();
    let valeur = dec(&chiffre,&sk,&deck,jt[t],&g);
    println!("joueur n°{:?} : {},{}",n+1,valeur.couleur,valeur.valeur);
    if state.alpha == 4 {
        state2.alpha = 1;
        state2.suit = valeur.couleur;
    } else {
        state2.alpha = state.alpha + 1;
        state2.suit = state.suit;
    }
    let pi0 = zkpi0(&valeur,&pk[n],&g,&chiffre[jt[t]],&sk);
    let mut l = Vec::new();
    for i in 0..52 {
        if deck[i].couleur != state2.suit {
            l.push(i);
        }
    }
    let mut pij : Vec<Zkpij> = Vec::new();
    let zero = Scalar::zero();
    let b = &constants::RISTRETTO_BASEPOINT_POINT;
    for j in 13*n..13*(n+1){
        if state2.suit == valeur.couleur {
            let pi = Zkpij{b : false, g1 : *g, g2 : chiffre[j].x, pk1 : pk[n], pk2 : vec![*b;39], y1 : vec![*b;39], y2 : vec![*b;39], z : vec![zero;39], c : vec![zero;39]};
            pij.push(pi);
            continue;
        }
        if ine(&state.u[n],&j) == 1 {
            //println!("Déjà dans Un");
            let pi = Zkpij{b : false, g1 : *g, g2 : chiffre[j].x, pk1 : pk[n], pk2 : vec![*b;39], y1 : vec![*b;39], y2 : vec![*b;39], z : vec![zero;39], c : vec![zero;39]};
            pij.push(pi);
            continue;
        } else {
            let carte = dec(&chiffre,&sk,&deck,j,&g);
            //println!("carte {:?}",j);
            let pi = zkpij(&deck,&l,&sk,&pk[n],&g,&chiffre[j],carte);
            pij.push(pi);
        }
    }
    //println!("{:?}",l);
    //println!("{:?}",state.u[n]);
    (t,valeur,pi0,pij,l)
}

fn zkpi0(id : &Carte, pk : &RistrettoPoint, g : &RistrettoPoint, ch : &Chiffre, sk : &Scalar) -> Zkpi0 {
    let mut rng = OsRng;
    let r : Scalar = Scalar::random(&mut rng);
    let t1 = r * g;
    let t2 = r * ch.x;
    let mut c = Scalar::hash_from_bytes::<Sha512>(t1.compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(t2.compress().as_bytes());
    c = Scalar::hash_from_bytes::<Sha512>(c.as_bytes());
    let z = r + sk * c;
    let carte = Carte{couleur : id.couleur,valeur : id.valeur};
    let ch1 = Chiffre{x : ch.x, y : ch.y};
    let pi0 = Zkpi0{id : carte, pk : *pk, ch : ch1, t1 : t1, t2 : t2, z : z, g : *g};
    pi0
    // Valeurs à mettre dans le struct : la carte id, la clé publique pk, le chiffre ch, t1, t2, z, g
}

fn veripi0(zk : Zkpi0) -> u8 {
    let pk2 = zk.ch.y - fromcarte_to_nb(&zk.id) * zk.g;
    let mut c = Scalar::hash_from_bytes::<Sha512>(zk.t1.compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(zk.t2.compress().as_bytes());
    c = Scalar::hash_from_bytes::<Sha512>(c.as_bytes());
    if (zk.z * zk.g == zk.t1 + c * zk.pk) && (zk.z * zk.ch.x == zk.t2 + c * pk2) {
        return 1
    } else {
        return 0
    }
}

fn ine(v : &Vec<usize>, j : &usize) -> u8{
    let k : usize = *j;
    if v.is_empty() {
        return 0
    }
    for i in 0..v.len() {
        if k == v[i].into() {
            return 1
        }
    }
    return 0
}

fn zkpij(deck : &Vec<Carte>, l : &Vec<usize>, sk : &Scalar, pk : &RistrettoPoint, g : &RistrettoPoint, ch : &Chiffre, id : Carte) -> Zkpij {
    let mut rng = OsRng;
    let mut indice = 39usize;
    let b = &constants::RISTRETTO_BASEPOINT_POINT;
    let zero = Scalar::zero();
    let mut pk2 = Vec::new();
    let mut y1 : Vec<RistrettoPoint> = vec![*b;39];
    let mut y2 : Vec<RistrettoPoint> = vec![*b;39];
    let mut c : Vec<Scalar> = vec![zero;39];
    let mut z : Vec<Scalar> = vec![zero;39];
    let mut som : Scalar = Scalar::zero();
    let r : Scalar = Scalar::random(&mut rng);
    for k in 0..39{
        if (deck[l[k]].couleur == id.couleur) && (deck[l[k]].valeur == id.valeur) {
            y1[k] = r * g;
            y2[k] = r * ch.x;
            indice = k;
            pk2.push(ch.y);
        } else {
            z[k]= Scalar::random(&mut rng);
            c[k] = Scalar::random(&mut rng);
            y1[k] = z[k] * g - c[k] * pk;
            y2[k] = z[k] * ch.x - c[k] * ch.y;
            pk2.push(ch.y + fromcarte_to_nb(&deck[l[k]]) * g);
        }
    }
    let mut s = Scalar::zero();
    for i in 0..39 {
        let t = Scalar::hash_from_bytes::<Sha512>(y1[i].compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(y2[i].compress().as_bytes());
        s = s + t;
    }
    s = Scalar::hash_from_bytes::<Sha512>(s.as_bytes());
    if indice != 39 {
        //println!("indice {:?}",indice);
        for i in 0..39{
            som = som + c[i];
        }
        c[indice] = s - som;
        z[indice] = r + sk * c[indice];
    }
    // Valeurs à retourner : g1, g2, pk1, pk2, y1, y2, z, c, l
    let pij = Zkpij{b : true, g1 : *g, g2 : ch.x, pk1 : *pk, pk2 : pk2, y1 : y1, y2 : y2, z : z, c : c};
    pij
}

fn veripij(pij : &Zkpij, deck : &Vec<Carte>, l : &Vec<usize>) -> u8 {
    let mut s = Scalar::zero();
    for i in 0..39 {
        let t = Scalar::hash_from_bytes::<Sha512>(pij.y1[i].compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(pij.y2[i].compress().as_bytes());
        s = s + t;
    }
    s = Scalar::hash_from_bytes::<Sha512>(s.as_bytes());
    let mut som = Scalar::zero();
    for i in 0..39{
        let pk2 = pij.pk2[i] - fromcarte_to_nb(&deck[l[i]]) * pij.g1;
        if (pij.z[i] * pij.g1 != pij.y1[i] + pij.c[i] * pij.pk1) {
            println!("chemin n°1");
            return 0
        }
        if (pij.z[i] * pij.g2 != pij.y2[i] + pij.c[i] * pk2) {
            println!("chemin n°2");
            return 0
        }
        som = som + pij.c[i];
    }
    if som != s {
        println!("chemin n°3");
        return 0
    }
    return 1
}

fn verif(n : usize, _chiffre : &Vec<Chiffre>, state : &State, state2 : &State, deck : &Vec<Carte>, tour : usize, t : usize, carte : Carte, pi0 : Zkpi0, pij : &Vec<Zkpij>, l : Vec<usize>, jt : &mut Vec<usize>) -> u8 {
    let mut i = 0;
    while i < 4 {
        if i == n {
            i += 1;
            continue;
        }
        for j in 0..13 {
            if state.u[i][j] != state2.u[i][j] {
                println!("choix n°1");
                return 0;
            }
        }
        i += 1;
    }
    for i in 0..tour {
        if jt[t] == state.u[n][i] || state.u[n][i] != state2.u[n][i] || jt[t] != state2.u[n][tour] {
            println!("choix n°2");
            return 0;
        }
    }
    if (state.alpha == 4||state.alpha == 0) && (state2.alpha != 1||state2.suit != carte.couleur) {
        println!("choix n°3");
        return 0;
    }
    if state.alpha != 4 && state.suit != 0 && (state2.alpha != state.alpha + 1||state2.suit != state.suit) {
        println!("choix n°4");
        return 0;
    }
    if veripi0(pi0) == 0 {
        println!("choix n°5");
        return 0
    }
    if (state2.suit != carte.couleur){
        for j in 0..13 {
            if pij[j].b == true {
                if veripij(&pij[j],&deck,&l) == 0 {
                    jt.remove(t);
                    println!("choix n°6");
                    return 0
                }
            }
        }
    }
    return 1;
}

fn copy(state : &mut State, state2 : &State) {
    state.alpha = state2.alpha;
    state.suit = state2.suit;
    for i in 0..4 {
        for j in 0..13 {
            state.u[i][j] = state2.u[i][j];
        }
    }
}

fn main() {
    let time = Instant::now();
    let deck : Vec <Carte> = deck();
    let g = init();
    let mut pk = Vec::new();
    let mut sk = Vec::new();
    for _i in 0..4 {
        let (a,b) = keygen(g);
        sk.push(a);
        pk.push(b);
    }
    let mut pkc : RistrettoPoint = pk[0];// PK est la somme des 4 clés publiques
    for i in 1..4{
        pkc = pkc + pk[i];
    }
    let mut ch : Vec <Chiffre> = Vec::new();
    let mut chiffre : Vec<Chiffre> = Vec::new();// ch correspnd au vecteur c dans le papier
    for i in 0..52 {
        let carte = Carte {couleur :deck[i].couleur , valeur :deck[i].valeur};
        let c : RistrettoPoint = pkc + g * fromcarte_to_nb(&carte);
        let d = Chiffre {x: g, y: c};
        let e = Chiffre {x: g, y: c};
        ch.push(d);
        chiffre.push(e);
    }
    gkeygen(ch,&mut chiffre,&sk,&g,&pkc);
    for n in 0..4 {
        get_hand(&deck,&chiffre,&sk[n],n,&g);
    }
    let mut state = State {alpha : 4, suit : 0, u : vec! [vec![53; 13];4]};
    let mut state2 = State {alpha : 0, suit : 0, u : vec! [vec![53; 13];4]};
    for tour in 0..13 {
        println!("tour n°{}",tour+1);
        for n in 0..4 {
            let mut jt : Vec<usize> = (13*n..13*(n+1)).collect();
            let mut veri = 0;
            while veri == 0{
                let (t,carte,pi0,pij,l) = play(n,&sk[n],&pk,&chiffre,&state,&mut state2,&deck,tour,&g,&mut jt);
                veri = verif(n,&chiffre,&state,&state2,&deck,tour,t,carte,pi0,&pij,l,&mut jt);
            }
            copy(&mut state,&state2);
        }
    }
    println!("{:?}",state.u);
    let new_time = Instant::now();
    println!("{:?}", new_time.duration_since(time));
}
