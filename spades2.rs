/* Version de l'algo avec la nouvelle preuve de shuffle */

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

struct Arg {
    c : RistrettoPoint,
    c_d : RistrettoPoint,
    c_delta : RistrettoPoint,
    c_a : RistrettoPoint,
    f : Vec<Scalar>,
    f_delta : Vec<Scalar>,
    z : Scalar,
    z_delta : Scalar,
}

struct Zkrand {
    c : RistrettoPoint,
    cd : RistrettoPoint,
    ed_x : RistrettoPoint,
    ed_y : RistrettoPoint,
    fi : Vec<Scalar>,
    z : Scalar,
    m : Vec<Scalar>,
    arg : Arg,
    a : Vec<RistrettoPoint>,
    b : RistrettoPoint,
    g : RistrettoPoint,
    pkc : RistrettoPoint,
    e : Vec<RistrettoPoint>,
    s : Vec<RistrettoPoint>,
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

fn setup(n : &usize) -> (Vec<RistrettoPoint>,RistrettoPoint) {
    let mut rng = OsRng;
    let mut g : Vec<RistrettoPoint> = Vec::new();
    for i in 0..*n{
        let gi = RistrettoPoint::random(&mut rng);
        g.push(gi);
    }
    let h = RistrettoPoint::random(&mut rng);
    (g,h)
}

fn com(x : &Vec<Scalar>, r : &Scalar, g : &Vec<RistrettoPoint>, h : &RistrettoPoint) -> RistrettoPoint {
    let mut res = r * h;
    for i in 0..x.len(){
        res = res + x[i] * g[i];
    }
    res
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
    for _j in 0..4 {
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
fn rand(mut ch : Vec<Chiffre>, nums : &Vec<usize>, r : Vec<Scalar>, zk_r : &mut Vec<Zkrand>, g : &RistrettoPoint, pkc : &RistrettoPoint) -> Vec<Chiffre> {
    let mut ch2 : Vec <Chiffre> = Vec::new();
    for k in 0..52 {
        let c = Chiffre {x: ch[nums[k]].x + r[k] * g, y: ch[nums[k]].y + r[k] * pkc};
        ch2.push(c);
    }
    let zkr = zkrand(&ch,&ch2,&nums,&r,&g,&pkc);
    zk_r.push(zkr);
    ch = ch2;
    ch
}

fn zkrand(e : &Vec<Chiffre>, s : &Vec<Chiffre>, nums : &Vec<usize>, ra : &Vec<Scalar>, g : &RistrettoPoint, pkc : &RistrettoPoint) -> Zkrand {
    let n = nums.len();
    let mut rng = OsRng;
    let zero = Scalar::zero();
    let mut x = Vec::new();
    let mut y = Vec::new();
    for i in 0..n {
        x.push(e[i].x);
        y.push(s[i].x);
    }
    let (a,b) = setup(&n);
    let r = Scalar::random(&mut rng);
    let rad = Scalar::random(&mut rng);
    let rd = Scalar::random(&mut rng);
    let mut d : Vec<Scalar> = Vec::new();
    let mut dm : Vec<Scalar> = Vec::new();
    for i in 0..n {
        let di = Scalar::random(&mut rng);
        d.push(di);
        dm.push(-di);
    }
    let mut num : Vec<Scalar> = Vec::new();
    for i in 0..n {
        let numi = Scalar::from(nums[i] as u32);
        num.push(numi);
    }
    let c = com(&num,&r,&a,&b);
    let cd = com(&dm,&rd,&a,&b);
    let mut ed_x = s[0].x * dm[0];
    let mut ed_y = s[0].y * dm[0];
    for i in 1..n {
        ed_x = ed_x + s[i].x * dm[i];
        ed_y = ed_y + s[i].x * dm[i];
    }
    ed_x = ed_x + rad * g;
    ed_y = ed_y + rad * pkc;
    let mut u = Scalar::hash_from_bytes::<Sha512>(c.compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(cd.compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(ed_x.compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(ed_y.compress().as_bytes());
    u = Scalar::hash_from_bytes::<Sha512>(u.as_bytes());
    let mut t = Vec::new();
    for i in 1..(n+1) {
        let j : u64 = i.try_into().unwrap();
        let s = Scalar::from(j) * u;
        t.push(s);
    }
    let mut f = Vec::new();
    let mut z = Scalar::zero();
    for i in 0..n {
        let fi = t[nums[i]] + d[i];
        f.push(fi);
        z = z + t[nums[i]] * ra[i];
    }
    z = z + rad;
    let mut lambda = Scalar::hash_from_bytes::<Sha512>(z.as_bytes());
    for i in 0..n {
        lambda = lambda + Scalar::hash_from_bytes::<Sha512>(f[i].as_bytes());
    }
    lambda = Scalar::hash_from_bytes::<Sha512>(lambda.as_bytes());
    let rho = r * lambda + rd;
    let ch = lambda * c + cd + com(&f,&zero,&a,&b);
    let mut m = Vec::new();
    for i in 0..n {
        let s = Scalar::from(i as u32);
        let m_i = lambda * s + t[i];
        m.push(m_i);
    }
    let arg = arg(&ch,&nums,&rho,&m,&a,&b);
    let zkr = Zkrand{c : c, cd : cd, ed_x : ed_x, ed_y : ed_y, fi : f, z : z, m : m, arg : arg, a : a, b : b,g : *g, pkc : *pkc, e : x, s : y};
    zkr
}

fn arg(c : &RistrettoPoint, nums : &Vec<usize>, r : &Scalar, m : &Vec<Scalar>, g : &Vec<RistrettoPoint>, h : &RistrettoPoint) -> Arg {
    let n = nums.len();
    let mut rng = OsRng;
    let mut x = Scalar::hash_from_bytes::<Sha512>(m[0].as_bytes());
    for i in 1..n {
        x = x + Scalar::hash_from_bytes::<Sha512>(m[i].as_bytes());
    }
    x = Scalar::hash_from_bytes::<Sha512>(x.as_bytes());
    let mut d : Vec<Scalar> = Vec::new();
    for i in 0..n {
        let di = Scalar::random(&mut rng);
        d.push(di);
    }
    let rd = Scalar::random(&mut rng);
    let r_delta = Scalar::random(&mut rng);
    let mut delta = Vec::new();
    delta.push(d[0]);
    for i in 1..(n-1) {
        let t = Scalar::random(&mut rng);
        delta.push(t);
    }
    delta.push(Scalar::zero());
    let mut a = Vec::new();
    for i in 0..n {
        let mut a_i = Scalar::one();
        for j in 0..=i {
            a_i = a_i * (m[nums[j]] - x);
        }
        a.push(a_i);
    }
    let r_a = Scalar::random(&mut rng);
    let c_d = com(&d,&rd,&g,&h);
    let mut com_delta = Vec::new();
    let mut com_a = Vec::new();
    for i in 0..(n-1) {
        let c_delta_i = - delta[i] * d[i+1];
        let c_a_i = delta[i+1] - (m[nums[i+1]] - x) * delta[i] - a[i] * d[i+1];
        com_delta.push(c_delta_i);
        com_a.push(c_a_i);
    }
    let c_delta = com(&com_delta,&r_delta,&g,&h);
    let c_a = com(&com_a,&r_a,&g,&h);
    let mut e = Scalar::hash_from_bytes::<Sha512>(c_d.compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(c_delta.compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(c_a.compress().as_bytes());
    e = Scalar::hash_from_bytes::<Sha512>(e.as_bytes());
    let mut f = Vec::new();
    for i in 0..n {
        let f_i = e * m[nums[i]] + d[i];
        f.push(f_i);
    }
    let z = e * r + rd;
    let mut f_delta = Vec::new();
    for i in 0..(n-1) {
        let f_delta_i = e * (delta[i+1] - (m[nums[i+1]] - x) * delta[i] - a[i] * d[i+1]) - delta[i] * d[i+1];
        f_delta.push(f_delta_i);
    }
    let z_delta = e * r_a + r_delta;
    let arg = Arg{c : *c, c_d : c_d, c_delta : c_delta, c_a : c_a, f : f, f_delta : f_delta, z : z, z_delta : z_delta};
    arg
}

fn verirand(zkr : &Zkrand) -> u8 {
    let mut e = Scalar::hash_from_bytes::<Sha512>(zkr.arg.c_d.compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(zkr.arg.c_delta.compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(zkr.arg.c_a.compress().as_bytes());
    e = Scalar::hash_from_bytes::<Sha512>(e.as_bytes());
    let ga1 = e * zkr.arg.c + zkr.arg.c_d;
    let ga2 = e * zkr.arg.c_a + zkr.arg.c_delta;
    let dr1 = com(&zkr.arg.f,&zkr.arg.z,&zkr.a,&zkr.b);
    let dr2 = com(&zkr.arg.f_delta,&zkr.arg.z_delta,&zkr.a,&zkr.b);
    if ga1 != dr1 {
        return 0
    }
    if ga2 != dr2 {
        return 0
    }
    let mut y = Vec::new();
    let mut x = Scalar::hash_from_bytes::<Sha512>(zkr.m[0].as_bytes());
    for i in 1..52 {
        x = x + Scalar::hash_from_bytes::<Sha512>(zkr.m[i].as_bytes());
    }
    x = Scalar::hash_from_bytes::<Sha512>(x.as_bytes());
    let k = e * x;
    y.push(zkr.arg.f[0] - k);
    for i in 1..52 {
        let mut y_i = y[i-1] * (zkr.arg.f[i] - k) + zkr.arg.f_delta[i-1];
        y_i = e.invert() * y_i;
        y.push(y_i);
    }
    let mut dr3 = Scalar::one();
    for i in 0..52 {
        dr3 = dr3 * (zkr.m[i] - x);
    }
    dr3 = e * dr3;
    if y[51] != dr3 {
        return 0
    }
    let dr_x = zkr.z * zkr.g;
    let dr_y = zkr.z *akr.pkc;
    let mut u = Scalar::hash_from_bytes::<Sha512>(zkr.c.compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(zkr.cd.compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(zkr.ed_x.compress().as_bytes()) + Scalar::hash_from_bytes::<Sha512>(zkr.ed_y.compress().as_bytes());
    u = Scalar::hash_from_bytes::<Sha512>(u.as_bytes());
    let mut t = Vec::new();
    for i in 1..53 {
        let j : u64 = i.try_into().unwrap();
        let s = Scalar::from(j) * u;
        t.push(s);
    }
    let mut ga_x = (-t[0] * zkr.e[0].x) + zkr.fi[0] * zkr.s[0].x;
    for i in 1..52 {
        ga_x = ga_x + (-t[i] * zkr.e[i].x) + zkr.fi[i] * zkr.s[i].x;
    }
    ga_x = ga_x + zkr.ed_x;
    if ga_x != dr_x {
        return 0
    }
    let mut ga_y = (-t[0] * zkr.e[0].y) + zkr.fi[0] * zkr.s[0].y;
    for i in 1..52 {
        ga_y = ga_y + (-t[i] * zkr.e[i].y) + zkr.fi[i] * zkr.s[i].y;
    }
    ga_y = ga_y + zkr.ed_y;
    if ga_y != dr_y {
        return 0
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
    let pij = Zktheta{theta: *theta,y: y,z: z,g: *g};
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
