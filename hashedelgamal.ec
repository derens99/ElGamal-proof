(* Hashed el'gamal proof *)

require import AllCore Distr SmtMap DBool FSet.

type group.

op gid: group.

op (^^): group -> group -> group.

axiom grpA (x y z : group) : x ^^ y ^^ z = x ^^ (y ^^ z).

axiom grpI (x  : group) : x ^^ gid = x.

axiom grpC (x y : group) : x ^^ y = y ^^ x.

  (* exponent definitions *)

type exp.

op ( * ) : exp -> exp -> exp.

axiom expA (x y z : exp) : x * y * z = x * (y * z).

axiom expC (x y : exp) : x * y = y * x.

op dexp : exp distr.

axiom dexp_fu : is_full dexp.

axiom dexp_uni : is_uniform dexp.

axiom dexp_ll : is_lossless dexp.

op g : group.

op (^) : group -> exp -> group.

  (* forall (x : group), unique (q : exp), s.t. x = g^q *)

axiom generated (x : group) : exists (q : exp),  x = g ^ q.

axiom generated2 (x : group) (z : exp) : exists (q : exp), x ^ z = g ^ q ^ z.

axiom grexpA (q1 q2 : exp) : (g ^ q1) ^ q2 = g ^ (q1 * q2).

op gen (q : exp) = g ^ q.
axiom inj (q1 q2 : exp) : g^q1 = g^q2 => q1 = q2.

op gen_rel (x : group)(q : exp) : bool = x = g^q.

op e : exp.

op log (x : group) : exp = choiceb (gen_rel x) e.

print cancel.

lemma gen_log : cancel gen log.
    proof.
      rewrite /gen /log /cancel => q.
      have choice_g2q := choicebP ( gen_rel(g ^ q)) e.
      have /choice_g2q @/gen_rel/inj {2}-> //:
      exists(q' : exp), gen_rel (g^q) q'
      by rewrite /gen_rel; by exists q.        
  qed.
  
lemma log_gen : cancel log gen.
    proof.
      rewrite /gen /log /cancel => x.
      have @/gen_rel <-// := choicebP ( gen_rel x) e.
      rewrite generated.
    qed.

lemma grexpAll (x : group) (q1 q2 : exp) : (x ^ q1) ^q2 = x ^ (q1 * q2).
    proof.
      have ->: x = g ^ log x.
      have ->: g ^ log x = gen (log x).    
      by rewrite /gen.
      by rewrite log_gen.
     by rewrite !grexpA expA.
  qed.

      (* text definitions *)
type text.

op (+^) : text -> text -> text.

axiom textA (x y z : text) : x +^ y +^ z = x +^ (y +^ z).

op text0 : text.

axiom textC (x y : text) : x +^ y = y +^ x.

axiom textI (x : text) : x +^ text0 = x.

axiom textR (x : text) : x +^ x = text0.

op dtext : text distr.

axiom dtext_fu : is_full dtext.

axiom dtext_uni : is_uniform dtext.

axiom dtext_ll : is_lossless dtext.

type cipher = group * text.

module type RO = {
  proc * init() : unit

  proc f(x : group) : text
}.

(* Defining Correctness *)
module type ENC (RO : RO) = {
  proc key_gen() : group * exp

  proc enc(pubk : group, t : text) : cipher {RO.f}

  proc dec(privk : exp, c : cipher) : text {RO.f}
}.

(* concrete example of elgamal *)
      (* Random Oracle *)


module RO : RO = {
  var mp : (group, text) fmap (* finite map, table *)

  proc init() : unit = {
    mp <- empty;  (* empty map *)
  }

  proc f(x : group) : text = {
    var y : text;
    if (x \notin mp) { (* not in mp's domain *)
      y <$ dtext;   (* updating mp so as before but value of *)
      mp.[x] <- y;  (* x is what we randomly picked *)
    }
    return oget mp.[x]; (* mp.[x] is either None or Some t *)
  }
}.

(* module to check for correctness of encryption scheme.

    is correct if it the original input = final output when run through all funcitons with probability 1 *)

module Cor (Enc : ENC) = {
  module E = Enc(RO)
  
  proc main(x : text) : bool = {
  var pubk : group; var privk : exp; var c : cipher; var y : text;
    
    (pubk, privk) <@ E.key_gen();
      c <@ E.enc(pubk, x);
      y <@ E.dec(privk, c);
    return x = y;
  }
  
}.


module (HEG : ENC) (RO : RO) ={
  proc key_gen() : group * exp = {
    var q : exp;
    q <$ dexp;
    return (g ^ q, q);
  }

  proc enc(pubk : group, t : text) : cipher = {
      var r : exp;
    var u : text;
    r <$ dexp;
    
      (* Need to define pubk and privk. pubk = g ^ q and privk = q *)
    u <@ RO.f(pubk ^ r);

    (*pubk ^ r = (g ^ q) ^ r = g ^ (q * r)*)
    return (g ^ r, t +^ u);

  }

  proc dec(privk : exp, c : cipher) : text = {
    var u,v : text;
      var x : group;

    (x, u) <- c;
    v <@ RO.f(x ^ privk);
    return v +^ u;
    (* (g ^ r) ^ q = g ^ (r * q) = g ^ (q * r) *)
    (*t +^ u +^ u = t =^ textO = t *)
  }

}.


    (* prove encryption scheme is stateless *)

lemma enc_stateless (g1 g2 : glob HEG) : g1 = g2.
    proof.
      trivial.
  qed.

      (* prove encryption scheme is correct *)
lemma correctness : phoare[Cor(HEG).main : true ==> res] = 1%r.
    proof.
      proc.
    inline*.
    seq 13: (x1 = g ^ (q * r) /\ x2 = x1 /\ t = x /\ RO.mp.[x1] = Some u /\ u0 = t +^ u).  
    auto.
    seq 3: (pubk0 = g ^ q /\ privk = q).
    wp.
    auto.
    wp.
    auto.
    progress.
    apply dexp_ll.
    wp.
    seq 2: (pubk0 = g ^ q /\ privk = q /\ t = x).
    auto.
    auto.
    progress. 
    apply dexp_ll.
    sp.
    if.
    auto.
    progress.
    apply dtext_ll.
    by rewrite grexpA.
      by rewrite !grexpA expC.    
    rewrite get_set_sameE.
    by rewrite oget_some.
    auto.
    progress.
    by rewrite grexpA.
    by rewrite !grexpA expC.
    by rewrite get_some.
    hoare.
    simplify.
    auto.
    trivial.
    hoare.
    auto.
    trivial.
    rcondf 1.
auto; progress.
smt().
auto.
      progress.
    rewrite H oget_some.
      rewrite -textA.
      rewrite -textC.
    rewrite- textA.
    rewrite textR.
    rewrite textC textI.
    trivial.
    hoare.
    auto.
    seq 1: true.
    auto.
    sp.
    seq 1: (privk = q /\ pubk = g ^ q /\ pubk0 = pubk /\ t = x).
    auto.
    sp.
    if.
    auto.
    progress.
     by rewrite grexpA.
    by rewrite !grexpA expC.
      rewrite get_some.
    search  dom.
    smt(mem_set).
    by rewrite get_set_sameE oget_some.
    auto.
    progress.
    rewrite grexpA.
    auto.
    by rewrite !grexpA expC.
    by rewrite get_some.
    trivial.
  qed.


  module type ADV (RO : RO) = {
    proc * choose(pubk : group) : text * text {RO.f}

    proc guess(c : cipher) : bool {RO.f}
  }.

  
  module INDCPA (Adv : ADV) = {
    module A = Adv(RO)
    module Enc = HEG(RO)

    proc main() : bool = {
      var x1, x2 : text; var c : cipher; var choice, guess : bool;
      var pubk : group; var privk : exp;

      (* get pubk, similar to initializing EO *)
      (pubk, privk) <@ Enc.key_gen();
      

      (x1,x2) <@ A.choose(pubk);

      choice <$ {0,1};
        c <@ Enc.enc(pubk, choice ? x1 : x2);

        guess <@ A.guess(c);

      return choice = guess;
    }
  }.

  
  module type LCDH_ADV = {
    proc main(x1 x2: group) : group fset
  }.

  module LCDH (Adv : LCDH_ADV) = {
    proc main() : bool = {
    var q1, q2 : exp;
    var ys : group fset;
    q1 <$ dexp; q2 <$ dexp;
    ys <@ Adv.main(g^q1, g^q2);
      return mem ys (g^ (q1*q2));
      }
    }.

module RO_track : RO = {
  var mp : (group, text) fmap (* finite map, table *)
  var badHappened : bool

  proc init() : unit = {
    mp <- empty;  (* empty map *)
  }

  proc f(x : group) : text = {
      var y : text;
      if(x \in mp){
        badHappened <- true;
      }
    if (x \notin mp) { (* not in mp's domain *)
      y <$ dtext;   (* updating mp so as before but value of *)
      mp.[x] <- y;  (* x is what we randomly picked *)
    }
    return oget mp.[x]; (* mp.[x] is either None or Some t *)
  }
}.
  
 module G1 (Adv : ADV) = {
    module A = Adv(RO_track)
    module Enc = HEG(RO_track)

    proc main() : bool = {
      var x1, x2 : text; var c : cipher; var choice, guess : bool;
      var pubk, x : group; var privk : exp;
       var r : exp;
        var u,y,t : text;

      (* key_gen but inlined *)
       privk <$ dexp;
      pubk <- g ^ privk;
      

      (x1,x2) <@ A.choose(pubk);

        choice <$ {0,1};

        (* enc Inlined *)
       
        t <- (choice ? x1 : x2);
        r <$ dexp;
      (* randomly choosing a u inlined *)
        u <@ RO.f(pubk ^ r);

        x <- pubk ^ r;
      
      (* not sure how to access the same mp while inlining the RO, I think RO.mp works properly *)
        if (x \notin RO.mp) { (* not in mp's domain *)
           y <$ dtext;   (* updating mp so as before but value of *)
           RO.mp.[x] <- y;  (* x is what we randomly picked *)
        }

      u <- oget RO.mp.[x]; (* mp.[x] is either None or Some t *)

    

    c <- (g ^ r, t +^ u);

        guess <@ A.guess(c);

      return choice = guess;
    }
  }.

