(* Hashed el'gamal proof *)

require import AllCore Distr.

type group.

op gid: group.

op (^^): group -> group -> group.

axiom grpA (x y z : group) : x ^^ y ^^ z = x ^^ (y ^^ z).

axiom grpI (x  : group) : x ^^ gid = x.

axiom grpC (x y : group) : x ^^ y = y ^^ x.

  (* exponent definitions *)

type exp.

op (+*) : exp -> exp -> exp.

axiom expA (x y z : exp) : x +* y +* z = x +* (y +* z).

axiom expC (x y : exp) : x +* y = y +* x.

op dexp : exp distr.

op g : group.

op (^) : group -> exp -> group.

  (* forall (x : group), unique (q : exp), s.t. x = g^q *)

axiom uni : forall (x : group), exists (q : exp),  x = g ^ q.

axiom grexpA (q1 q2 : exp) : (g ^ q1) ^ q2 = g ^ (q1 +* q2).

lemma grexpAll (x : group) (q1 q2 : exp) : (x ^ q1) ^q2 = x ^ (q1 +* q2).
    proof.
      admit.
    
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


      (* Random Oracle *)
module type RO = {
  proc * init() : unit

  proc f(x : group) : text
}.

module RO : RO = {
  var mp : (group, text) fmap (* finite map, table *)

     x1 -> t1
     x2 -> t2
     x3 -> t3

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
}

module HEG (RO : RO) ={
  proc key_gen() : exp = {
    var q : exp;
    q <$ dexp;
    return (g ^ q, q);
  }

  proc enc(e : exp, t : text) : group {
    

  }

  proc dec(e : exp, g : group) : text {
  }

}


  




