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
