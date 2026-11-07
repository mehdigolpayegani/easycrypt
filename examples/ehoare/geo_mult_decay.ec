(* Geometric termination for a fair coin, via lower-bound While-Mult.*)

require import AllCore Int Real Xreal Distr DBool StdOrder.
import RealOrder.

module GEO = {
  var b : bool
  var c : int

  proc loop() : unit = {
    while (b) {
      b <$ {0,1};
      c <- c + 1;
    }
  }
}.

(* E = c + 2[b]: it is c+2 in an active state and c at exit. *)
op geoE (b : bool) (c : int) : xreal =
  (c%r + 2%r * b2r b)%xr.

(* V = c + 2, with the constant decay factor beta = 3/4: on the outputs of
   the body that stay inside the loop, E[[b] V'] = (c+3)/2 <= 3/4 (c+2)
   as 0 <= c. *)
op geoV (c : int) : xreal = (c%r + 2%r)%xr.

op geo_beta : real = 3%r / 4%r.

lemma geo_lower :
  ehoare [<=] [GEO.loop :
    {0 <= GEO.c | geoE GEO.b GEO.c}
    ==>
    {0 <= GEO.c /\ !GEO.b | GEO.c%xr}].
proof.
  proc.
  while (geoV GEO.c) geo_beta.

  (* Post bridge: at exit b=false, geoE is exactly c. *)
  + move=> &hr [hc hb].
    split.
    by split.
    by rewrite /geoE hb.

  (* G1: the loop body preserves geoE in expectation. *)
  + wp.
    skip => &hr /=.
    move=> [hc hb].
    split.
    + move=> b _; smt().
    + rewrite /geoE hb /=.
      rewrite Ep_dbool /=.
      smt().

  (* G2: on active states, geoE = geoV. *)
  + move=> &hr [hc hb] /=.
    by rewrite /geoE /geoV hb /=.

  (* G3: wp(body, [b] ** geoV) <= (3/4) ** geoV. *)
  + wp.
    skip => &hr /=.
    move=> [hc hb].
    rewrite Ep_dbool /=.
    rewrite /geoV /geo_beta /=.
    smt().

  (* G4: beta = 3/4 belongs to [0,1). *)
  + move=> _.
    rewrite /geo_beta.
    smt().

  (* G5: geoV is a finite xreal on active states. *)
  + by move=> &hr [hc hb] /=.
qed.
