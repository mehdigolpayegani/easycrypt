(* Adaptive betting against a fair coin: whatever its strategy, an
   adversary that places at most Q accepted stakes keeps its expected
   wealth (Doob's optional stopping theorem for bounded stopping times). *)
require import AllCore Int Real Xreal Distr DBool StdOrder.
import RealOrder.

op Q : int.
section.
declare axiom Q_ge0 : 0 <= Q.

module type Bet = { proc bet (a : int) : unit }.
module type Adv (B : Bet) = { proc play () : unit }.

module O : Bet = {
  var w, q : int

  proc bet (a : int) : unit = {
    var b;
    if (q < Q /\ 0 <= a <= w) {
      q <- q + 1;
      b <$ {0,1};
      w <- if b then w + a else w - a;
    }
  }
}.

module Main (A : Adv) = {
  proc main (w0 : int) : int = {
    O.w <- w0; O.q <- 0;
    A(O).play();
    return O.w;
  }
}.

lemma bet_budget (j : int) (v : real) :
  ehoare [=] [O.bet :
    {(O.q <= Q /\ 0 <= O.w) /\ O.q = j /\ O.w%xr = v%xr | O.w%xr} ==>
    {(O.q <= Q /\ 0 <= O.w) /\ j <= O.q /\ (j < O.q \/ O.w%xr = v%xr) | O.w%xr}].
proof.
proc; if; last by auto.
wp; skip => &hr /> hq hw hwv hlt ha haw; split; 1: smt().
rewrite Ep_dbool /= Rp_to_real_eq /=.
by rewrite !to_pos_pos; 1..3: smt(); smt().
qed.

lemma main_exact (A <: Adv{-O}) :
  (forall (B <: Bet{-A}), islossless B.bet => islossless A(B).play) =>
  ehoare [=] [Main(A).main : {0 <= arg | arg%xr} ==> {true | res%xr}].
proof.
move=> A_ll.
proc; wp.
call (: (O.q <= Q /\ 0 <= O.w, O.w%xr) ==> (O.q <= Q /\ 0 <= O.w, O.w%xr)).
+ proc (O.q <= Q /\ 0 <= O.w, O.w%xr) O.q Q.
  (* the oracle preserves the invariant, counting in q the calls that may change w *)
  + by move=> j v; exact (bet_budget j v).
  (* the adversary terminates: it is lossless and so is the oracle *)
  + proc (O.q <= Q /\ 0 <= O.w, 1%xr).
    + by move=> B B_ll; apply (A_ll B).
    proc; auto => &hr /> hq hw; split; 1: smt().
    by case: (O.q{hr} < Q /\ 0 <= a{hr} <= O.w{hr}) => //= _; rewrite EpC dbool_ll /=.
  (* the budget is bounded, and the invariant finite *)
  + by move=> &hr /#.
  by move=> &hr _; rewrite /is_real.
by auto => &hr /> _; exact Q_ge0.
qed.

end section.
