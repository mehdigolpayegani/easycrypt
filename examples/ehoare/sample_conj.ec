(* The probability that k independent samples all satisfy a predicate is
   exactly p ^ k, where p = mu d P.  The loop runs exactly k times, so the
   variant rule applies, on an equality judgment, with the invariant
   {i <= k | [ok] * p ^ (k - i)}: the upper half of the body premise is rule
   Park, its lower half the variant rule; no decay witness, no finiteness
   condition. *)

require import AllCore Int Real Xreal Distr StdOrder.
import RealOrder.

type t.
op d : t distr.
op P : t -> bool.
op p : real = mu d P.

module Conj = {
  var ok : bool
  var i  : int

  proc run(k : int) : bool = {
    var x : t;
    ok <- true;
    i  <- 0;
    while (i < k) {
      x  <$ d;
      ok <- ok /\ P x;
      i  <- i + 1;
    }
    return ok;
  }
}.

lemma conj_lower :
  ehoare [=] [Conj.run : {0 <= k | (p ^ k)%xr} ==> {true | res%xr}].
proof.
  proc.
  while ((Conj.i <= k), Conj.ok%xr * (p ^ (k - Conj.i))%xr) (k - Conj.i).
  (* exit: i = k, and the invariant is [ok] *)
  + move=> &hr [hik hstop] /=.
    have -> : k{hr} - Conj.i{hr} = 0 by smt().
    by rewrite RField.expr0 /#.
  (* body: P is preserved, k - i decreases, and the expectation is exact *)
  + move=> z.
    wp.
    skip => &hr /=.
    move=> [[hik hlt] <-].
    split; 1: smt().
    case: (Conj.ok{hr}) => hok /=; last by rewrite EpC.
    (* E[[P x] * p^(k-i-1)] = p^(k-i-1) * p = p^(k-i) *)
    have -> :
        (fun (x0 : t) =>
           ((b2r (P x0))%rp * (p ^ (k{hr} - (Conj.i{hr} + 1)))%rp)%xr)
      = (fun (x0 : t) => (p ^ (k{hr} - (Conj.i{hr} + 1)))%rp ** (P x0)%xr).
    + by apply fun_ext => x0 /=; rewrite mulrpC.
    rewrite EpsZ Ep_mu -/p /=.
    have hn : 0 <= k{hr} - (Conj.i{hr} + 1) by smt().
    have -> : k{hr} - Conj.i{hr} = (k{hr} - (Conj.i{hr} + 1)) + 1 by ring.
    by rewrite RField.exprSr //; smt(RealOrder.expr_ge0 mu_bounded).
  (* the variant is non-negative inside the loop *)
  + by move=> &hr [hik hlt] /=; smt().
  (* prefix *)
  + by wp; skip.
qed.

(* The same result by the decay rule, following the recipe of the paper for
   loops with a variant: the witness is beta^(-V) * F, where F is a
   super-invariant bound on the invariant; here the invariant is a
   probability, so F = 1, and with beta = 1/2 and V = k - i the witness is
   2 ^ (k - i).  Compared to the variant rule, this costs the bound, decay
   and finiteness obligations on the witness. *)
lemma conj_decay :
  ehoare [=] [Conj.run : {0 <= k | (p ^ k)%xr} ==> {true | res%xr}].
proof.
  proc.
  while ((Conj.i <= k), Conj.ok%xr * (p ^ (k - Conj.i))%xr)
        ((2%r ^ (k - Conj.i))%xr) (1%r / 2%r).
  (* exit: i = k, and the invariant is [ok] *)
  + move=> &hr [hik hstop] /=.
    have -> : k{hr} - Conj.i{hr} = 0 by smt().
    by rewrite RField.expr0 /#.
  (* body: P is preserved and the expectation of the invariant is exact *)
  + wp.
    skip => &hr /=.
    move=> [hik hlt].
    split; 1: smt().
    case: (Conj.ok{hr}) => hok /=; last by rewrite EpC.
    have -> :
        (fun (x0 : t) =>
           ((b2r (P x0))%rp * (p ^ (k{hr} - (Conj.i{hr} + 1)))%rp)%xr)
      = (fun (x0 : t) => (p ^ (k{hr} - (Conj.i{hr} + 1)))%rp ** (P x0)%xr).
    + by apply fun_ext => x0 /=; rewrite mulrpC.
    rewrite EpsZ Ep_mu -/p /=.
    have hn : 0 <= k{hr} - (Conj.i{hr} + 1) by smt().
    have -> : k{hr} - Conj.i{hr} = (k{hr} - (Conj.i{hr} + 1)) + 1 by ring.
    by rewrite RField.exprSr //; smt(RealOrder.expr_ge0 mu_bounded).
  (* the witness bounds the invariant: [ok] p^(k-i) <= 2^(k-i) *)
  + move=> &hr [hik hlt] /=.
    smt(RealOrder.expr_ge0 RealOrder.exprn_ege1 RealOrder.exprn_ile1 mu_bounded).
  (* decay: E[[i+1 < k] 2^(k-i-1)] <= 1/2 2^(k-i) *)
  + wp.
    skip => &hr /=.
    move=> [hik hlt].
    rewrite EpC /=.
    have hw := mu_bounded d predT.
    have h2 : 0%r <= 2%r ^ (k{hr} - (Conj.i{hr} + 1)) by apply RealOrder.expr_ge0.
    have -> : k{hr} - Conj.i{hr} = (k{hr} - (Conj.i{hr} + 1)) + 1 by ring.
    rewrite RField.exprSr 1:/#.
    smt().
  (* 0 <= 1/2 < 1 *)
  + by move=> _ /=; smt().
  (* the witness is finite *)
  + by move=> &hr _ /=.
  (* prefix *)
  + by wp; skip.
qed.
