(* The Miller-Rabin primality test: k random bases are drawn in
   [2 .. n-2]; the test stops as soon as one of them is a witness of
   compositeness, and declares n prime if none was found.  The
   number-theoretic facts are axioms on an abstract predicate [witness]:
   a witness exists only for a composite n, and for a composite n >= 4 at
   least three quarters of the bases are witnesses.

   - mr_composite: on a composite n, the test answers "composite" with
     probability at least 1 - (1/4)^k.  Lower bound [<=]; the loop runs at
     most k times, so the variant rule applies with variant k - i and the
     invariant [comp] + [!comp] (1 - (1/4)^(k - i)).
   - mr_rounds: on a composite n, the expected number of rounds is at most
     4/3.  Upper bound [>=], rule Park with the invariant
     rounds + [!comp /\ i < k] * 4/3.
   - mr_prime: a prime is always declared prime.  Equality [=], variant
     rule with the invariant [!comp], exactly preserved since no base is a
     witness.
   The probability statements follow by [byehoare]. *)

require import AllCore Int Real RealExp Xreal Distr DInterval StdOrder.
import RealOrder.

op composite : int -> bool.
op witness : int -> int -> bool.         (* witness n a: the base a certifies that n is composite *)

axiom witness_composite n a : witness n a => composite n.
axiom witness_density n : composite n => 4 <= n => 3%r / 4%r <= mu [2 .. n - 2] (witness n).

module MR = {
  var rounds : int
  proc test (n k : int) : bool = {
    var i, a, comp;
    i <- 0; comp <- false; rounds <- 0;
    while (i < k /\ !comp) {
      a <$ [2 .. n - 2];
      comp <- witness n a;
      i <- i + 1; rounds <- rounds + 1;
    }
    return !comp;
  }
}.

lemma mr_composite (n0 k0 : int) : composite n0 => 4 <= n0 => 0 <= k0 =>
  ehoare [<=] [MR.test : {arg = (n0, k0) | (1%r - (1%r/4%r) ^ k0)%xr} ==> {true | (!res)%xr}].
proof.
move=> hc hn hk; proc.
while ((n = n0 /\ k = k0 /\ 0 <= i <= k),
       (if comp then 1%r else 1%r - (1%r/4%r) ^ (k - i))%xr) (k - i).
(* exit: either a witness was found, or i = k and (1/4)^0 = 1 *)
+ move=> &hr [[_ [_ [h0 hik]]] hex]; case: (comp{hr}) => hcomp /=; 1: by [].
  have -> : k{hr} - i{hr} = 0 by smt().
  by rewrite RField.expr0.
(* body: with q = (1/4)^(k-i-1), the next value is 1 on a witness and
   1 - q otherwise; its expectation is 1 - q + q p >= 1 - q/4 *)
+ move=> j; wp; skip => &hr /=.
  move=> [[[-> [-> [h0 hik]]] [hlt hnc]] <-].
  split; 1: smt().
  rewrite hnc /=.
  have hq0 : 0%r <= inv 4%r ^ (k0 - (i{hr} + 1)) by apply expr_ge0; smt().
  have hq1 : inv 4%r ^ (k0 - (i{hr} + 1)) <= 1%r by apply exprn_ile1; smt().
  pose q := inv 4%r ^ (k0 - (i{hr} + 1)).
  rewrite (eq_Ep _ _ ((fun a => (1%r - q)%xr) + (fun a => of_reald q ** (witness n0 a)%xr))).
  + move=> x _ /=; case: (witness n0 x) => _ //=.
    by rewrite Rp_to_real_eq /= !to_pos_pos /#.
  rewrite EpD EpC EpsZ Ep_mu /=.
  have hw : weight [2..n0 - 2] = 1%r by apply dinter_ll; smt().
  have hd := witness_density n0 hc hn.
  have -> : k0 - i{hr} = (k0 - (i{hr} + 1)) + 1 by ring.
  rewrite RField.exprS 1:/# -/q hw !to_pos_pos; 1..3: smt().
  have := ler_wpmul2l q hq0 _ _ hd.
  smt().
(* the variant is non-negative inside the loop *)
+ by move=> &hr /#.
(* prefix *)
wp; skip => &hr /=.
by move=> [-> ->].
qed.

lemma pr_mr_composite (n k : int) &m : composite n => 4 <= n => 0 <= k =>
  1%r - (1%r/4%r) ^ k <= Pr[MR.test(n, k) @ &m : !res].
proof. by move=> hc hn hk; byehoare (mr_composite n k hc hn hk). qed.

lemma mr_rounds (n0 k0 : int) : composite n0 => 4 <= n0 => 0 <= k0 =>
  ehoare [>=] [MR.test : {arg = (n0, k0) | (4%r / 3%r)%xr} ==> {true | MR.rounds%xr}].
proof.
move=> hc hn hk; proc.
while ((n = n0 /\ 0 <= MR.rounds),
       (MR.rounds%r + b2r (!comp /\ i < k) * 4%r / 3%r)%xr).
(* exit: no round remains *)
+ move=> &hr [[_ h0] hex].
  have -> : (!comp{hr} /\ i{hr} < k{hr}) = false by smt().
  by [].
(* body: one round, and a further round is pending with probability at
   most 1/4 *)
+ wp; skip => &hr /= [[-> h0] [hlt hnc]].
  split; 1: smt().
  rewrite hnc hlt /=.
  pose c := b2r (i{hr} + 1 < k{hr}) * 4%r / 3%r.
  have hc0 : 0%r <= c by smt().
  rewrite (eq_Ep _ _ ((fun a => (MR.rounds{hr} + 1)%xr) + (fun a => of_reald c ** (!witness n0 a)%xr))).
  + move=> x _ /=; case: (witness n0 x) => _ //=.
    by rewrite Rp_to_real_eq /= !to_pos_pos /#.
  rewrite EpD EpC EpsZ Ep_mu mu_not /=.
  have hw : weight [2..n0 - 2] = 1%r by apply dinter_ll; smt().
  have hd := witness_density n0 hc hn.
  have hc1 : c <= 4%r / 3%r by smt().
  rewrite hw !to_pos_pos; 1..4: smt(mu_bounded).
  have := ler_pmul c (4%r / 3%r) (1%r - mu [2..n0 - 2] (witness n0)) (1%r / 4%r)
            hc0 _ hc1 _; 1,2: smt(mu_bounded).
  smt().
(* prefix *)
wp; skip => &hr /= [-> _] /=.
by apply le_pos; smt().
qed.

lemma mr_prime (n0 k0 : int) : !composite n0 => 4 <= n0 =>
  ehoare [=] [MR.test : {arg = (n0, k0) | 1%xr} ==> {true | res%xr}].
proof.
move=> hp hn; proc.
while ((n = n0), (!comp)%xr) (k - i).
(* exit: the invariant is the post *)
+ by [].
(* body: no base is a witness *)
+ move=> j; wp; skip => &hr /= [[-> [_ ->]] <-] /=.
  split; 1: smt().
  rewrite (eq_Ep _ _ (fun _ => 1%xr)).
  + by move=> x _ /=; have -> : witness n0 x = false by smt(witness_composite).
  by rewrite EpC dinter_ll /#.
(* the variant is non-negative inside the loop *)
+ by move=> &hr /#.
(* prefix *)
by wp; skip => &hr /= [-> _].
qed.

lemma pr_mr_prime (n k : int) &m : !composite n => 4 <= n =>
  Pr[MR.test(n, k) @ &m : res] = 1%r.
proof. by move=> hp hn; byehoare (mr_prime n k hp hn). qed.
