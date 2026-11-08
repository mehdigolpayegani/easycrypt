(* The Miller-Rabin primality test: k random bases are drawn in
   [2 .. n-2]; the test stops as soon as one of them is a witness of
   compositeness, and declares n prime if none was found.  [witness] is
   the concrete Miller-Rabin witness: with n - 1 = 2^s * d and d odd, the
   base a is a witness iff a^d <> 1 and a^(2^r * d) <> -1 modulo n for
   every 0 <= r < s.  The real test rules out even numbers first, so the
   statements about composites assume n odd (and n >= 9, the smallest odd
   composite).

   Two number-theoretic facts are axioms: a witness exists only for a
   composite n (soundness of the witness), and an odd composite n has at
   most (n-1)/4 strong liars in [1 .. n-1] (the Rabin-Monier bound, a
   theorem of group theory about (Z/nZ)^* ).  Neither mentions
   probabilities; everything about probabilities is proved, starting with
   [witness_density]: at least three quarters of the bases in [2 .. n-2]
   are witnesses.

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

require import AllCore Int IntDiv Real RealExp Xreal Distr DInterval List StdOrder.
import RealOrder.

(* -------------------------------------------------------------------- *)
(* Decomposition m = 2^(val2 m) * odd_part m of a positive integer. *)

lemma two_adic_ex m : 0 < m =>
  exists s d, 0 <= s /\ odd d /\ m = 2 ^ s * d.
proof.
move=> hm; have hm0 : 0 <= m by smt().
move: hm; elim/sintind: m hm0 => m hm0 ih hm.
case: (odd m) => hodd; 1: by exists 0 m; rewrite expr0.
have hm2 : m = 2 * (m %/ 2) by smt(oddPn divzE).
have [s d [hs [hd hsd]]] := ih (m %/ 2) _ _; 1,2: smt().
exists (s + 1) d; split; 1: smt(); split=> //; rewrite Ring.IntID.exprS // hm2 hsd; ring.
qed.

op is_val2 (m s : int) = 0 <= s /\ exists d, odd d /\ m = 2 ^ s * d.

op val2 (m : int) : int = choiceb (is_val2 m) 0.

op odd_part (m : int) : int = m %/ 2 ^ val2 m.

lemma two_adicP m : 0 < m =>
  0 <= val2 m /\ odd (odd_part m) /\ m = 2 ^ val2 m * odd_part m.
proof.
move=> hm; have [s d [hs [hd hsd]]] := two_adic_ex m hm.
have [h0 [d' [hd' hm']]] : is_val2 m (val2 m).
+ by rewrite /val2; apply (choicebP (is_val2 m) 0); exists s; split => //; exists d.
rewrite /odd_part.
have hp : 0 < 2 ^ val2 m by apply IntOrder.expr_gt0.
have -> : m %/ 2 ^ val2 m = d' by rewrite {1}hm' mulzC mulzK 1:/#.
by rewrite -hm'.
qed.

(* -------------------------------------------------------------------- *)
(* Miller-Rabin witnesses. *)

op composite (n : int) = 1 < n /\ !prime n.

(* witness n a: the base a certifies that n is composite.  With
   n - 1 = 2^s * d and d odd, a^d <> 1 and a^(2^r * d) <> -1 modulo n for
   every 0 <= r < s. *)
op witness (n a : int) =
  let s = val2 (n - 1) in
  let d = odd_part (n - 1) in
  a ^ d %% n <> 1 /\ forall r, 0 <= r < s => a ^ (2 ^ r * d) %% n <> n - 1.

(* Soundness of the witness: if n is prime, the squares a^(2^r * d) go up
   to a^(n-1) = 1 (Fermat), and the only square roots of 1 modulo n are 1
   and -1. *)
axiom witness_composite n a : witness n a => composite n.

(* Rabin-Monier: a composite odd n has at most (n-1)/4 strong liars in
   [1 .. n-1]. *)
axiom nonwitness_count n : composite n => odd n => 9 <= n =>
  4 * count (fun a => !witness n a) (range 1 n) <= n - 1.

(* -------------------------------------------------------------------- *)
(* 1 and n-1 are never witnesses. *)

lemma exp_pred_mod n d : 1 < n => 0 <= d =>
  (n - 1) ^ d %% n = if odd d then n - 1 else 1.
proof.
move=> hn; elim: d => [|d hd ih]; 1: by rewrite expr0 odd0 /= modz_small /#.
rewrite exprS // -modzMmr ih oddS.
case: (odd d) => _ /=.
+ have -> : (n - 1) * (n - 1) = (n - 2) * n + 1 by ring.
  by rewrite modzMDl modz_small /#.
by rewrite modz_small /#.
qed.

lemma liar1 n : 1 < n => !witness n 1.
proof. by move=> hn; rewrite /witness /= expr1z modz_small /#. qed.

lemma liar_pred n : odd n => 3 <= n => !witness n (n - 1).
proof.
move=> hodd hn; have [hs [hd he]] := two_adicP (n - 1) _; 1: smt().
rewrite /witness /= negb_and; right; rewrite negb_forall /=; exists 0.
rewrite expr0 /= exp_pred_mod 1:/# 1:/# hd /=.
case: (val2 (n - 1) = 0) => [h0|]; 2: smt().
have he' : n - 1 = odd_part (n - 1) by move: he; rewrite h0 expr0.
by move: hd; rewrite -he'; smt(oddS).
qed.

lemma witness_density n : composite n => odd n => 9 <= n =>
  3%r / 4%r <= mu [2 .. n - 2] (witness n).
proof.
move=> hc hodd hn; have := nonwitness_count n hc hodd hn.
rewrite range_ltn 1:/# /= liar1 1:/# /=.
have -> : n = (n - 1) + 1 by ring.
rewrite rangeSr 1:/# -cats1 count_cat /=.
have -> : n - 1 + 1 - 1 = n - 1 by ring.
rewrite liar_pred // 1:/# /= => hcnt.
rewrite dinterE size_filter.
have -> : n - 2 + 1 = n - 1 by ring.
have := count_predC (witness n) (range 2 (n - 1)).
rewrite size_range => hC.
have hpos : 0%r < (n - 3)%r by smt().
rewrite ler_pdivl_mulr; smt().
qed.

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

lemma mr_composite (n0 k0 : int) : composite n0 => odd n0 => 9 <= n0 => 0 <= k0 =>
  ehoare [<=] [MR.test : {arg = (n0, k0) | (1%r - (1%r/4%r) ^ k0)%xr} ==> {true | (!res)%xr}].
proof.
move=> hc ho hn hk; proc.
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
  have hd := witness_density n0 hc ho hn.
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

lemma pr_mr_composite (n k : int) &m : composite n => odd n => 9 <= n => 0 <= k =>
  1%r - (1%r/4%r) ^ k <= Pr[MR.test(n, k) @ &m : !res].
proof. by move=> hc ho hn hk; byehoare (mr_composite n k hc ho hn hk). qed.

lemma mr_rounds (n0 k0 : int) : composite n0 => odd n0 => 9 <= n0 => 0 <= k0 =>
  ehoare [>=] [MR.test : {arg = (n0, k0) | (4%r / 3%r)%xr} ==> {true | MR.rounds%xr}].
proof.
move=> hc ho hn hk; proc.
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
  have hd := witness_density n0 hc ho hn.
  have hc1 : c <= 4%r / 3%r by smt().
  rewrite hw !to_pos_pos; 1..4: smt(mu_bounded).
  have := ler_pmul c (4%r / 3%r) (1%r - mu [2..n0 - 2] (witness n0)) (1%r / 4%r)
            hc0 _ hc1 _; 1,2: smt(mu_bounded).
  smt().
(* prefix *)
wp; skip => &hr /= [-> _] /=.
by apply le_pos; smt().
qed.

lemma mr_prime (n0 k0 : int) : prime n0 => 4 <= n0 =>
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

lemma pr_mr_prime (n k : int) &m : prime n => 4 <= n =>
  Pr[MR.test(n, k) @ &m : res] = 1%r.
proof. by move=> hp hn; byehoare (mr_prime n k hp hn). qed.
