(* Karger's randomised minimum cut: lower bounds on success probabilities.
   Karger's algorithm contracts a uniformly random edge of a multigraph until
   two vertices remain; the edges between them form a cut.  If a minimum cut
   has survived so far and m vertices remain, the next contracted edge lies in
   it with probability at most 2/m (degree bound), so it survives one more
   contraction with probability at least 1 - 2/m.  The graph is abstracted
   away: one contraction at m vertices is a coin whose bias [q m] (the
   probability that the minimum cut is spared) is only known to be at least
   1 - 2/m.
   - karger_success_c: [<=] judgment for [contract], scaled by a constant c in
     [0, 1]: c + (1 - c) * 2/(n(n-1)) <= E[c + (1 - c) [res]].  Variant rule
     ([while /variant], prefix form) with invariant
     {2 <= m | c + (1 - c) [ok] 2/(m(m-1))}: the coin (Ep_dbiased) gives the
     factor q m >= (m-2)/m, and 2/(m(m-1)) = (m-2)/m * 2/((m-1)(m-2)).
   - karger_success, pr_karger: the instance c = 0 (conseq), the success
     probability 2/(n(n-1)) (byehoare).
   - karger_amplify, pr_karger_amplify: r independent runs find a minimum cut
     with probability at least 1 - (1 - p)^r, p = 2/(n(n-1)).  Variant rule
     with invariant {0 <= i <= r | [found] + [!found] (1 - (1 - p)^(r-i))};
     the body calls [contract] with the [<=] call rule, using
     karger_success_c for c = 1 if a cut is already found, and
     c = 1 - (1 - p)^(r-i-1) otherwise (values named by exlim; the range of
     i, which keeps c in [0, 1], is recovered by a case split whose impossible
     branch is closed by exfalso); the call rule carries the frame of [i] and
     [found]. *)
require import AllCore Int Real RealExp Xreal Distr DBool StdOrder.
import RealOrder Biased.

(* probability that a contraction at m vertices spares the minimum cut *)
op q : int -> real.
axiom q_bnd (m : int) : 3 <= m => 1%r - 2%r / m%r <= q m <= 1%r.

module Karger = {
  proc contract (n : int) : bool = {
    var m, ok, b;
    m <- n; ok <- true;
    while (2 < m) {
      b <$ dbiased (q m);
      ok <- ok /\ b;
      m <- m - 1;
    }
    return ok;
  }

  proc amplify (n r : int) : bool = {
    var i, found, ok;
    i <- 0; found <- false;
    while (i < r) {
      ok <@ contract(n);
      found <- found \/ ok;
      i <- i + 1;
    }
    return found;
  }
}.

(* the success probability of [contract] from m vertices *)
op pk (m : int) = 2%r / (m%r * (m - 1)%r).

lemma karger_success_c (n : int) (c : real) :
  2 <= n => 0%r <= c <= 1%r =>
  ehoare [<=] [Karger.contract :
    {arg = n | (c + (1%r - c) * pk n)%xr} ==>
    {true | (c + (1%r - c) * b2r res)%xr}].
proof.
move=> hn hc; proc.
while /variant ((2 <= m), (c + (1%r - c) * (b2r ok * pk m))%xr) (m - 2).
(* exit: m = 2, and 2/(2 * 1) = 1 *)
+ move=> &hr [h1 h2]; have -> : m{hr} = 2 by smt().
  by rewrite /pk.
(* body: the coin spares the cut with probability q m >= (m-2)/m *)
+ move=> k; wp; skip => &hr /= [[h1 h2] hk].
  split; 1: smt().
  rewrite Ep_dbiased; 1: smt(q_bnd).
  rewrite /=.
  have hq := q_bnd m{hr} _; 1: smt().
  (* 2/(m(m-1)) = (1 - 2/m) * 2/((m-1)(m-2)) *)
  have hpk : pk m{hr} = (1%r - 2%r / m{hr}%r) * pk (m{hr} - 1).
  + rewrite /pk !fromintB /=; field.
    + have : 0%r < m{hr}%r * (m{hr}%r - 1%r) by apply mulr_gt0; smt().
      by rewrite RField.expr2; smt().
    + smt().
    have : 0%r < (m{hr}%r - 1%r) * (m{hr}%r - 2%r) by apply mulr_gt0; smt().
    by rewrite RField.expr2; smt().
  have hp : 0%r <= pk (m{hr} - 1).
  + by rewrite /pk; apply divr_ge0 => //; apply mulr_ge0; smt().
  have ha : 0%r <= 1%r - 2%r / m{hr}%r.
  + by rewrite subr_ge0 ler_pdivr_mulr; smt().
  rewrite hpk; move: (pk (m{hr} - 1)) (q m{hr}) (1%r - 2%r / m{hr}%r) hp hq ha.
  move=> p qm a hp hq ha.
  case: (ok{hr}) => _ /=; last by rewrite !to_pos_pos; smt(mulr_ge0).
  have hx : 0%r <= (1%r - c) * p by apply mulr_ge0; smt().
  have -> : (1%r - c) * (a * p) = a * ((1%r - c) * p) by ring.
  move: ((1%r - c) * p) hx => x hx.
  by rewrite !to_pos_pos; smt(mulr_ge0).
(* the variant is non-negative inside the loop *)
+ smt().
(* prefix: m = n and ok = true *)
by wp; skip => &hr /= ->.
qed.

lemma karger_success (n : int) : 2 <= n =>
  ehoare [<=] [Karger.contract :
    {arg = n | (2%r / (n%r * (n - 1)%r))%xr} ==> {true | res%xr}].
proof.
move=> hn; conseq (karger_success_c n 0%r hn _).
+ by move=> &hr ->; rewrite /pk.
+ by move=> &hr _ result /=; case: result.
by [].
qed.

lemma pr_karger (n : int) &m :
  2 <= n => 2%r / (n%r * (n - 1)%r) <= Pr[Karger.contract(n) @ &m : res].
proof. by move=> hn; byehoare (karger_success n hn). qed.

lemma karger_amplify (n r : int) : 2 <= n => 0 <= r =>
  ehoare [<=] [Karger.amplify :
    {arg = (n, r) | (1%r - (1%r - 2%r / (n%r * (n - 1)%r)) ^ r)%xr} ==>
    {true | res%xr}].
proof.
move=> hn hr; move: n r hn hr => n0 r0 hn hr.
have hp : 0%r <= pk n0 <= 1%r.
+ have h2 : 2%r <= n0%r * (n0 - 1)%r.
  + by have := ler_pmul 2%r n0%r 1%r (n0 - 1)%r; smt().
  rewrite /pk; split; 1: by apply divr_ge0 => //; smt().
  by rewrite ler_pdivr_mulr; smt().
proc.
while /variant ((0 <= i <= r /\ n = n0 /\ r = r0),
                (if found then 1%r else 1%r - (1%r - pk n0) ^ (r0 - i))%xr) (r - i).
(* exit: i = r, and (1 - p)^0 = 1 *)
+ move=> &hr [[[_ hi] [_ <-]] hni]; have -> : r{hr} - i{hr} = 0 by smt().
  by rewrite RField.expr0; case: (found{hr}).
(* body: one more run of [contract]; c = 1 when a cut is already found *)
+ move=> k; wp; exlim found, i => f0 i0.
  (* the loop runs only while i < r, so the exponent is non-negative *)
  have hcase : 0 <= i0 < r0 \/ !(0 <= i0 < r0) by smt().
  elim hcase => hi0r; last by exfalso => &hr /#.
  have hx : 0%r <= (1%r - pk n0) ^ (r0 - (i0 + 1)) <= 1%r.
  + by split; [apply expr_ge0 | move=> _; apply exprn_ile1]; smt().
  call (karger_success_c n0
          (if f0 then 1%r else 1%r - (1%r - pk n0) ^ (r0 - (i0 + 1))) hn _).
  + by case: f0 => /=; smt().
  skip => &hr [[<- <-] [[[[hi0 _] [-> ->]] hlt] hk]] /=.
  (* 1 - (1 - p)^(e+1) = c + (1 - c) p with c = 1 - (1 - p)^e *)
  have -> : r0 - i0 = r0 - (i0 + 1) + 1 by ring.
  rewrite RField.exprS 1:/#.
  move: ((1%r - pk n0) ^ (r0 - (i0 + 1))) hx => x hx.
  case: f0 => /= _; 1: smt().
  split.
  + move=> b; split; 1: smt().
    case: b => //=.
    by have -> : 1%r - x + (1%r - (1%r - x)) = 1%r by ring.
  have -> : 1%r - x + (1%r - (1%r - x)) * pk n0 = 1%r - (1%r - pk n0) * x by ring.
  by [].
(* the variant is non-negative inside the loop *)
+ smt().
(* prefix: i = 0 and found = false *)
by wp; skip => &hr /= [-> ->]; rewrite /pk.
qed.

lemma pr_karger_amplify (n r : int) &m : 2 <= n => 0 <= r =>
  1%r - (1%r - 2%r / (n%r * (n - 1)%r)) ^ r
  <= Pr[Karger.amplify(n, r) @ &m : res].
proof. by move=> hn hr; byehoare (karger_amplify n r hn hr). qed.
