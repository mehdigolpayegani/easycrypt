(* A doubling loop (paper, Sect. 4.3): starting from x >= 1, each
   iteration doubles x and exits with probability 1/2.  The expected
   final value of x is infinite (the series sum 2^k x / 2^(k+1)
   diverges), so no finite upper bound exists.  Every finite lower bound
   is provable, which is how the logic establishes that the expectation
   is infinite.  The bound 2 is proved with the decay rule for while
   loops, using the invariant [!t] * 2 + [t] * x, the constant witness 2
   and the factor 1/2.  An arbitrary bound N is obtained from the lower
   bound a * x^(1-eps), proved with the decay rule (the paper calls it
   beta-decay) and the witness a * x^(1-eps): one iteration doubles x
   and keeps running with probability 1/2, so the running mass of the
   witness decays by the factor 2^(-eps) < 1. *)
require import AllCore Int Real RealExp Xreal Distr DBool StdOrder.
import RealOrder.

(* exp lies above its tangent at 0, on the whole real line. *)
lemma ge1D_exp (y : real) : 1%r + y <= exp y.
proof. by have := le_ln_up (exp y) (exp_gt0 y); rewrite lnK; smt(). qed.

module D = {
  var x : int
  var t : bool
  proc run () : int = {
    t <- false;
    while (!t) {
      x <- 2 * x;
      t <$ {0,1};
    }
    return x;
  }
}.

lemma doubling_lower :
  ehoare [<=] [D.run : {1 <= D.x | 2%xr} ==> {true | res%xr}].
proof.
proc.
while /decay ((1 <= D.x), (b2r (!D.t) * 2%r + b2r D.t * D.x%r)%xr) (2%xr) (1%r / 2%r).
+ by move=> &hr /= [_ ->].
+ auto => &hr /> hx ht; rewrite Ep_dbool /=.
  by split => [/#|]; rewrite to_pos_pos /#.
+ by move=> &hr /= [_ ->].
+ by auto => &hr /> hx ht; rewrite Ep_dbool /=.
+ smt().
+ by move=> &hr _; rewrite /is_real.
by auto.
qed.

(* Doubling x multiplies x^(1-eps) by 2 * 2^(-eps). *)
lemma rpow_double (eps : real) (x : int) : 1 <= x =>
  (2 * x)%r ^ (1%r - eps) = 2%r * 2%r ^ (-eps) * x%r ^ (1%r - eps).
proof.
move=> hx; rewrite fromintM rpowMr // 1:/#.
have -> : 2%r ^ (1%r - eps) = 2%r ^ 1%r * 2%r ^ (-eps) by rewrite -rpowD.
by rewrite rpow1.
qed.

(* Lower bound a * x^(1-eps): on a running state, one iteration yields
   1/2 * 2x + 1/2 * a (2x)^(1-eps) = x + a 2^(-eps) x^(1-eps), which is
   above a x^(1-eps) since a (1 - 2^(-eps)) <= 1 <= x^eps.  The witness
   a x^(1-eps) keeps running with probability 1/2 and is multiplied by
   2^(1-eps), so its running mass decays by 2^(-eps). *)
lemma doubling_lower_pow (eps a : real) :
  0%r < eps => eps <= 1%r => 0%r <= a => a * (1%r - 2%r ^ (-eps)) <= 1%r =>
  ehoare [<=] [D.run : {1 <= D.x | (a * D.x%r ^ (1%r - eps))%xr} ==> {true | res%xr}].
proof.
move=> he0 he1 ha hb.
have hb0 : 0%r < 2%r ^ (-eps) by apply rpow_gt0.
have hb1 : 2%r ^ (-eps) < 1%r.
+ rewrite rpowN // -(rpow0 2%r); have := rexpr_hmono_ltr 2%r 0%r eps _ _ => //.
  smt(rpow0 rpow_gt0).
proc.
while /decay ((1 <= D.x),
  (b2r (!D.t) * (a * D.x%r ^ (1%r - eps)) + b2r D.t * D.x%r)%xr)
  ((a * D.x%r ^ (1%r - eps))%xr) (2%r ^ (-eps)).
+ by move=> &hr /= [_ ->].
+ auto => &hr /> hx ht; rewrite Ep_dbool /=.
  split => [/#|].
  have hx0 : 1%r <= D.x{hr}%r by smt().
  have hp : 0%r <= D.x{hr}%r ^ (1%r - eps) by apply rpow_ge0; smt().
  have hxe : 1%r <= D.x{hr}%r ^ eps.
  + by rewrite -{1}(rpow0 D.x{hr}%r); apply rexpr_hmono => /#.
  have ex : D.x{hr}%r = D.x{hr}%r ^ (1%r - eps) * D.x{hr}%r ^ eps.
  + by rewrite -rpowD 1:/# (_ : 1%r - eps + eps = 1%r) 1:/# rpow1 /#.
  rewrite rpow_double // !to_pos_pos; 1..3: smt(mulr_ge0).
  have : a * (1%r - 2%r ^ (-eps)) * D.x{hr}%r ^ (1%r - eps)
         <= 1%r * D.x{hr}%r ^ eps * D.x{hr}%r ^ (1%r - eps).
  + by apply ler_wpmul2r => //; smt().
  smt().
+ by move=> &hr /= [_ ->].
+ auto => &hr /> hx ht; rewrite Ep_dbool /=.
  have hp : 0%r <= D.x{hr}%r ^ (1%r - eps) by apply rpow_ge0; smt().
  rewrite rpow_double // !to_pos_pos; 1..3: smt(mulr_ge0).
  smt().
+ smt().
+ by move=> &hr _; rewrite /is_real.
by auto.
qed.

(* Every finite lower bound N >= 1 holds: take eps = 1/N and a = N.
   Since 2^(-1/N) = exp (-(ln 2)/N) >= 1 - (ln 2)/N, we get
   N (1 - 2^(-1/N)) <= ln 2 <= 1, and N <= N x^(1-1/N) for x >= 1. *)
lemma doubling_unbounded (N : real) : 1%r <= N =>
  ehoare [<=] [D.run : {1 <= D.x | N%xr} ==> {true | res%xr}].
proof.
move=> hN; conseq (doubling_lower_pow (inv N) N _ _ _ _).
+ move=> &hr hx /=; have h1 : 1%r <= D.x{hr}%r ^ (1%r - inv N).
  + rewrite -{1}(rpow0 D.x{hr}%r); apply rexpr_hmono; 1: smt().
    smt(invr_le1).
  by rewrite !to_pos_pos; smt().
+ by [].
+ smt(invr_gt0).
+ smt(invr_le1).
+ smt().
have hl2 : ln 2%r <= 1%r by smt(le_ln_up).
have := ge1D_exp ((- inv N) * ln 2%r); rewrite -rpowE // => h.
have : N * (1%r - 2%r ^ - inv N) <= N * (inv N * ln 2%r).
+ by apply ler_wpmul2l; smt().
by rewrite RField.mulrA RField.divff; smt().
qed.
