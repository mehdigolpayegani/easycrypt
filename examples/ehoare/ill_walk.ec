(* Discounted symmetric random walk (paper, Fig. "Discounted random walk").
   While x > 0, x moves one step up or down with probability 1/2 and y is
   halved.  The expected hitting time of 0 is infinite, yet the expected final
   value of y is exactly y * lam^x, with lam = 2 - sqrt 3: since
   lam + 1/lam = 4, one iteration preserves y * lam^x exactly.
   The proof uses the decay rule for while loops ([while /decay]) with
   witness y, which bounds y * lam^x under the guard (lam^x <= 1) and is
   halved at each iteration (factor 1/2). *)
require import AllCore Int Real RealExp Xreal Distr DBool StdOrder.
import RealOrder RField.

op lam : real = 2%r - sqrt 3%r.

lemma sqrt3_sq : sqrt 3%r * sqrt 3%r = 3%r.
proof. by have := sqsqrt 3%r _; [smt() | rewrite expr2]. qed.

lemma sqrt3_lt2 : sqrt 3%r < 2%r.
proof. have := sqrt3_sq; have := ge0_sqrt 3%r; smt(). qed.

lemma lam_gt0 : 0%r < lam.
proof. smt(sqrt3_lt2). qed.

lemma lam_lt1 : lam < 1%r.
proof. have := sqrt3_sq; have := ge0_sqrt 3%r; rewrite /lam; smt(). qed.

(* lam + 1/lam = 4, multiplied by lam *)
lemma lam_sq : lam * lam + 1%r = 4%r * lam.
proof.
have -> : lam * lam + 1%r = 4%r * lam + (sqrt 3%r * sqrt 3%r - 3%r) by rewrite /lam; ring.
by rewrite sqrt3_sq.
qed.

module W = {
  var x : int
  var y : real
  proc run () : unit = {
    var b;
    while (0 < x) {
      b <$ {0,1};
      x <- if b then x + 1 else x - 1;
      y <- y / 2%r;
    }
  }
}.

lemma walk :
  ehoare [=] [W.run : {0 <= W.x /\ 0%r <= W.y | (W.y * lam ^ W.x)%xr}
                  ==> {W.x = 0 | W.y%xr}].
proof.
proc.
while /decay (W.y%xr) (1%r / 2%r).
+ by move=> &hr /> hx hy hx0; rewrite (_ : W.x{hr} = 0) 1:/# expr0.
+ auto => &hr /> hx hy hx0; rewrite Ep_dbool /=; split; 1: smt().
  rewrite Rp_to_real_eq /=.
  have e2 : lam ^ (W.x{hr} + 1) = lam * lam ^ W.x{hr} by rewrite exprS.
  have e1 : lam ^ W.x{hr} = lam * lam ^ (W.x{hr} - 1) by rewrite -exprS 1:/#.
  have hp : 0%r <= lam ^ (W.x{hr} - 1) by apply expr_ge0; smt(lam_gt0).
  rewrite e2 e1 !to_pos_pos; 1..3: smt(mulr_ge0 divr_ge0 lam_gt0).
  move: (lam ^ (W.x{hr} - 1)) (W.y{hr}) => p y.
  have -> : y * (lam * (lam * p)) / 2%r / 2%r + y * p / 2%r / 2%r
          = y * p * (lam * lam + 1%r) / 4%r by field.
  by rewrite lam_sq; field.
+ move=> &hr /> hx hy hx0.
  have hl : lam ^ W.x{hr} <= 1%r by apply exprn_ile1 => //; smt(lam_gt0 lam_lt1).
  have hl0 : 0%r <= lam ^ W.x{hr} by apply expr_ge0; smt(lam_gt0).
  rewrite !to_pos_pos; 1,2: smt(mulr_ge0).
  by rewrite -{2}(mulr1 W.y{hr}) ler_wpmul2l.
+ auto => &hr /> hx hy hx0; rewrite Ep_dbool /= !to_pos_pos; 1..4: smt().
  by rewrite (_ : 0 < W.x{hr} + 1) 1:/#; case: (0 < W.x{hr} - 1) => _ /=; smt().
+ smt().
by move=> &hr _; rewrite /is_real.
qed.
