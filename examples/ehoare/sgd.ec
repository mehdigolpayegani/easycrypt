(* The noise floor of stochastic gradient descent with random stopping.
   SGD minimises f(x) = x^2/2 (minimiser 0) with learning rate lr and
   Rademacher gradient noise +-sigma: x <- (1 - lr) x - lr xi.  After each
   step the run stops with probability 1 - gamma (a geometric stopping time,
   1/(1 - gamma) steps on average).  With rho = (1 - lr)^2:
   - sgd_error: the expected squared error at the stopping time is exactly
     A x0^2 + B, with A = (1 - gamma) rho / (1 - gamma rho) and
     B = lr^2 sigma^2 / (1 - gamma rho);
   - sgd_noise_floor: it is at least B, whatever the initial point: with a
     constant learning rate SGD does not get below the noise floor B (which
     tends to lr sigma^2 / (2 - lr) when gamma tends to 1).
   The invariant [alive] (A x^2 + B) + [!alive] x^2 is an exact martingale,
   unbounded in x, so the loop is handled by the summability rule
   (while /sum) with witness K (A x^2 + B): one iteration continues with
   probability gamma, and K bounds the sum over the remaining iterations. *)
require import AllCore Int Real Xreal Distr DBool StdOrder.
import RealOrder Biased.

op lr, sigma, gamma : real.
section.
declare axiom lr_bnd : 0%r < lr < 1%r.
declare axiom sigma_gt0 : 0%r < sigma.
declare axiom gamma_bnd : 0%r <= gamma < 1%r.

op rho = (1%r - lr) * (1%r - lr).
op A = (1%r - gamma) * rho / (1%r - gamma * rho).
op B = lr * lr * sigma * sigma / (1%r - gamma * rho).
op K = gamma * (1%r + rho - gamma * rho) / ((1%r - gamma) * (1%r - gamma * rho)).

lemma rho_bnd : 0%r < rho < 1%r.
proof. rewrite /rho; smt(lr_bnd mulr_gt0). qed.

lemma grho_lt1 : 0%r < 1%r - gamma * rho.
proof. smt(rho_bnd gamma_bnd). qed.

lemma A_ge0 : 0%r <= A.
proof. rewrite /A; smt(divr_ge0 mulr_ge0 rho_bnd gamma_bnd grho_lt1). qed.

lemma B_ge0 : 0%r <= B.
proof. rewrite /B; smt(divr_ge0 mulr_ge0 grho_lt1). qed.

lemma K_ge0 : 0%r <= K.
proof. rewrite /K; smt(divr_ge0 mulr_ge0 rho_bnd gamma_bnd grho_lt1). qed.

lemma K_eq : K * (1%r - gamma * rho) * (1%r - gamma) = gamma * (1%r + rho - gamma * rho).
proof.
rewrite /K; have h := grho_lt1; have hg := gamma_bnd; field.
have -> : 1%r + (-rho) * gamma + rho * gamma ^ 2 - gamma = (1%r - gamma) * (1%r - gamma * rho) by ring.
smt(mulf_neq0).
qed.

(* A x^2 + B is a martingale: the coefficient of x^2 and the constant *)
lemma mart_x : (1%r - gamma) * rho + gamma * (A * rho) = A.
proof. by rewrite /A; have h := grho_lt1; field; smt(). qed.

lemma mart_c :
  (1%r - gamma) * (lr * lr * sigma * sigma)
  + gamma * (A * (lr * lr * sigma * sigma) + B) = B.
proof. by rewrite /A /B; have h := grho_lt1; field; smt(). qed.

(* K (A x^2 + B) bounds the sum of the expected values of A x^2 + B over
   the iterations: the coefficient of x^2 and the constant *)
lemma sum_x : gamma * (K + 1%r) * (A * rho) <= K * A.
proof.
have h : gamma * rho <= K * (1%r - gamma * rho).
+ have hg := gamma_bnd; have hr := rho_bnd.
  rewrite -(ler_pmul2r (1%r - gamma)) 1:/# K_eq.
  have -> : gamma * (1%r + rho - gamma * rho) = gamma * rho * (1%r - gamma) + gamma by ring.
  smt().
have -> : gamma * (K + 1%r) * (A * rho) = A * (gamma * rho * (K + 1%r)) by ring.
rewrite (RField.mulrC K); apply ler_wpmul2l; 1: exact A_ge0.
smt().
qed.

lemma sum_c :
  gamma * (K + 1%r) * (A * (lr * lr * sigma * sigma) + B) = K * B.
proof.
rewrite /K /A /B; have h := grho_lt1; have hg := gamma_bnd; field.
+ have -> : 1%r + (-rho) * gamma + rho * gamma ^ 2 - gamma = (1%r - gamma) * (1%r - gamma * rho) by ring.
  smt(mulf_neq0).
smt().
qed.

(* One step of the update, averaged over the noise *)
lemma step x :
  ((1%r - lr) * x - lr * sigma) * ((1%r - lr) * x - lr * sigma) / 2%r
  + ((1%r - lr) * x - lr * -sigma) * ((1%r - lr) * x - lr * -sigma) / 2%r
  = rho * (x * x) + lr * lr * sigma * sigma.
proof. by rewrite /rho; field. qed.

(* One iteration from a running state, averaged over the noise and the stop *)
lemma mart_step x :
  (gamma * (A * ((1%r - lr) * x - lr * sigma) * ((1%r - lr) * x - lr * sigma) + B)
   + (1%r - gamma) * (((1%r - lr) * x - lr * sigma) * ((1%r - lr) * x - lr * sigma))) / 2%r
  + (gamma * (A * ((1%r - lr) * x - lr * -sigma) * ((1%r - lr) * x - lr * -sigma) + B)
   + (1%r - gamma) * (((1%r - lr) * x - lr * -sigma) * ((1%r - lr) * x - lr * -sigma))) / 2%r
  = A * x * x + B.
proof.
have -> : (gamma * (A * ((1%r - lr) * x - lr * sigma) * ((1%r - lr) * x - lr * sigma) + B)
   + (1%r - gamma) * (((1%r - lr) * x - lr * sigma) * ((1%r - lr) * x - lr * sigma))) / 2%r
  + (gamma * (A * ((1%r - lr) * x - lr * -sigma) * ((1%r - lr) * x - lr * -sigma) + B)
   + (1%r - gamma) * (((1%r - lr) * x - lr * -sigma) * ((1%r - lr) * x - lr * -sigma))) / 2%r
  = (gamma * A + (1%r - gamma)) * (((1%r - lr) * x - lr * sigma) * ((1%r - lr) * x - lr * sigma) / 2%r
     + ((1%r - lr) * x - lr * -sigma) * ((1%r - lr) * x - lr * -sigma) / 2%r) + gamma * B by field.
rewrite step.
have h : A * x * x + B - ((gamma * A + (1%r - gamma)) * (rho * (x * x) + lr * lr * sigma * sigma) + gamma * B)
       = (A - ((1%r - gamma) * rho + gamma * (A * rho))) * (x * x)
         + (B - ((1%r - gamma) * (lr * lr * sigma * sigma) + gamma * (A * (lr * lr * sigma * sigma) + B))) by ring.
by rewrite mart_x mart_c /= in h; smt().
qed.

lemma sq_ge0 (y : real) : 0%r <= y * y.
proof. by rewrite -RField.expr2 ge0_sqr. qed.

lemma quad_ge0 (y : real) : 0%r <= A * y * y + B.
proof. by have := mulr_ge0 A (y * y) A_ge0 (sq_ge0 y); smt(B_ge0). qed.

(* One iteration of the summability premise, averaged over the noise *)
lemma sum_step x :
  gamma * (K * (A * ((1%r - lr) * x - lr * sigma) * ((1%r - lr) * x - lr * sigma) + B)
           + (A * ((1%r - lr) * x - lr * sigma) * ((1%r - lr) * x - lr * sigma) + B)) / 2%r
  + gamma * (K * (A * ((1%r - lr) * x - lr * -sigma) * ((1%r - lr) * x - lr * -sigma) + B)
             + (A * ((1%r - lr) * x - lr * -sigma) * ((1%r - lr) * x - lr * -sigma) + B)) / 2%r
  <= K * (A * x * x + B).
proof.
have -> : gamma * (K * (A * ((1%r - lr) * x - lr * sigma) * ((1%r - lr) * x - lr * sigma) + B)
           + (A * ((1%r - lr) * x - lr * sigma) * ((1%r - lr) * x - lr * sigma) + B)) / 2%r
  + gamma * (K * (A * ((1%r - lr) * x - lr * -sigma) * ((1%r - lr) * x - lr * -sigma) + B)
             + (A * ((1%r - lr) * x - lr * -sigma) * ((1%r - lr) * x - lr * -sigma) + B)) / 2%r
  = gamma * (K + 1%r) * (A * (((1%r - lr) * x - lr * sigma) * ((1%r - lr) * x - lr * sigma) / 2%r
     + ((1%r - lr) * x - lr * -sigma) * ((1%r - lr) * x - lr * -sigma) / 2%r) + B) by field.
rewrite step.
have -> : gamma * (K + 1%r) * (A * (rho * (x * x) + lr * lr * sigma * sigma) + B)
        = gamma * (K + 1%r) * (A * rho) * (x * x)
          + gamma * (K + 1%r) * (A * (lr * lr * sigma * sigma) + B) by ring.
rewrite sum_c.
have -> : K * (A * x * x + B) = K * A * (x * x) + K * B by ring.
by rewrite ler_add2r ler_wpmul2r 1:sq_ge0 sum_x.
qed.

module SGD = {
  var x : real
  var alive : bool
  proc run () : real = {
    var b;
    alive <- true;
    while (alive) {
      b <$ {0,1};
      x <- (1%r - lr) * x - lr * (if b then sigma else -sigma);
      alive <$ dbiased gamma;
    }
    return x * x;
  }
}.

lemma sgd_error :
  ehoare [=] [SGD.run : {true | (A * SGD.x * SGD.x + B)%xr} ==> {true | res%xr}].
proof.
have hg : 0%r <= gamma <= 1%r by smt(gamma_bnd).
proc.
while /sum (true, (if SGD.alive then A * SGD.x * SGD.x + B else SGD.x * SGD.x)%xr)
           ((K * (A * SGD.x * SGD.x + B))%xr).
+ by move=> &hr ->.
+ auto => &hr /> ha; rewrite Ep_dbool /= Ep_dbiased; 1: exact hg.
  rewrite Ep_dbiased; 1: exact hg.
  rewrite /= Rp_to_real_eq /= !to_pos_pos;
    1..7: ((try apply quad_ge0); (try apply sq_ge0); smt(gamma_bnd)).
  by rewrite mart_step.
+ by move=> &hr _; rewrite /is_real.
+ auto => &hr /> ha; rewrite Ep_dbool /= Ep_dbiased; 1: exact hg.
  rewrite Ep_dbiased; 1: exact hg.
  rewrite /= !to_pos_pos;
    1..6: ((try apply quad_ge0); (try (apply mulr_ge0; [exact K_ge0 | apply quad_ge0])); smt(gamma_bnd)).
  by apply sum_step.
by auto.
qed.

lemma sgd_noise_floor :
  ehoare [<=] [SGD.run : {true | B%xr} ==> {true | res%xr}].
proof.
conseq sgd_error.
+ move=> &hr; apply xle_rle; split; 1: exact B_ge0.
  by have := mulr_ge0 A (SGD.x{hr} * SGD.x{hr}) A_ge0 (sq_ge0 SGD.x{hr}); smt().
by [].
qed.

end section.
