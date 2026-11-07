(* Rejection sampling with a log (paper, Sect. 2): each draw is appended
   to a global log until one passes the test, which happens with
   probability p.  The expected growth of the log is exactly 1/p: the
   equality is proved with the ascent rule for while loops, using the
   invariant [!t]/p + size log and the constant witness 2(1-p)/p.
   The output distribution is dr conditioned on test: a value a is
   returned with probability mu1 dr a / p if test a holds, and never
   otherwise; these equalities use the decay rule. *)
require import AllCore List Distr Xreal StdOrder.
import RealOrder.

type r.
op [lossless] dr : r distr.
op test : r -> bool.
op p = mu dr test.
axiom p_gt0 : 0%r < p.

module RS = {
  var log : r list
  proc rsample () : r = {
    var t, x;
    t <- false;
    x <- witness;
    while (!t) {
      x <$ dr;
      log <- x :: log;
      t <- test x;
    }
    return x;
  }
}.

lemma rsample_exact :
  ehoare [=] [RS.rsample : {true | (inv p + (size RS.log)%r)%xr} ==> {true | (size RS.log)%xr}].
proof.
proc.
while /ascent (true, (b2r (!t) / p + (size RS.log)%r)%xr) ((2%r * (1%r - p) / p)%xr).
+ by move=> &hr /= ->.
+ auto => &hr /> ht.
  rewrite (eq_Ep _ _ ((fun r => (inv p)%xr * (! test r)%xr) + (fun r => (1 + size RS.log{hr})%xr))).
  + move=> x _ /=; rewrite Rp_to_real_eq /= !to_pos_pos //;
      smt(invr_ge0 b2r_ge0 p_gt0 size_ge0 divr_ge0).
  rewrite EpD EpC EpZ /=; 1: smt(invr_gt0 p_gt0 of_realdK).
  rewrite Ep_mu mu_not dr_ll /= -/p.
  by rewrite Rp_to_real_eq /= !to_pos_pos; smt(invr_ge0 p_gt0 size_ge0 mu_bounded).
+ by move=> &hr _; rewrite /is_real.
+ move=> v; auto => &hr /> ht hv hE.
  have <- : inv p + (size RS.log{hr})%r = v by apply of_reald_pinj => //; smt(invr_ge0 p_gt0 size_ge0).
  have hp1 : p <= 1%r by smt(mu_bounded).
  have hr0 : 0%r <= 2%r * (1%r - p) / p by apply divr_ge0; smt(p_gt0).
  rewrite (eq_Ep _ _ (fun x => (2%r * (1%r - p) / p + 2%r)%xr * (! test x)%xr)).
  + move=> x _ /=; case: (test x) => _ //=.
    by rewrite Rp_to_real_eq /= !to_pos_pos; smt(invr_ge0 p_gt0 size_ge0).
  rewrite EpZ /=; 1: smt(of_realdK).
  rewrite Ep_mu mu_not dr_ll /= -/p !to_pos_pos; 1..3: smt().
  have -> // : (2%r * (1%r - p) / p + 2%r) * (1%r - p) = 2%r * (1%r - p) / p.
  by field; smt(p_gt0).
by auto.
qed.

(* The output distribution: rejection sampling returns each a passing
   the test with probability mu1 dr a / p, i.e. it samples dr
   conditioned on test.  The invariant is [t /\ x = a] + [!t] mu1 dr a / p;
   the loop is left with probability p at each iteration, so the decay
   rule applies with the constant witness 1 and factor 1 - p. *)
lemma rsample_out_exact (a : r) : test a =>
  ehoare [=] [RS.rsample : {true | (mu1 dr a / p)%xr} ==> {true | (res = a)%xr}].
proof.
move=> ha; proc.
while /decay (true, (b2r (t /\ x = a) + b2r (!t) * (mu1 dr a / p))%xr) (1%xr) (1%r - p).
+ by move=> &hr /= ->.
+ auto => &hr /> ht.
  rewrite (eq_Ep _ _ ((fun r => (r = a)%xr) + (fun r => of_reald (mu1 dr a / p) ** (! test r)%xr))).
  + move=> y _ /=; case: (y = a) => [->> /=|ne /=]; 1: by rewrite ha.
    by rewrite Rp_to_real_eq /= !to_pos_pos //; smt(b2r_ge0 p_gt0 ge0_mu divr_ge0).
  rewrite EpD EpsZ !Ep_mu mu_not dr_ll -/p (mu_eq _ _ (pred1 a)) //= -/(pred1 a).
  rewrite Rp_to_real_eq /= !to_pos_pos; 1,2: smt(ge0_mu p_gt0 divr_ge0 mu_bounded).
  by field; smt(p_gt0).
+ move=> &hr /= ->.
  have hap : mu1 dr a <= p by rewrite /p; apply mu_le => /#.
  by rewrite /= to_pos_pos; smt(ge0_mu p_gt0 divr_ge0 ler_pdivr_mulr).
+ by auto => &hr /> ht; rewrite Ep_mu mu_not dr_ll -/p.
+ smt(p_gt0 mu_bounded).
+ by move=> &hr _; rewrite /is_real.
by auto.
qed.

lemma pr_rsample_out (a : r) &m : test a =>
  Pr[RS.rsample() @ &m : res = a] = mu1 dr a / p.
proof. by move=> ha; byehoare (rsample_out_exact a ha). qed.

(* A value failing the test is never returned. *)
lemma rsample_out_zero (a : r) : !test a =>
  ehoare [=] [RS.rsample : {true | 0%xr} ==> {true | (res = a)%xr}].
proof.
move=> ha; proc.
while /decay (true, (t /\ x = a)%xr) (1%xr) (1%r - p).
+ by move=> &hr /= ->.
+ by auto => &hr /> ht; rewrite Ep_mu (mu_eq _ _ pred0) 1:/# mu0.
+ by move=> &hr /= ->.
+ by auto => &hr /> ht; rewrite Ep_mu mu_not dr_ll -/p.
+ smt(p_gt0 mu_bounded).
+ by move=> &hr _; rewrite /is_real.
by auto.
qed.

lemma pr_rsample_out_zero (a : r) &m : !test a =>
  Pr[RS.rsample() @ &m : res = a] = 0%r.
proof. by move=> ha; byehoare (rsample_out_zero a ha). qed.
