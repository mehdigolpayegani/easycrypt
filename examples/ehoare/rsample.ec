(* Rejection sampling with a log (paper, Sect. 2): each draw is appended
   to a global log until one passes the test, which happens with
   probability p.  The expected growth of the log is exactly 1/p: the
   equality is proved with the ascent rule for while loops, using the
   invariant [!t]/p + size log and the constant witness 2(1-p)/p. *)
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
