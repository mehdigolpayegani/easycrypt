(* Von Neumann's fair coin from a biased one: a coin of bias p is flipped
   twice until the two outcomes differ, and the first one is returned.
   With q = p^2 + (1-p)^2 the probability that the two flips agree, the
   loop is left with probability 1 - q = 2 p (1-p) at each iteration.
   - vn_exact: the expected number of flips is exactly 1/(p(1-p)); the
     invariant c + [a = b]/(p(1-p)) is unbounded (c grows), so the
     equality is proved with the ascent rule (while /ascent) and the
     constant witness 3/(2p(1-p)).
   - vn_fair: the returned bit is fair; the invariant
     [a <> b][a] + [a = b]/2 is bounded by 1, so the equality is proved
     with the decay rule (while /decay), witness 1 and factor q.
   - pr_vn_fair: the probability statement, by byehoare. *)
require import AllCore Int Real Xreal Distr DBool StdOrder.
import RealOrder Biased.

op p : real.
axiom p_bnd : 0%r < p < 1%r.

module VN = {
  var c : int
  proc run () : bool = {
    var a, b;
    a <- true; b <- true;
    while (a = b) {
      a <$ dbiased p;
      b <$ dbiased p;
      c <- c + 2;
    }
    return a;
  }
}.

lemma vn_exact :
  ehoare [=] [VN.run : {0 <= VN.c | (VN.c%r + 1%r / (p * (1%r - p)))%xr} ==> {true | VN.c%xr}].
proof.
have hp : 0%r <= p <= 1%r by smt(p_bnd).
have hpq : 0%r < p * (1%r - p) by smt(p_bnd mulr_gt0).
have hi : 0%r <= inv (p * (1%r - p)) by smt(invr_ge0).
proc.
while /ascent ((0 <= VN.c), (VN.c%r + b2r (a = b) / (p * (1%r - p)))%xr) ((3%r / (2%r * p * (1%r - p)))%xr).
+ by move=> &hr [_ hab]; rewrite hab b2r0.
+ auto => &hr /= [hc ->]; rewrite Ep_dbiased; 1: exact hp.
  split; 1: smt().
  rewrite /= Ep_dbiased; 1: exact hp.
  rewrite Ep_dbiased; 1: exact hp.
  rewrite /= Rp_to_real_eq /= !to_pos_pos; 1..5: smt().
  rewrite fromintD; field.
  have -> : p - p ^ 2 = p * (1%r - p) by ring.
  smt().
+ by move=> &hr _; rewrite /is_real.
+ move=> v; auto => &hr /= [[hc hab] [hv hE]].
  rewrite hab /= in hE.
  have <- : VN.c{hr}%r + inv (p * (1%r - p)) = v by apply of_reald_pinj => //; smt().
  rewrite Ep_dbiased; 1: exact hp.
  rewrite /= Ep_dbiased; 1: exact hp.
  rewrite Ep_dbiased; 1: exact hp.
  have hr : 0%r <= 3%r / (2%r * p * (1%r - p)) by apply divr_ge0 => //; smt(mulr_ge0).
  rewrite /= !to_pos_pos; 1..8: smt().
  have hqr : (p * p + (1%r - p) * (1%r - p)) * (3%r / (2%r * p * (1%r - p))) =
             3%r / (2%r * p * (1%r - p)) - 3%r.
  + field; have -> : 2%r * p + (-2%r) * p ^ 2 = 2%r * (p * (1%r - p)) by ring.
    smt().
  by rewrite fromintD; smt().
by wp; skip => &hr hc; split => //; congr; smt().
qed.

lemma vn_fair :
  ehoare [=] [VN.run : {true | (1%r / 2%r)%xr} ==> {true | res%xr}].
proof.
have hp : 0%r <= p <= 1%r by smt(p_bnd).
proc.
while /decay (true, (b2r (a <> b) * b2r a + b2r (a = b) / 2%r)%xr) (1%xr) (p * p + (1%r - p) * (1%r - p)).
+ by move=> &hr /= ->.
+ auto => &hr /= ->; rewrite Ep_dbiased; 1: exact hp.
  rewrite /= Ep_dbiased; 1: exact hp.
  rewrite Ep_dbiased; 1: exact hp.
  rewrite /= Rp_to_real_eq /= !to_pos_pos; 1,2: smt().
  by field.
+ by move=> &hr /= ->; rewrite /= to_pos_pos; smt().
+ auto => &hr /= _; rewrite Ep_dbiased; 1: exact hp.
  rewrite /= Ep_dbiased; 1: exact hp.
  rewrite Ep_dbiased; 1: exact hp.
  by rewrite /= !to_pos_pos; smt().
+ smt(p_bnd).
+ by move=> &hr _; rewrite /is_real.
by wp; skip => _; congr; smt().
qed.

lemma pr_vn_fair &m : Pr[VN.run() @ &m : res] = 1%r / 2%r.
proof. by byehoare vn_fair. qed.
