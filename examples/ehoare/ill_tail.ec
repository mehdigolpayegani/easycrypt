(* Heavy tail with growing increments (paper, Fig. "Heavy tail"): each
   iteration continues with probability (n-1)/(n+2), increments n and adds
   it to the cost c.  We prove that the expected final cost is exactly
   c + [t] n (n+1).  The cost has no uniform bound and its increment per
   iteration grows with n, but the expected number of iterations is finite
   and the expected ascent of the invariant is linear in n: the equality is
   obtained with the ascent rule (while /ascent), with witness 4 (n+1)^2. *)
require import AllCore Int Real Xreal Distr DBool StdOrder.
import RealOrder Biased.

module HT = {
  var n, c : int
  var t : bool
  proc run () : unit = {
    while (t) {
      t <$ dbiased ((n - 1)%r / (n + 2)%r);
      n <- n + 1;
      c <- c + n;
    }
  }
}.

lemma tail :
  ehoare [=] [HT.run : {1 <= HT.n /\ 0 <= HT.c | (HT.c + b2i HT.t * HT.n * (HT.n + 1))%xr}
                   ==> {!HT.t | HT.c%xr}].
proof.
proc.
while /ascent ((4 * (HT.n + 1) * (HT.n + 1))%xr).
+ by move=> &hr /> _ _ ->.
+ auto => &hr /> hn hc ht; rewrite Ep_dbiased /= 1:/#.
  split; 1: smt().
  rewrite Rp_to_real_eq /= /b2i /=.
  have hp : 0%r <= (HT.n{hr} - 1)%r / (HT.n{hr} + 2)%r <= 1%r by smt().
  rewrite !to_pos_pos; 1..5: smt().
  by rewrite !(fromintD, fromintM, fromintN); field; smt().
+ by move=> &hr _; rewrite /is_real.
move=> v; auto => &hr /> hn hc ht hv hE; rewrite Ep_dbiased /= 1:/#.
have <- : (HT.c{hr} + HT.n{hr} * (HT.n{hr} + 1))%r = v by apply of_reald_pinj => //; smt().
have hp : 0%r <= (HT.n{hr} - 1)%r / (HT.n{hr} + 2)%r by smt().
have h1 : 0 <= HT.n{hr} * (HT.n{hr} + 1) by smt().
rewrite /b2i /= !to_pos_pos; 1..8: smt().
have -> : (HT.n{hr} - 1)%r / (HT.n{hr} + 2)%r *
          ((4 * (HT.n{hr} + 2) * (HT.n{hr} + 2))%r + 1%r +
           ((HT.c{hr} + (HT.n{hr} + 1) + (HT.n{hr} + 1) * (HT.n{hr} + 2))%r -
            (HT.c{hr} + HT.n{hr} * (HT.n{hr} + 1))%r)) =
          ((HT.n{hr} - 1) * (4 * HT.n{hr} * HT.n{hr} + 19 * HT.n{hr} + 20))%r / (HT.n{hr} + 2)%r.
+ by rewrite !(fromintD, fromintM, fromintN); field; smt().
rewrite ler_pdivr_mulr 1:/# -!fromintM le_fromint.
have -> : 4 * (HT.n{hr} + 1) * (HT.n{hr} + 1) * (HT.n{hr} + 2) =
          (HT.n{hr} - 1) * (4 * HT.n{hr} * HT.n{hr} + 19 * HT.n{hr} + 20) +
          (HT.n{hr} * HT.n{hr} + 19 * HT.n{hr} + 28) by ring.
smt().
qed.
