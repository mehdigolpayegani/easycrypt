(* A doubling loop (paper, Sect. 4.3): starting from x >= 1, each
   iteration doubles x and exits with probability 1/2.  The expected
   final value of x is infinite (the series sum 2^k x / 2^(k+1)
   diverges), so no finite upper bound exists; the lower bound 2 is
   proved with the decay rule for while loops, using the invariant
   [!t] * 2 + [t] * x, the constant witness 2 and the factor 1/2. *)
require import AllCore Int Real Xreal Distr DBool StdOrder.
import RealOrder.

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
