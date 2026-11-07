(* Morris's approximate counter (1978): n events are counted with a
   register x holding about log2 n, i.e. with log log n bits.  At each
   event x is incremented with probability 2^-x, and 2^x - 1 estimates the
   number of events.
   - morris_unbiased: the estimate is unbiased, E[2^x - 1] = n exactly.
     One event takes 2^x to 2^(x+1) with probability 2^-x, so
     E[2^x'] = 2^x + 1, and the invariant 2^x - 1 + (n - i) is an exact
     martingale.
   - morris_second_moment: E[4^x] = 1 + 3n(n+1)/2.  One event gives
     E[4^x'] = 4^x + 3 * 2^x, and the invariant
     4^x + 3 (n - i) 2^x + 3 (n - i)(n - i - 1)/2 is an exact martingale.
   Together, Var[2^x - 1] = E[4^x] - (n + 1)^2 = n(n - 1)/2, Morris's bound.
   The loop runs exactly n times, so both equalities are proved with the
   variant rule (while /variant) and the variant n - i. *)
require import AllCore Int Real Xreal Distr DBool StdOrder.
import RealOrder Biased.

op n : int.
axiom n_ge0 : 0 <= n.

module Morris = {
  var x : int
  proc run () : int = {
    var i, b;
    x <- 0; i <- 0;
    while (i < n) {
      b <$ dbiased (inv (2 ^ x)%r);
      x <- if b then x + 1 else x;
      i <- i + 1;
    }
    return 2 ^ x - 1;
  }
}.

lemma morris_unbiased :
  ehoare [=] [Morris.run : {true | n%xr} ==> {true | res%xr}].
proof.
proc.
while /variant ((0 <= Morris.x /\ i <= n),
                ((2 ^ Morris.x)%r - 1%r + (n - i)%r)%xr) (n - i).
(* exit: i = n, and the invariant is the estimate *)
+ move=> &hr [[hx hi] hstop] /=.
  have -> : n - i{hr} = 0 by smt().
  by congr; smt().
(* body: E[2^x'] = 2^x + 1 *)
+ move=> k; auto => &hr /= [[[hx hi] hlt] <-].
  have hp : 1%r <= (2 ^ Morris.x{hr})%r by smt(expr_gt0).
  rewrite Ep_dbiased; 1: smt(invr_ge0 invr_le1).
  split; 1: smt().
  rewrite /= exprS 1:hx Rp_to_real_eq /=.
  rewrite !to_pos_pos; 1..5: smt(invr_ge0 invr_le1).
  by rewrite fromintM !fromintB fromintD; field; smt().
(* the variant is non-negative inside the loop *)
+ by move=> &hr [[hx hi] hlt] /=; smt().
(* prefix *)
wp; skip => &hr /=.
by rewrite expr0 /=; smt(n_ge0).
qed.

lemma morris_second_moment :
  ehoare [=] [Morris.run : {true | (1%r + 3%r * n%r * (n + 1)%r / 2%r)%xr} ==>
                           {true | ((res + 1) ^ 2)%xr}].
proof.
proc.
while /variant ((0 <= Morris.x /\ i <= n),
                ((2 ^ Morris.x)%r * (2 ^ Morris.x)%r
                 + 3%r * (n - i)%r * (2 ^ Morris.x)%r
                 + 3%r * ((n - i) * (n - i - 1))%r / 2%r)%xr) (n - i).
(* exit: i = n, and the invariant is 4^x *)
+ move=> &hr [[hx hi] hstop] /=.
  have -> : n - i{hr} = 0 by smt().
  by congr; rewrite expr2 fromintM; smt().
(* body: E[4^x'] = 4^x + 3 * 2^x and E[2^x'] = 2^x + 1 *)
+ move=> k; auto => &hr /= [[[hx hi] hlt] <-].
  have hp : 1%r <= (2 ^ Morris.x{hr})%r by smt(expr_gt0).
  rewrite Ep_dbiased; 1: smt(invr_ge0 invr_le1).
  split; 1: smt().
  rewrite /= exprS 1:hx Rp_to_real_eq /=.
  have h1 : 0 <= (n - i{hr}) * (n - i{hr} - 1).
  + by apply IntOrder.mulr_ge0 => /#.
  have h2 : 0 <= (n - (i{hr} + 1)) * (n - (i{hr} + 1) - 1).
  + have [->|?] : n - (i{hr} + 1) = 0 \/ 1 <= n - (i{hr} + 1) by smt().
    + by [].
    by apply IntOrder.mulr_ge0 => /#.
  rewrite !to_pos_pos; 1..5: smt(invr_ge0 invr_le1 mulr_ge0 divr_ge0).
  by rewrite !(fromintM, fromintB, fromintD); field; smt().
(* the variant is non-negative inside the loop *)
+ by move=> &hr [[hx hi] hlt] /=; smt().
(* prefix *)
wp; skip => &hr /=; split; 1: smt(n_ge0).
by rewrite expr0; congr; rewrite fromintM fromintB fromintD; field.
qed.
