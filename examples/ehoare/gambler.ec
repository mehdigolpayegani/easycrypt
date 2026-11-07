(* Gambler's ruin: a symmetric random walk on 0..N, absorbed at both ends.
   - gambler_exact: from 0 <= w <= N, the walk reaches N before 0 with
     probability exactly w/N. The value w/N is an exact martingale bounded
     by 1; rule [while /bounded] on an [=] goal, whose termination premise
     is discharged by rule [while /ast] with variant w, progress
     probability 1/2 and decrease 1.
   - pr_gambler: the same result as a probability, by [byehoare]. *)
require import AllCore Int Real Xreal Distr DBool StdOrder.
import RealOrder.

op N : int.
axiom N_ge1 : 1 <= N.

module G = {
  var w : int
  proc run () : bool = {
    var b;
    while (0 < w < N) {
      b <$ {0,1};
      w <- if b then w + 1 else w - 1;
    }
    return w = N;
  }
}.

lemma gambler_exact :
  ehoare [=] [G.run : {0 <= G.w <= N | (G.w%r / N%r)%xr} ==> {true | (res)%xr}].
proof.
proc.
while /bounded 1%r.
+ move=> &hr /> h0 hN hb.
  case: (G.w{hr} = N) => [-> | hne].
  + by rewrite RField.divrr //; smt(N_ge1).
  by have -> /= : G.w{hr} = 0 by smt().
+ auto => &hr /> h0 hN h0' hN'; rewrite Ep_dbool /=.
  split; 1: smt().
  rewrite Rp_to_real_eq /= !to_pos_pos; 1..3: smt(N_ge1 divr_ge0).
  by rewrite !(fromintD, fromintN); field; smt(N_ge1).
+ move=> &hr /> h0 hN; rewrite to_pos_pos; 1: smt(N_ge1 divr_ge0).
  by rewrite ler_pdivr_mulr /=; smt(N_ge1).
while /ast (G.w%r) (fun (_ : real) => 1%r / 2%r) (fun (_ : real) => 1%r).
+ by auto => &hr /> *; rewrite Ep_dbool /=; smt().
+ by move=> &hr /#.
+ by move=> v; auto => &hr /> *; rewrite Ep_dbool /= !to_pos_pos; smt().
+ by move=> v; auto => &hr /> *; rewrite Ep_dbool /=; smt().
by move=> &hr; smt().
qed.

(* as a probability: the gambler reaches N with probability w/N *)
lemma pr_gambler &m : 0 <= G.w{m} <= N =>
  Pr[G.run() @ &m : res] = G.w{m}%r / N%r.
proof. by move=> hw; byehoare gambler_exact. qed.
