(* Symmetric random walk on the integers, absorbed at 0.
   - rw_ast: from any w >= 0 the walk reaches 0 almost surely, although its
     expected duration is infinite; rule [while /ast] of McIver, Morgan,
     Kaminski and Katoen, with variant w, progress probability 1/2 and
     decrease 1.
   - rw_lower: (1/2)^w is a bounded sub-invariant (a sub-martingale bounded
     by 1), so it is a lower bound on the probability of reaching 0; rule
     [while /bounded], whose termination premise is again [while /ast].
   - pr_rw_terminates: the same result as a probability, by [byehoare]. *)
require import AllCore Int Real RealExp Xreal Distr DBool StdOrder.
import RealOrder RField.

module RW = {
  var w : int
  proc run () : unit = {
    var b;
    while (0 < w) {
      b <$ {0,1};
      w <- if b then w + 1 else w - 1;
    }
  }
}.

lemma rw_ast :
  ehoare [<=] [RW.run : {0 <= RW.w | 1%xr} ==> {RW.w = 0 | 1%xr}].
proof.
proc.
while /ast (RW.w%r) (fun (_ : real) => 1%r / 2%r) (fun (_ : real) => 1%r).
+ by move=> &hr /> /#.
+ by auto => &hr /> *; rewrite Ep_dbool /=; smt().
+ by move=> &hr /#.
+ by move=> v; auto => &hr /> *; rewrite Ep_dbool /= !to_pos_pos; smt().
+ by move=> v; auto => &hr /> *; rewrite Ep_dbool /=; smt().
by move=> &hr; smt().
qed.

lemma rw_lower :
  ehoare [<=] [RW.run : {0 <= RW.w | (inv 2%r ^ RW.w)%xr} ==> {RW.w = 0 | 1%xr}].
proof.
proc.
while /bounded 1%r.
+ move=> &hr /> hw hw0; have -> : RW.w{hr} = 0 by smt().
  by rewrite expr0.
+ auto => &hr /> hw hw0; rewrite Ep_dbool /=; split; 1: smt().
  rewrite !to_pos_pos; 1..3: smt(expr_ge0).
  have h1 : inv 2%r ^ (RW.w{hr} + 1) = inv 2%r * inv 2%r ^ RW.w{hr}.
  + by rewrite exprS /#.
  have h2 : inv 2%r ^ RW.w{hr} = inv 2%r * inv 2%r ^ (RW.w{hr} - 1).
  + by rewrite -exprS 1:/#.
  smt(expr_ge0).
+ move=> &hr /> hw; rewrite to_pos_pos; 1: smt(expr_ge0).
  smt(exprn_ile1).
while /ast (RW.w%r) (fun (_ : real) => 1%r / 2%r) (fun (_ : real) => 1%r).
+ by auto => &hr /> *; rewrite Ep_dbool /=; smt().
+ by move=> &hr /#.
+ by move=> v; auto => &hr /> *; rewrite Ep_dbool /= !to_pos_pos; smt().
+ by move=> v; auto => &hr /> *; rewrite Ep_dbool /=; smt().
by move=> &hr; smt().
qed.

(* as a probability: the walk terminates with probability 1 *)
lemma pr_rw_terminates &m : 0 <= RW.w{m} => 1%r <= Pr[RW.run() @ &m : true].
proof. by move=> hw; byehoare rw_ast. qed.
