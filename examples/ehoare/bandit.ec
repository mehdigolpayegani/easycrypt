(* A regret lower bound for epsilon-greedy exploration.  Two arms: arm
   [true] is optimal, arm [false] is suboptimal by a gap [gap] (pulling it
   costs [gap] of pseudo-regret).  At each of the T rounds the learner
   explores with probability eps, and then pulls a uniformly random arm, or
   exploits, and then pulls the arm chosen by an arbitrary rule [G.choose]:
   an abstract procedure, which may depend on the whole history but cannot
   write the counters of the bandit.  Whatever this rule, the bad arm is
   pulled with probability at least eps/2 at each round, so the expected
   regret is at least eps * gap * T / 2.

   The loop runs exactly T times: variant rule, with the invariant
   {0 <= t <= T | regret + (T - t) * eps * gap / 2}.  In the body, the
   exploration step contributes gap/2 when it explores (Ep_dbiased,
   Ep_dbool); the exploitation step contributes at least 0, and the call to
   the abstract rule keeps the value of the invariant, whose variables it
   cannot write: rule Adv-Budget with an empty budget, whose termination
   premise is rule Adv-Lossless. *)
require import AllCore Int Real Xreal Distr DBool StdOrder.
import RealOrder Biased.

op eps : real.
op gap : real.
section.
declare axiom eps_bnd : 0%r <= eps <= 1%r.
declare axiom gap_ge0 : 0%r <= gap.

op T : int.
declare axiom T_ge0 : 0 <= T.

module type Greedy = { proc choose () : bool }.

module Bandit (G : Greedy) = {
  var t : int
  var regret : real

  proc run () : real = {
    var explore, arm;
    t <- 0; regret <- 0%r;
    while (t < T) {
      explore <$ dbiased eps;
      if (explore) { arm <$ {0,1}; } else { arm <@ G.choose(); }
      if (!arm) { regret <- regret + gap; }
      t <- t + 1;
    }
    return regret;
  }
}.

lemma regret_lower (G <: Greedy{-Bandit}) :
  islossless G.choose =>
  ehoare [<=] [Bandit(G).run :
    {true | (eps * gap * T%r / 2%r)%xr} ==> {true | res%xr}].
proof.
move=> G_ll; proc.
while ((0 <= Bandit.t <= T),
       (Bandit.regret + (T - Bandit.t)%r * eps * gap / 2%r)%xr)
      (T - Bandit.t).
(* exit: t = T, and the invariant is the regret *)
+ move=> &hr [[h0 hT] hlt].
  have -> : T = Bandit.t{hr} by smt().
  by [].
(* body: t < T is preserved, T - t decreases, and the expected value of the
   invariant does not decrease *)
+ move=> k; wp.
  (* the guard only reads t, which the rest of the body does not write *)
  conseq (_: {true | (Bandit.regret + (T - Bandit.t)%r * eps * gap / 2%r)%xr}
             ==>
             {true | (Bandit.regret + (if !arm then gap else 0%r)
                      + (T - (Bandit.t + 1))%r * eps * gap / 2%r)%xr}).
  + by [].
  + by move=> &hr [[[h0 hT] hlt] hk] arm0; case: arm0 => /=; smt().
  (* after the coin: exploring is worth gap/2 more *)
  seq 1 : ((Bandit.regret + (T - (Bandit.t + 1))%r * eps * gap / 2%r
            + b2r explore * gap / 2%r)%xr).
  (* E[[explore] gap/2] = eps gap/2: the coin pays for one round *)
  + rnd; skip => &hr /=.
    rewrite Ep_dbiased; 1: smt(eps_bnd).
    rewrite /=.
    have -> : Bandit.regret{hr} + (T - Bandit.t{hr})%r * eps * gap / 2%r
            = (Bandit.regret{hr} + (T - (Bandit.t{hr} + 1))%r * eps * gap / 2%r)
              + eps * (gap / 2%r) by rewrite fromintD; ring.
    have ha : 0%r <= gap / 2%r by smt(gap_ge0).
    move: (Bandit.regret{hr} + _) (gap / 2%r) ha => r a ha.
    have [he0 he1] := eps_bnd.
    rewrite (to_pos_pos eps) // (to_pos_pos (1%r - eps)) 1:/#.
    case: (0%r <= r) => hr.
    + have hea : 0%r <= eps * a by apply mulr_ge0.
      by rewrite !to_pos_pos 1..3:/#; smt().
    have h1 : eps * a <= a by smt(ler_pimull).
    by rewrite /(%pos); smt(mulr_ge0).
  if.
  (* exploring: the bad arm has probability 1/2 *)
  + rnd; skip => &hr [_ ->] /=.
    rewrite Ep_dbool /=.
    have -> : Bandit.regret{hr} + gap + (T - (Bandit.t{hr} + 1))%r * eps * gap / 2%r
            = (Bandit.regret{hr} + (T - (Bandit.t{hr} + 1))%r * eps * gap / 2%r)
              + gap by ring.
    move: (Bandit.regret{hr} + _) => r.
    by have := gap_ge0; rewrite /(%pos); smt().
  (* exploiting: whatever arm the rule chooses, the regret does not decrease *)
  conseq (_: {true | (Bandit.regret + (T - (Bandit.t + 1))%r * eps * gap / 2%r)%xr}
             ==>
             {true | (Bandit.regret + (T - (Bandit.t + 1))%r * eps * gap / 2%r)%xr}).
  + by move=> &hr [_ ->].
  + move=> &hr _ arm0 /=.
    by apply le_pos; case: arm0 => _ /=; smt(gap_ge0).
  (* the rule cannot write t and regret: it keeps the value *)
  call (: (true, (Bandit.regret + (T - (Bandit.t + 1))%r * eps * gap / 2%r)%xr)
          ==>
          (true, (Bandit.regret + (T - (Bandit.t + 1))%r * eps * gap / 2%r)%xr)).
  + proc (true, (Bandit.regret + (T - (Bandit.t + 1))%r * eps * gap / 2%r)%xr) 0 0.
    (* termination: the rule is lossless *)
    + proc (true, 1%xr).
      by apply G_ll.
    (* the empty budget is bounded, and the invariant finite *)
    + by move=> &hr.
    by move=> &hr _; rewrite /is_real.
  by skip.
(* the variant is non-negative inside the loop *)
+ by move=> &hr [[_ hT] hlt]; smt().
(* prefix: t = 0 and regret = 0 *)
wp; skip => &hr /=.
split; 1: exact T_ge0.
by apply le_pos; smt().
qed.

end section.
