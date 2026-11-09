(* Policy evaluation in Markov decision processes.
   - Part A, discounted value: a two-state chain under a fixed policy
     (state 1 has reward 1, state 0 reward 0; from 0 the next state is 1
     with probability a, from 1 it stays 1 with probability c).  The
     discount gamma is realised as a geometric horizon: after each step
     the episode goes on with probability gamma.  mdp_value: the expected
     total reward of an episode started in s is exactly the value V s,
     the solution of the Bellman equations (bellman0, bellman1).  The
     total reward is unbounded, so the equality is proved with the ascent
     rule (while /ascent), invariant total + [alive] V s and constant
     witness gamma (2 + V0 + V1) / (1 - gamma) (expected number of
     remaining steps times a bound on the increase per step).
   - Part B, a risky policy near a cliff: a biased walk on 0..N, a step
     right with probability p, left with 1 - p, absorbed at 0 (the cliff,
     reward 0) and at N (the goal, reward 1).  cliff_value: the value of
     w, the probability of reaching the goal, is exactly
     (rho^w - 1) / (rho^N - 1) with rho = (1 - p) / p, since rho^w is a
     martingale.  The value is bounded by 1, so the equality is proved with
     the bounded rule (while /bounded); its termination premise uses the
     almost-sure termination rule (while /ast) with variant w if the walk
     drifts towards the cliff (p <= 1/2), N - w otherwise.
     pr_cliff: the same result as a probability, by byehoare. *)
require import AllCore Int Real Xreal Distr DBool StdOrder.
import RealOrder Biased.

(* ------------------------------------------------------------------ *)
(* Part A: discounted value of a two-state chain *)

op a, c, gamma : real.
section.
declare axiom a_bnd : 0%r <= a <= 1%r.
declare axiom c_bnd : 0%r <= c <= 1%r.
declare axiom gamma_bnd : 0%r <= gamma < 1%r.

(* closed-form solution of the Bellman equations; D > 0 since gamma < 1 *)
op D : real = (1%r - gamma) * (1%r - gamma * c + gamma * a).
op V0 : real = gamma * a / D.
op V1 : real = (1%r - gamma + gamma * a) / D.
op V (s : bool) = if s then V1 else V0.

lemma D_gt0 : 0%r < D.
proof. rewrite /D; apply mulr_gt0; smt(gamma_bnd a_bnd c_bnd). qed.

lemma bellman0 : V0 = gamma * (a * V1 + (1%r - a) * V0).
proof. rewrite /V0 /V1; field; smt(D_gt0). qed.

lemma bellman1 : V1 = 1%r + gamma * (c * V1 + (1%r - c) * V0).
proof. by rewrite /V0 /V1; field; [smt(D_gt0) | rewrite /D; ring]. qed.

lemma V_ge0 s : 0%r <= V s.
proof. rewrite /V /V0 /V1; case: s => _; apply divr_ge0; smt(D_gt0 gamma_bnd a_bnd). qed.

(* one step of the witness: the episode goes on with probability gamma and
   the value increases by at most 1 + V0 + V1 *)
lemma witness_step (q m1 m0 : real) :
  0%r <= q <= 1%r => 0%r <= m1 <= 1%r + V0 + V1 => 0%r <= m0 <= 1%r + V0 + V1 =>
  q * (gamma * (gamma * (2%r + V0 + V1) / (1%r - gamma) + 1%r + m1)) +
  (1%r - q) * (gamma * (gamma * (2%r + V0 + V1) / (1%r - gamma) + 1%r + m0)) <=
  gamma * (2%r + V0 + V1) / (1%r - gamma).
proof.
move=> hq hm1 hm0.
have hg := gamma_bnd.
have hr : gamma * (gamma * (2%r + V0 + V1) / (1%r - gamma) + 1%r + (1%r + V0 + V1)) =
          gamma * (2%r + V0 + V1) / (1%r - gamma) by field; smt().
rewrite -{3}hr.
pose r := gamma * (2%r + V0 + V1) / (1%r - gamma).
pose K := 1%r + V0 + V1.
have h1 : q * (gamma * (r + 1%r + m1)) <= q * (gamma * (r + 1%r + K)).
+ by apply ler_wpmul2l; 1: smt(); apply ler_wpmul2l; smt().
have h0 : (1%r - q) * (gamma * (r + 1%r + m0)) <= (1%r - q) * (gamma * (r + 1%r + K)).
+ by apply ler_wpmul2l; 1: smt(); apply ler_wpmul2l; smt().
have -> : gamma * (r + 1%r + K) = q * (gamma * (r + 1%r + K)) + (1%r - q) * (gamma * (r + 1%r + K)) by ring.
by apply ler_add.
qed.

module MDP = {
  var s, alive : bool
  var total : int
  proc run () : int = {
    total <- 0; alive <- true;
    while (alive) {
      total <- total + b2i s;
      s <$ dbiased (if s then c else a);
      alive <$ dbiased gamma;
    }
    return total;
  }
}.

lemma mdp_value :
  ehoare [=] [MDP.run : {true | (V MDP.s)%xr} ==> {true | res%xr}].
proof.
have hg : 0%r <= gamma <= 1%r by smt(gamma_bnd).
have ha : 0%r <= a <= 1%r by smt(a_bnd).
have hc : 0%r <= c <= 1%r by smt(c_bnd).
have hr0 : 0%r <= gamma * (2%r + V0 + V1) / (1%r - gamma).
+ by apply divr_ge0; smt(V_ge0 gamma_bnd).
proc.
while /ascent ((0 <= MDP.total), (MDP.total%r + b2r MDP.alive * V MDP.s)%xr)
              ((gamma * (2%r + V0 + V1) / (1%r - gamma))%xr).
+ by move=> &hr [_ ->].
+ auto => &hr [ht ->]; case: (MDP.s{hr}) => hs /=; split; 1,3: smt().
  + rewrite Ep_dbiased; 1: exact hc.
    rewrite /= Ep_dbiased; 1: exact hg.
    rewrite Ep_dbiased; 1: exact hg.
    rewrite /= Rp_to_real_eq /= !to_pos_pos; 1..8: smt(V_ge0).
    by rewrite /V /b2i /= fromintD {1}bellman1; ring.
  rewrite Ep_dbiased; 1: exact ha.
  rewrite /= Ep_dbiased; 1: exact hg.
  rewrite Ep_dbiased; 1: exact hg.
  rewrite /= Rp_to_real_eq /= !to_pos_pos; 1..8: smt(V_ge0).
  by rewrite /V /b2i /= {1}bellman0; ring.
+ by move=> &hr _; rewrite /is_real.
+ move=> v; auto => &hr /> ht hal hv hE.
  have <- : MDP.total{hr}%r + V MDP.s{hr} = v by apply of_reald_pinj => //; smt(V_ge0).
  case: (MDP.s{hr}) => hs.
  + rewrite Ep_dbiased; 1: exact hc.
    rewrite /= Ep_dbiased; 1: exact hg.
    rewrite Ep_dbiased; 1: exact hg.
    rewrite /V /b2i /= !(to_pos_pos gamma) 1:/# (to_pos_pos c) 1:/# (to_pos_pos (1%r - c)) 1:/#
      (to_pos_pos (gamma * (2%r + V0 + V1) / (1%r - gamma))) 1://.
    by apply witness_step => //; smt(V_ge0).
  rewrite Ep_dbiased; 1: exact ha.
  rewrite /= Ep_dbiased; 1: exact hg.
  rewrite Ep_dbiased; 1: exact hg.
  rewrite /V /b2i /= !(to_pos_pos gamma) 1:/# (to_pos_pos a) 1:/# (to_pos_pos (1%r - a)) 1:/#
    (to_pos_pos (gamma * (2%r + V0 + V1) / (1%r - gamma))) 1://.
  have := witness_step a ((MDP.total{hr}%r + V1)%pos - (MDP.total{hr}%r + V0)%pos)%pos 0%r ha _ _;
    1,2: smt(V_ge0).
  by rewrite RField.addr0.
by auto.
qed.

(* ------------------------------------------------------------------ *)
(* Part B: reaching the goal before falling off the cliff *)

end section.

section.
op p : real.
declare axiom p_bnd : 0%r < p < 1%r.
declare axiom p_neq : p <> 1%r / 2%r.
op N : int.
declare axiom N_ge1 : 1 <= N.
op rho = (1%r - p) / p.

lemma rho_gt0 : 0%r < rho.
proof. by rewrite /rho; apply divr_gt0; smt(p_bnd). qed.

lemma rho_neq1 : rho <> 1%r.
proof. rewrite /rho; smt(p_bnd p_neq). qed.

lemma rho_exp_bnd w : 0 <= w <= N =>
  if 1%r < rho then 1%r <= rho ^ w <= rho ^ N /\ 1%r < rho ^ N
  else rho ^ N <= rho ^ w <= 1%r /\ rho ^ N < 1%r.
proof.
move=> hw; case: (1%r < rho) => hr.
+ have h1 := ler_weexpn2l rho _ 0 w _; 1,2: smt().
  have h2 := ler_weexpn2l rho _ w N _; 1,2: smt().
  have h3 := ler_weexpn2l rho _ 1 N _; 1,2: smt(N_ge1).
  by move: h1 h3; rewrite RField.expr0 RField.expr1 => h1 h3; smt().
have h1 := ler_wiexpn2l rho _ w 0 _; 1,2: smt(rho_gt0).
have h2 := ler_wiexpn2l rho _ N w _; 1,2: smt(rho_gt0).
have h3 := ler_wiexpn2l rho _ N 1 _; 1,2: smt(rho_gt0 N_ge1).
by move: h1 h3; rewrite RField.expr0 RField.expr1 => h1 h3; smt(rho_neq1).
qed.

lemma rhoN_neq1 : rho ^ N - 1%r <> 0%r.
proof. by have := rho_exp_bnd N _; smt(N_ge1). qed.

(* the value lies in [0, 1] *)
lemma value_bnd w : 0 <= w <= N =>
  0%r <= (rho ^ w - 1%r) / (rho ^ N - 1%r) <= 1%r.
proof.
move=> /rho_exp_bnd; case: (1%r < rho) => _ hb.
+ split; 1: by apply divr_ge0; smt().
  by rewrite ler_pdivr_mulr; smt().
have -> : (rho ^ w - 1%r) / (rho ^ N - 1%r) = (1%r - rho ^ w) / (1%r - rho ^ N).
+ by field; smt().
split; 1: by apply divr_ge0; smt().
by rewrite ler_pdivr_mulr; smt().
qed.

module Cliff = {
  var w : int
  proc run () : bool = {
    var b;
    while (0 < w < N) {
      b <$ dbiased p;
      w <- if b then w + 1 else w - 1;
    }
    return w = N;
  }
}.

lemma cliff_value :
  ehoare [=] [Cliff.run : {0 <= Cliff.w <= N | ((rho ^ Cliff.w - 1%r) / (rho ^ N - 1%r))%xr} ==> {true | res%xr}].
proof.
have hp : 0%r <= p <= 1%r by smt(p_bnd).
proc.
while /bounded 1%r.
+ move=> &hr /> h0 hN hb.
  case: (Cliff.w{hr} = N) => [-> | hne].
  + by rewrite RField.divrr //; exact rhoN_neq1.
  have -> : Cliff.w{hr} = 0 by smt().
  by rewrite RField.expr0.
+ auto => &hr /> h0 hN h0' hN'; rewrite Ep_dbiased; 1: exact hp.
  split; 1: smt().
  rewrite /= Rp_to_real_eq /= !to_pos_pos; 1..5: smt(value_bnd).
  rewrite RField.exprS 1:/#.
  have -> : rho ^ Cliff.w{hr} = rho * rho ^ (Cliff.w{hr} - 1).
  + by rewrite -RField.exprS 1:/#.
  rewrite /rho; field; 1: smt(p_bnd).
  by have := rhoN_neq1; rewrite /rho; smt().
+ move=> &hr hw /=.
  by have := value_bnd _ hw; move=> hv; rewrite to_pos_pos; smt().
while /ast ((if p <= 1%r / 2%r then Cliff.w else N - Cliff.w)%r)
  (fun (_ : real) => if p <= 1%r / 2%r then 1%r - p else p) (fun (_ : real) => 1%r).
+ by auto => &hr /> *; rewrite Ep_dbiased 1:hp /=; smt().
+ by move=> &hr /#.
+ move=> v; auto => &hr /> *; rewrite Ep_dbiased 1:hp /=.
  split; 1: smt().
  by case: (p <= inv 2%r) => hp2 /=; rewrite !to_pos_pos; smt().
+ move=> v; auto => &hr /> *; rewrite Ep_dbiased 1:hp /=.
  by case: (p <= inv 2%r) => hp2 /=; rewrite !to_pos_pos; smt().
by move=> _; smt(p_bnd).
qed.

(* as a probability: the goal is reached with probability (rho^w - 1) / (rho^N - 1) *)
lemma pr_cliff &m : 0 <= Cliff.w{m} <= N =>
  Pr[Cliff.run() @ &m : res] = (rho ^ Cliff.w{m} - 1%r) / (rho ^ N - 1%r).
proof. by move=> hw; byehoare cliff_value. qed.

end section.
