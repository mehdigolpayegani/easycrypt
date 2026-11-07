(* Gambler's ruin: a symmetric random walk on 0..N, absorbed at both ends,
   with a counter c of the steps.
   - gambler_exact: from 0 <= w <= N, the walk reaches N before 0 with
     probability exactly w/N. The value w/N is an exact martingale bounded
     by 1; rule [while /bounded] on an [=] goal, whose termination premise
     is discharged by rule [while /ast] with variant w, progress
     probability 1/2 and decrease 1.
   - pr_gambler: the same result as a probability, by [byehoare].
   - gambler_time: the expected final value of c is exactly c + w (N - w).
     The value c + w (N - w) is an exact martingale, equal to c on exit;
     rule [while /ascent] (Hark, Kaminski, Giesl and Katoen, with the
     expected increase of the invariant in place of a bounded change), with
     witness (N + 1) w (N - w) bounding the expected number of remaining
     iterations plus the expected increases of the invariant.
   - gambler_duration: from c = 0, the expected duration of the game is
     exactly w (N - w), by [conseq]. *)
require import AllCore Int Real Xreal Distr DBool StdOrder.
import RealOrder.

op N : int.
axiom N_ge1 : 1 <= N.

module G = {
  var w : int
  var c : int
  proc run () : bool = {
    var b;
    while (0 < w < N) {
      b <$ {0,1};
      w <- if b then w + 1 else w - 1;
      c <- c + 1;
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

lemma gambler_time :
  ehoare [=] [G.run : {0 <= G.w <= N /\ 0 <= G.c | (G.c%r + G.w%r * (N - G.w)%r)%xr}
                 ==> {true | G.c%xr}].
proof.
proc.
while /ascent (((N + 1)%r * G.w%r * (N - G.w)%r)%xr).
+ (* on exit w = 0 or w = N *)
  move=> &hr /> h0 hN hc hb.
  have -> : G.w{hr}%r * (N - G.w{hr})%r = 0%r by smt().
  by [].
+ (* c + w (N - w) is an exact martingale *)
  auto => &hr /> h0 hN hc h0' hN'; rewrite Ep_dbool /=.
  split; 1: smt().
  rewrite Rp_to_real_eq /= !to_pos_pos; 1..3: smt(mulr_ge0).
  by rewrite !(fromintD, fromintN, fromintB); field.
+ by move=> &hr _; rewrite /is_real.
(* one step of the walk changes c + w (N - w) by N - 2w or 2w - N, each with
   probability 1/2, and |N - 2w| <= N *)
move=> v; auto => &hr /> h0 hN hc h0' hN' hE; rewrite Ep_dbool /=.
move=> hv; have <- : G.c{hr}%r + G.w{hr}%r * (N - G.w{hr})%r = v.
+ by apply of_reald_pinj => //; smt(mulr_ge0).
rewrite !(fromintD, fromintB, fromintN).
have hW1 : 1%r <= G.w{hr}%r by smt().
have hWN : G.w{hr}%r + 1%r <= N%r by smt().
have hC : 0%r <= G.c{hr}%r by smt().
have hB1 : 0%r <= b2r (0 < G.w{hr} + 1 < N) <= 1%r by smt().
have hB2 : 0%r <= b2r (0 < G.w{hr} - 1 < N) <= 1%r by smt().
move: hW1 hWN hC hB1 hB2.
pose W := G.w{hr}%r; pose C := G.c{hr}%r; pose M := N%r.
pose B1 := b2r (0 < G.w{hr} + 1 < N); pose B2 := b2r (0 < G.w{hr} - 1 < N).
move=> hW1 hWN hC hB1 hB2.
rewrite (to_pos_pos B1); 1: smt().
rewrite (to_pos_pos B2); 1: smt().
rewrite (to_pos_pos (C + W * (M - W))); 1: smt(mulr_ge0).
rewrite (to_pos_pos (C + 1%r + (W + 1%r) * (M - (W + 1%r)))); 1: smt(mulr_ge0).
rewrite (to_pos_pos (C + 1%r + (W - 1%r) * (M - (W - 1%r)))); 1: smt(mulr_ge0).
rewrite (to_pos_pos ((M + 1%r) * (W + 1%r) * (M - (W + 1%r)))); 1: smt(mulr_ge0).
rewrite (to_pos_pos ((M + 1%r) * (W - 1%r) * (M - (W - 1%r)))); 1: smt(mulr_ge0).
rewrite (to_pos_pos ((M + 1%r) * W * (M - W))); 1: smt(mulr_ge0).
pose X1 := (M + 1%r) * (W + 1%r) * (M - (W + 1%r)) + 1%r + _.
pose X2 := (M + 1%r) * (W - 1%r) * (M - (W - 1%r)) + 1%r + _.
have hX1 : 0%r <= X1 by smt(mulr_ge0).
have hX2 : 0%r <= X2 by smt(mulr_ge0).
(* the indicators of staying in the loop only drop non-negative terms *)
apply (ler_trans (X1 / 2%r + X2 / 2%r)); 1: smt(ler_pimull).
rewrite /X1 /X2.
have -> : C + 1%r + (W + 1%r) * (M - (W + 1%r)) - (C + W * (M - W)) = M - 2%r * W by ring.
have -> : C + 1%r + (W - 1%r) * (M - (W - 1%r)) - (C + W * (M - W)) = 2%r * W - M by ring.
have hm : (M - 2%r * W)%pos + (2%r * W - M)%pos <= M by rewrite /(%pos); smt().
have e : (M + 1%r) * (W + 1%r) * (M - (W + 1%r)) + (M + 1%r) * (W - 1%r) * (M - (W - 1%r)) =
         2%r * ((M + 1%r) * W * (M - W)) - 2%r * (M + 1%r) by ring.
smt().
qed.

(* the expected duration of the game is w (N - w) *)
lemma gambler_duration :
  ehoare [=] [G.run : {0 <= G.w <= N /\ G.c = 0 | (G.w%r * (N - G.w)%r)%xr} ==> {true | G.c%xr}].
proof. by conseq gambler_time => />. qed.
