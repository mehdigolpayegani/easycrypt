(* The coupon collector: coupons 0 .. n-1 are drawn uniformly until all
   of them have been collected.  The expected number of draws is exactly
   n * H n, with H the harmonic numbers.  The equality is proved with the
   ascent rule for while loops: with k coupons collected, n * H (n - k)
   draws remain on average, so c + n * H (n - k) is invariant in
   expectation, and 2 * n * H (n - k) is the witness bounding the
   expected number of remaining iterations. *)
require import AllCore Int Real List Distr DInterval FSet Xreal StdOrder.
import RealOrder StdBigop.Bigreal.

op n : int.
axiom n_ge1 : 1 <= n.

module CC = {
  var s : int fset
  var c : int
  proc run () : unit = {
    var x;
    s <- fset0; c <- 0;
    while (card s < n) {
      x <$ [0 .. n - 1];
      s <- s `|` fset1 x;
      c <- c + 1;
    }
  }
}.

(* Harmonic numbers. *)
op H (m : int) : real = BRA.bigi predT (fun i => 1%r / i%r) 1 (m + 1).

lemma H0 : H 0 = 0%r.
proof. by rewrite /H BRA.big_geq. qed.

lemma H_S m : 0 <= m => H (m + 1) = H m + 1%r / (m + 1)%r.
proof. by move=> hm; rewrite /H BRA.big_int_recr 1:/#. qed.

lemma H_ge0 m : 0 <= m => 0%r <= H m.
proof.
elim: m => [| m hm hrec]; 1: by rewrite H0.
by rewrite H_S //; smt(divr_ge0).
qed.

(* One step of the coupon collector with m coupons missing:
   n H m = 1 + (n - m) H m + m H (m - 1). *)
lemma H_step m : 1 <= m =>
  n%r * H m = 1%r + (n - m)%r / n%r * (n%r * H m) + m%r / n%r * (n%r * H (m - 1)).
proof.
move=> hm; have -> : H m = H (m - 1) + 1%r / m%r.
+ by have := H_S (m - 1) _; 1: smt().
rewrite !fromintB; field; smt(n_ge1).
qed.

(* A subset of [0 .. n-1] has at most n elements. *)
lemma card_le_n (s : int fset) :
  (forall x, x \in s => 0 <= x < n) => card s <= n.
proof.
move=> hs; have : card s <= card (rangeset 0 n).
+ by apply subset_leq_fcard => x /hs; rewrite mem_rangeset.
by rewrite card_rangeset; smt(n_ge1).
qed.

(* The probability of drawing an already collected coupon. *)
lemma mu_in (s : int fset) :
  (forall x, x \in s => 0 <= x < n) =>
  mu [0 .. n - 1] (fun x => x \in s) = (card s)%r / n%r.
proof.
move=> hs; rewrite (mu_eq _ _ (mem (elems s))); 1: by move=> x; rewrite memE.
rewrite mu_mem_uniq 1:uniq_elems.
rewrite (BRA.eq_big_seq _ (fun _ => 1%r / n%r)).
+ by move=> x hx /=; rewrite dinter1E; smt(memE).
by rewrite sumr_const count_predT -cardE; ring.
qed.

lemma coupon_exact :
  ehoare [=] [CC.run : {true | (n%r * H n)%xr} ==> {true | CC.c%xr}].
proof.
proc.
while /ascent (((forall x, x \in CC.s => 0 <= x < n) /\ 0 <= CC.c),
               (CC.c%r + n%r * H (n - card CC.s))%xr)
              ((2%r * n%r * H (n - card CC.s))%xr).
+ move=> &hr /> hs _ h.
  have -> : n - card CC.s{hr} = 0 by smt(card_le_n).
  by rewrite H0.
+ auto => &hr /> hs hc hk.
  split; 1: by move=> x /supp_dinter hx; split; [smt(in_fsetU in_fset1) | smt()].
  have hHm := H_ge0 (n - card CC.s{hr} - 1) _; 1: smt().
  have hHm1 := H_ge0 (n - card CC.s{hr}) _; 1: smt().
  rewrite (eq_Ep _ _
    ((fun x => of_reald ((CC.c{hr} + 1)%r + n%r * H (n - card CC.s{hr})) ** (x \in CC.s{hr})%xr) +
     (fun x => of_reald ((CC.c{hr} + 1)%r + n%r * H (n - card CC.s{hr} - 1)) ** (!(x \in CC.s{hr}))%xr))).
  + move=> x _ /=; rewrite fcardU1; case: (x \in CC.s{hr}) => _ /=.
    + by rewrite b2i0.
    by rewrite b2i1; congr; congr; congr; congr; ring.
  rewrite EpD !EpsZ !Ep_mu mu_not weight_dinter mu_in //.
  have -> : b2r (0 <= n - 1) = 1%r by smt(n_ge1).
  have hk0 := fcard_ge0 CC.s{hr}.
  have hkn : (card CC.s{hr})%r / n%r <= 1%r by rewrite ler_pdivr_mulr; smt(n_ge1).
  have hn0 := n_ge1.
  rewrite /= Rp_to_real_eq /= !to_pos_pos; 1..5: smt(mulr_ge0 divr_ge0).
  rewrite {1}(H_step (n - card CC.s{hr})) 1:/#.
  by rewrite !(fromintD, fromintB); field; smt().
+ by move=> &hr _; rewrite /is_real.
+ move=> v; auto => &hr /> hs hc hk hv hE.
  have hHm := H_ge0 (n - card CC.s{hr} - 1) _; 1: smt().
  have hHm1 := H_ge0 (n - card CC.s{hr}) _; 1: smt().
  have hk0 := fcard_ge0 CC.s{hr}.
  have hn0 := n_ge1.
  have <- : CC.c{hr}%r + n%r * H (n - card CC.s{hr}) = v.
  + by apply of_reald_pinj => //; smt(mulr_ge0).
  apply (xle_trans (Ep [0..n - 1]
    ((fun x => of_reald (2%r * n%r * H (n - card CC.s{hr}) + 2%r) ** (x \in CC.s{hr})%xr) +
     (fun x => of_reald (2%r * n%r * H (n - card CC.s{hr} - 1) + 1%r) ** (!(x \in CC.s{hr}))%xr)))).
  + apply le_Ep => x _ /=; rewrite fcardU1; case: (x \in CC.s{hr}) => _ /=.
    + by rewrite b2i0 /= hk /= !to_pos_pos; smt(mulr_ge0).
    have hd : n%r * H (n - card CC.s{hr} - 1) + 1%r <= n%r * H (n - card CC.s{hr}).
    + have -> : H (n - card CC.s{hr}) = H (n - card CC.s{hr} - 1) + 1%r / (n - card CC.s{hr})%r.
      + by have := H_S (n - card CC.s{hr} - 1) _; smt().
      have : 1%r <= n%r / (n - card CC.s{hr})%r by rewrite ler_pdivl_mulr; smt().
      smt().
    have -> : n - (b2i true + card CC.s{hr}) = n - card CC.s{hr} - 1 by rewrite b2i1; ring.
    by rewrite /(%pos); smt(mulr_ge0).
  rewrite EpD !EpsZ !Ep_mu mu_not weight_dinter mu_in //.
  have -> : b2r (0 <= n - 1) = 1%r by smt().
  have hkn : (card CC.s{hr})%r / n%r <= 1%r by rewrite ler_pdivr_mulr; smt().
  rewrite /= !to_pos_pos; 1..5: smt(mulr_ge0 divr_ge0).
  have e : 2%r * n%r * H (n - card CC.s{hr}) = 2%r * (n%r * H (n - card CC.s{hr})) by ring.
  rewrite {2}e (H_step (n - card CC.s{hr})) 1:/# -subr_ge0 !(fromintB, fromintD).
  pose K := (card CC.s{hr})%r.
  pose A := H (n - card CC.s{hr}).
  pose B := H (n - card CC.s{hr} - 1).
  have -> : 2%r * (1%r + (n%r - (n%r - K)) / n%r * (n%r * A) + (n%r - K) / n%r * (n%r * B)) -
            ((2%r * n%r * A + 2%r) * (K / n%r) + (2%r * n%r * B + 1%r) * (1%r - K / n%r)) =
            (n%r - K) / n%r.
  + by field; smt().
  by apply divr_ge0; smt().
by auto => &hr /=; rewrite fcards0 /=; smt(in_fset0).
qed.
