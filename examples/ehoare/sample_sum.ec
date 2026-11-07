(* The expected sum of k independent samples uniform in [0..10] is exactly
   5 * k.  The loop runs exactly k times, so the variant rule applies, on an
   equality judgment, with the invariant {0 <= s /\ i <= k | s + 5 (k - i)}.
   Unlike the conjunction example, the invariant is unbounded: the decay rule
   would need a finite super-invariant bound on it, the variant rule needs
   nothing besides the decrease of k - i. *)

require import AllCore Int Real Xreal Distr DInterval StdOrder List StdBigop.
import RealOrder.

module Sum = {
  var s : int
  var i : int

  proc run(k : int) : int = {
    var x : int;
    s <- 0;
    i <- 0;
    while (i < k) {
      x <$ [0..10];
      s <- s + x;
      i <- i + 1;
    }
    return s;
  }
}.

(* The mean of [0..10] is 5: the expectation is a sum over the interval,
   turned into a real sum and computed. *)
lemma sum_0_10 :
  Bigreal.BRA.bigi predT (fun (i : int) => i%r) 0 (10 + 1) = 55%r.
proof.
  have h := Bigreal.sumidE (10 + 1) _; 1: by [].
  by rewrite h; smt().
qed.

lemma Ep_dinter_mean (c : int) : 0 <= c =>
  Ep [0..10] (fun (x : int) => (c + x)%xr) = (c + 5)%xr.
proof.
  move=> hc.
  rewrite (Ep_dinterval_le _ 0 10) 1://.
  rewrite -(is_real_bigRX (fun (x : int) => (c + x)%xr)) 1:/#.
  rewrite bigR_to_real.
  + by move=> a /mem_range ha /=; smt().
  rewrite (Bigreal.BRA.eq_bigr _ _ (fun (i : int) => c%r + i%r)).
  + by move=> i _ /=; rewrite fromintD.
  rewrite Bigreal.BRA.big_split Bigreal.sumr_const count_predT size_range.
  rewrite sum_0_10 /=.
  rewrite -of_realI -of_realM; 1,2: smt().
  by congr; smt().
qed.

lemma sum_exact :
  ehoare [=] [Sum.run : {0 <= k | (5 * k)%xr} ==> {true | res%xr}].
proof.
  proc.
  while ((0 <= Sum.s /\ Sum.i <= k), (Sum.s + 5 * (k - Sum.i))%xr) (k - Sum.i).
  (* exit: i = k, and the invariant is s *)
  + move=> &hr [[hs hik] hstop] /=.
    have -> : k{hr} - Sum.i{hr} = 0 by smt().
    by rewrite /=.
  (* body: P is preserved, k - i decreases, and the expectation is exact *)
  + move=> z.
    wp.
    skip => &hr /=.
    move=> [[[hs hik] hlt] <-].
    split; 1: by move=> x0 /supp_dinter hx0; smt().
    rewrite (eq_Ep _ _
      (fun (x0 : int) => ((Sum.s{hr} + 5 * (k{hr} - (Sum.i{hr} + 1))) + x0)%xr)).
    + by move=> x0 _ /=; congr; ring.
    rewrite Ep_dinter_mean 1:/#.
    by smt().
  (* the variant is non-negative inside the loop *)
  + by move=> &hr [[hs hik] hlt] /=; smt().
  (* prefix *)
  + by wp; skip.
qed.
