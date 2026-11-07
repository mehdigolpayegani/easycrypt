(* The expected number of comparisons of randomised quicksort on n distinct
   elements is exactly Q n = 2 (n + 1) H n - 4 n, where H n is the n-th
   harmonic number.  The logic has no recursion, so quicksort is written
   iteratively with an explicit stack of ranges; each range is split by the
   random partition QS.p_partition of qselect.ec.  The result is an equality
   ehoare [=], proved with the rule while /variant: the invariant value is the
   cost so far plus Q of the size of every pending range, and it is preserved
   exactly by each iteration. *)

require import AllCore Distr List DInterval StdOrder Array Xreal.
require import Qselect.
import StdBigop.Bigreal Partition0.

module Sort = {
  proc qsort (t : elem array) : elem array = {
    var st, lo, hi, p;
    QS.c <- 0;
    st <- [(0, size t - 1)];
    while (st <> []) {
      (lo, hi) <- head witness st;
      st <- behead st;
      if (lo < hi) {
        (t, p) <@ QS.p_partition(t, lo, hi);
        st <- (lo, p - 1) :: (p + 1, hi) :: st;
      }
    }
    return t;
  }
}.

(* -------------------------------------------------------------------- *)
(* Expected number of comparisons on a range of size m.                 *)

op Q (m : int) : real = 2%r * (m + 1)%r * H m - 4%r * m%r.

lemma H0 : H 0 = 0%r.
proof. by rewrite /H BRA.big_geq. qed.

lemma Q0 : Q 0 = 0%r.
proof. by rewrite /Q H0. qed.

lemma Q1 : Q 1 = 0%r.
proof. by rewrite /Q (H_S 0) // H0. qed.

lemma Q_S m : 0 <= m => Q (m + 1) = Q m + 2%r * H (m + 1) - 2%r.
proof.
  move=> hm; rewrite /Q !H_S // !fromintD.
  by field; smt().
qed.

lemma H_ge1 m : 1 <= m => 1%r <= H m.
proof.
  move=> hm; have -> : m = (m - 1) + 1 by ring.
  have : 0 <= m - 1 by smt().
  elim: (m - 1) => [| n hn hrec]; 1: by rewrite (H_S 0) // H0.
  by rewrite (H_S (n + 1)) 1:/#; smt().
qed.

lemma Q_ge0 m : 0 <= m => 0%r <= Q m.
proof.
  elim: m => [| n hn hrec]; 1: by rewrite Q0.
  by rewrite Q_S //; smt(H_ge1).
qed.

(* The recurrence of quicksort: m Q m = m (m - 1) + 2 sum_{k < m} Q k. *)
lemma Q_rec m : 0 <= m =>
  m%r * Q m = m%r * (m - 1)%r + 2%r * BRA.bigi predT Q 0 m.
proof.
  elim: m => [| n hn hrec]; 1: by rewrite BRA.big_geq.
  rewrite BRA.big_int_recr // /=.
  have -> : BRA.bigi predT Q 0 n = (n%r * Q n - n%r * (n - 1)%r) / 2%r.
  + by rewrite hrec; field.
  rewrite /Q H_S // !fromintD.
  by field; smt().
qed.

lemma sum_rev (F : int -> real) n : 0 <= n =>
  BRA.bigi predT (fun i => F (n - 1 - i)) 0 n = BRA.bigi predT F 0 n.
proof.
  elim: n => [| n hn hrec]; 1: by rewrite !BRA.big_geq.
  rewrite (BRA.big_ltn 0 _ (fun i => F (n + 1 - 1 - i))) 1:/#.
  rewrite (BRA.big_int_recr _ _ F) //= RField.addrC.
  have := BRA.big_addn 0 (n + 1) 1 predT (fun i => F (n - i)).
  rewrite /= => ->; have -> : (fun (i : int) => predT (i + 1)) = predT<:int> by done.
  by rewrite -hrec; congr; apply BRA.eq_big_int => i _ /=; congr; ring.
qed.

lemma sum_shift (F : int -> real) lo hi :
  BRA.bigi predT (fun p => F (p - lo)) lo (hi + 1) = BRA.bigi predT F 0 (hi - lo + 1).
proof.
  have := BRA.big_addn 0 (hi + 1) lo predT (fun p => F (p - lo)).
  rewrite /= => ->; have -> : (fun (i : int) => predT (i + lo)) = predT<:int> by done.
  have -> : hi + 1 - lo = hi - lo + 1 by ring.
  by apply BRA.eq_big_int => i _ /=; congr; ring.
qed.

(* One partition of [lo..hi]: m = hi - lo + 1 times Q m is m times the cost
   hi - lo of the partition plus the sum over the pivots p of the expected
   costs of the two sides [lo..p-1] and [p+1..hi]. *)
lemma Q_step lo hi : lo <= hi =>
  (hi - lo + 1)%r * Q (hi - lo + 1) =
  (hi - lo + 1)%r * (hi - lo)%r +
  BRA.bigi predT (fun p => Q (p - lo) + Q (hi - p)) lo (hi + 1).
proof.
  move=> hle; rewrite Q_rec 1:/# (BRA.big_split _ (fun p => Q (p - lo))) /=.
  rewrite (sum_shift Q) (BRA.eq_big_int _ _ (fun p => Q (hi - p))
             (fun p => (fun k => Q (hi - lo + 1 - 1 - k)) (p - lo))).
  + by move=> i _ /=; congr; ring.
  by rewrite (sum_shift (fun k => Q (hi - lo + 1 - 1 - k))) sum_rev 1:/#; ring.
qed.

(* -------------------------------------------------------------------- *)
(* The random partition permutes the range and leaves the rest intact.  *)

lemma uniq_on_perm_except (t t' : elem array) lo hi :
  0 <= lo <= hi < size t =>
  uniq_on t 0 (size t - 1) => perm_eq_on t t' lo hi => eq_except t t' lo hi =>
  uniq_on t' 0 (size t' - 1).
proof.
  move=> hb hu hp he; have hp' := perm_eq_on_eq_except _ _ _ _ hb hp he.
  by case: he => <- _; rewrite -(perm_uniq_on _ _ _ _ hp').
qed.

equiv p_partition_permE t_ lo_ hi_ : QS.p_partition ~ QS.p_partition_abs :
  ={lo,hi,QS.c} /\ lo{1} = lo_ /\ hi{1} = hi_ /\ t{1} = t_ /\ 0 <= lo_ <= hi_ < size t{1} /\
  (uniq_on t lo hi){1}
  ==>
  ={QS.c} /\ uniq_on res.`1{1} lo_ hi_ /\ res.`2{1} = res{2} /\ lo_ <= res.`2{1} <= hi_ /\
  size res.`1{1} = size t_ /\ perm_eq_on t_ res.`1{1} lo_ hi_ /\ eq_except t_ res.`1{1} lo_ hi_.
proof.
  proc.
  seq 1 1 : (#pre /\ p{2} = sindex Partition0.(<=) t{1} lo{1} hi{1} p{1} /\ (lo <= p <= hi){1} ).
  + rnd (sindex Partition0.(<=) t{1} lo{1} hi{1}) (sindex_inv Partition0.(<=) t{1} lo{1} hi{1}); skip => />.
    move=> hlo hlohi hhi hu; split.
    + by move=> p /supp_dinter hp; rewrite sindex_sindex_inv.
    move=> _; split.
    + move=> p /supp_dinter hp.
      by rewrite !dinter1E hp /=; smt(sindex_inv_in).
    move=> _ p /supp_dinter hp; split.
    + by apply/supp_dinter; smt(sindex_in).
    by move=> _; rewrite sindex_inv_sindex //; smt(sindex_in).
  wp.
  ecall{1} (h_partition_ll t{1} QS.c{1} lo{1} hi{1}).
  ecall{1} (h_swap_ll t{1} p{1} hi{1} QS.c{1}); skip => |>.
  move=> &1 &2 hu *.
  split; 1: smt().
  move=> 3? t' hsw.
  have hp := swapP_perm_eq_on _ _ lo_ hi_ _ _ _ _ hsw => //.
  rewrite -(perm_uniq_on _ _ _ _ hp); split; 1: smt().
  move=> ?? [t'' p''] /= hp' hpart *.
  have hp2 := perm_eq_on_trans _ _ _ _ _ hp hp'.
  split; 1: by have /perm_uniq_on <- := hp2.
  split.
  + have -> := perm_sindex t_ t'' lo_ hi_ p{1} p'' _ _ _ hp2 => //; 1:smt().
    rewrite sindex_countP //;  1: by rewrite -(perm_uniq_on _ _ _ _ hp2).
    rewrite (partition_on_sindex _ _ _ _ _ hpart) // /#.
  smt().
qed.

lemma eh_p_partition_perm (f : int -> int -> xreal) (t_ : elem array) (c_ lo_ hi_ : int) :
  ehoare [=] [QS.p_partition :
  {QS.c = c_ /\ lo = lo_ /\ hi = hi_ /\ t = t_ /\ uniq_on t lo hi /\ 0 <= lo_ <= hi_ < size t |
   Ep [lo .. hi] (fun p => f p (QS.c + (hi - lo)*clt))} ==>
  {QS.c = c_ + (hi_ - lo_) * clt /\ lo_ <= res.`2 <= hi_ /\ uniq_on res.`1 lo_ hi_ /\
   size res.`1 = size t_ /\ perm_eq_on t_ res.`1 lo_ hi_ /\ eq_except t_ res.`1 lo_ hi_ |
   f res.`2 QS.c}].
proof.
  conseq (p_partition_permE t_ lo_ hi_)
    (_: {QS.c = c_ /\ lo = lo_ /\ hi = hi_ | Ep [lo .. hi] (fun p => f p (QS.c + (hi - lo)*clt))} ==>
        {QS.c = c_ + (hi_ - lo_) * clt | f res QS.c}).
  + by move=> &1 /> *; exists QS.c{1} (lo, hi){1}.
  + by move=> &1 &2 /> /#.
  proc; auto.
qed.

(* -------------------------------------------------------------------- *)
(* Quicksort.                                                           *)

(* Expected remaining cost of the pending ranges. *)
op SQ (st : (int * int) list) : real =
  BRA.big predT (fun (r : int * int) => Q (r.`2 - r.`1 + 1)) st.

(* Termination measure: a range of size m weighs 2 m + 1. *)
op V (st : (int * int) list) : int =
  StdBigop.Bigint.BIA.big predT (fun (r : int * int) => 2 * (r.`2 - r.`1 + 1) + 1) st.

(* The pending ranges lie inside an array of size n and may be empty. *)
op ranges_in (n : int) (st : (int * int) list) =
  forall r, r \in st => 0 <= r.`1 /\ r.`2 < n /\ r.`1 - 1 <= r.`2.

lemma SQ_ge0 n st : ranges_in n st => 0%r <= SQ st.
proof.
  move=> hst; apply sumr_ge0_seq => r hr _ /=.
  by apply Q_ge0; smt().
qed.

lemma V_ge0 n st : ranges_in n st => 0 <= V st.
proof.
  move=> hst; apply StdBigop.Bigint.sumr_ge0_seq => r hr _ /=; smt().
qed.

lemma qsort_exact :
  ehoare [=] [Sort.qsort : {uniq_on t 0 (size t - 1) | (Q (size t))%xr} ==> {true | QS.c%xr}].
proof.
  proc.
  while /variant ((0 <= QS.c /\ uniq_on t 0 (size t - 1) /\ ranges_in (size t) st),
                  (QS.c%r + SQ st)%xr) (V st).
  + by move=> &hr [#] hc _ _ /= ->; rewrite /SQ BRA.big_nil.
  + move=> k; case: ((head witness st).`1 < (head witness st).`2).
    (* a range of size at least 2 is partitioned *)
    + rcondt 3; 1: by auto.
      wp; exlim (head witness st).`1, (head witness st).`2, (behead st), t, QS.c
        => lo_ hi_ rest_ t_ c_.
      call (eh_p_partition_perm
              (fun p (c : int) => (c%r + SQ ((lo_, p - 1) :: (p + 1, hi_) :: rest_))%xr)
              t_ c_ lo_ hi_).
      wp; skip => &hr /= [#] ->> ->> ->> ->> ->> hc hu hr hne <<- hlt.
      move: (st{hr}) hr hne hlt => -[// | [l h] rest] /= hr hlt.
      have [#] hl hh _ := hr (l, h) _ => //.
      split; 1: split; 1: smt(uniq_on_sub).
      + move=> _ [t1 p1] c1 /= [#] -> hpl hph _ hsz hperm hex.
        rewrite /V !StdBigop.Bigint.BIA.big_cons /predT /= hsz; split; 2: smt().
        split; 1: by rewrite /clt /#.
        split; 2: by move=> r /= [| [|]] => [-> | -> | hin] /=; smt().
        by rewrite -hsz; apply (uniq_on_perm_except t{hr} t1 l h) => // /#.
      have hS : 0%r <= SQ rest by apply (SQ_ge0 (size t{hr})) => r hin; apply hr => /#.
      move: (QS.c{hr}) hc => c hc {hr hu}.
      rewrite Ep_dinterval_le 1:/# /clt /=.
      rewrite (BXA.eq_big_int _ _ _
                 (fun p => (((c + (h - l))%r + SQ rest) + (Q (p - l) + Q (h - p)))%xr)).
      + move=> p hp /=; rewrite /SQ !BRA.big_cons /predT /=.
        by rewrite (: p - 1 - l + 1 = p - l) 1:/# (: h - (p + 1) + 1 = h - p) 1:/#; congr; ring.
      have hQ : forall p, l <= p <= h => 0%r <= Q (p - l) + Q (h - p).
      + by move=> p hp; apply RealOrder.addr_ge0; apply Q_ge0 => /#.
      rewrite bigiXR /=; 1: by move=> i hi; have := hQ i _; smt().
      rewrite BRA.big_split sumri_const 1:/# /=.
      have -> : BRA.bigi predT (fun (i : int) => Q (i - l) + Q (h - i)) l (h + 1) =
                (h - l + 1)%r * Q (h - l + 1) - (h - l + 1)%r * (h - l)%r.
      + by rewrite Q_step 1:/#; ring.
      have -> : SQ ((l, h) :: rest) = Q (h - l + 1) + SQ rest by rewrite /SQ BRA.big_cons.
      have hQm := Q_ge0 (h - l + 1) _; 1: smt().
      rewrite Rp_to_real_eq /= !to_pos_pos; 1..3: smt().
      have -> : h + 1 - l = h - l + 1 by ring.
      by rewrite !fromintD; field; smt().
    (* a range of size 0 or 1 is dropped *)
    rcondf 3; 1: by auto.
    wp; skip => &hr /= [#] hc hu hr hne <<-.
    move: (st{hr}) hr hne => -[// | [l h] rest] /= hr hle.
    have [#] _ _ hlh := hr (l, h) _ => //.
    rewrite /V /SQ !StdBigop.Bigint.BIA.big_cons BRA.big_cons /predT /=.
    have -> : Q (h - l + 1) = 0%r.
    + case: (h - l + 1 = 0) => [-> | ?]; 1: by apply Q0.
      by rewrite (: h - l + 1 = 1) 1:/# Q1.
    smt().
  + by move=> &hr [#] _ _ hr _; apply (V_ge0 _ _ hr).
  wp; skip => &hr /= hu; rewrite /SQ BRA.big_seq1 /= hu /=.
  by move=> r /= ->; smt(size_ge0).
qed.

(* -------------------------------------------------------------------- *)
(* Functional correctness: quicksort sorts and permutes its input.      *)

(* The positions i <= j lie in a common pending range. *)
op covered (st : (int * int) list) (i j : int) =
  exists r, r \in st /\ r.`1 <= i /\ j <= r.`2.

(* Every pair of positions not in a common pending range is in order. *)
op sorted_except (st : (int * int) list) (t : elem array) =
  forall i j, 0 <= i < j < size t => covered st i j \/ t.[i] <= t.[j].

(* Two ranges do not overlap (an empty range overlaps nothing). *)
op apart (r1 r2 : int * int) =
  r1.`2 < r2.`1 \/ r2.`2 < r1.`1 \/ r1.`2 < r1.`1 \/ r2.`2 < r2.`1.

(* The pending ranges are pairwise disjoint. *)
op disj (st : (int * int) list) : bool =
  with st = [] => true
  with st = r :: rest => (forall r', r' \in rest => apart r r') /\ disj rest.

(* A permuted range holds the values of the original range. *)
lemma perm_eq_on_get (t t' : elem array) lo hi j :
  lo <= j <= hi => perm_eq_on t t' lo hi => exists j', lo <= j' <= hi /\ t'.[j] = t.[j'].
proof.
  move=> hj hp; apply (mem_sub t lo hi t'.[j]).
  by rewrite (perm_eq_mem _ _ hp) mem_array_sub.
qed.

(* A range of size at most 1 covers no pair of distinct positions. *)
lemma sorted_except_pop (t : elem array) lo hi rest :
  hi <= lo => sorted_except ((lo, hi) :: rest) t => sorted_except rest t.
proof.
  move=> hle hs i j hij.
  by case: (hs i j hij) => [[r] h | ->]; [left; exists r | right]; smt().
qed.

(* Partitioning the pending range [lo..hi] around p splits it into
   [lo..p-1] and [p+1..hi]: the pairs that straddle p become ordered, the
   rest of the array is unchanged, and the pairs with one position outside
   [lo..hi] stay ordered since [lo..hi] is only permuted. *)
lemma sorted_except_partition (t t' : elem array) lo p hi rest :
  0 <= lo <= p <= hi < size t =>
  disj ((lo, hi) :: rest) =>
  sorted_except ((lo, hi) :: rest) t =>
  partition_on t' lo p hi => perm_eq_on t t' lo hi => eq_except t t' lo hi =>
  sorted_except ((lo, p - 1) :: (p + 1, hi) :: rest) t'.
proof.
  move=> hb /= [hd _] hs [hlt hge] hp [hsz he] i j hij.
  have hr : forall i' j', i' < j' => covered rest i' j' => j' < lo \/ hi < i'.
  + by move=> i' j' hij' [r [hr h]]; have := hd r hr; rewrite /apart /#.
  case: (covered rest i j) => hc.
  + by left; case: hc => r [hr' h]; exists r; rewrite /= hr'.
  have hs' : forall i' j', 0 <= i' < j' < size t => !(lo <= i' /\ j' <= hi) =>
    !covered rest i' j' => t.[i'] <= t.[j'].
  + move=> i' j' h h1 h2; case: (hs i' j' h) => [[r] hr' | //].
    case: hr' => /= -[->> /# | hin] hh.
    by have /# : covered rest i' j' by exists r.
  case: (lo <= i <= hi) => hi_; case: (lo <= j <= hi) => hj.
  + case: (j < p) => hjp; 1: by left; exists (lo, p - 1) => /#.
    case: (p < i) => hip; 1: by left; exists (p + 1, hi) => /#.
    by right; smt(le_trans).
  + have [i' [hi' ->]] := perm_eq_on_get t t' lo hi i hi_ hp.
    by right; rewrite -he 1:/#; apply hs'; smt().
  + have [j' [hj' ->]] := perm_eq_on_get t t' lo hi j hj hp.
    by right; rewrite -he 1:/#; apply hs'; smt().
  by right; rewrite -!he 1,2:/#; apply hs'; smt().
qed.

lemma disj_partition lo p hi rest :
  lo <= p <= hi => disj ((lo, hi) :: rest) => disj ((lo, p - 1) :: (p + 1, hi) :: rest).
proof. by rewrite /= /apart => hp [hd ->] /=; smt(). qed.

(* The random partition permutes [lo..hi] around the returned pivot and
   leaves the rest of the array unchanged. *)
hoare h_p_partition (t_ : elem array) lo_ hi_ : QS.p_partition :
  t = t_ /\ lo = lo_ /\ hi = hi_ /\ 0 <= lo <= hi < size t
  ==>
  lo_ <= res.`2 <= hi_ /\ partition_on res.`1 lo_ res.`2 hi_ /\
  perm_eq_on t_ res.`1 lo_ hi_ /\ eq_except t_ res.`1 lo_ hi_.
proof.
  proc; ecall (h_partition t QS.c lo hi); ecall (h_swap t p hi QS.c); rnd; skip => />.
  move=> 3? p /supp_dinter hp; split; 1: smt().
  move=> 3? t1 hsz hk h1 h2; split => [/# | _ [t2 p2] /= hp2 *].
  have hsw : swapP t_ t1 p hi_ by done.
  have hp1 := swapP_perm_eq_on _ _ lo_ hi_ _ _ _ _ hsw => //.
  split; 1: by apply (perm_eq_on_trans t1).
  smt().
qed.

op sorted_on (t : elem array) = forall i j, 0 <= i <= j < size t => t.[i] <= t.[j].

(* Quicksort returns a sorted permutation of its input (the elements need
   not be distinct). *)
lemma qsort_sorted (t0 : elem array) :
  hoare [Sort.qsort : t = t0 ==> sorted_on res /\ perm_eq (ofarray t0) (ofarray res)].
proof.
  proc.
  while (size t = size t0 /\ ranges_in (size t) st /\ disj st /\ sorted_except st t /\
         perm_eq_on t0 t 0 (size t0 - 1)).
  + case: ((head witness st).`1 < (head witness st).`2).
    (* a range of size at least 2 is partitioned *)
    + rcondt 3; 1: by auto.
      wp; exlim (head witness st).`1, (head witness st).`2, t => lo_ hi_ t_.
      call (h_p_partition t_ lo_ hi_).
      wp; skip => &hr [#] ->> ->> ->> hsz hr hd hs hp.
      move: (st{hr}) hr hd hs => -[// | [l h] rest] hr hd hs _ /= hlt.
      have [#] hl hh _ := hr (l, h) _ => //.
      split => [/# | _].
      move=> [t1 p1] /= [#] hpl hph hpart hperm hex.
      have hsz1 : size t1 = size t{hr} by case: hex => ->.
      split; 1: by rewrite hsz1.
      split; 1: by rewrite hsz1 => r /= -[-> | [-> | hin]] /=; smt().
      split; 1: by have := disj_partition l p1 h rest _ hd.
      split; 1: by apply (sorted_except_partition t{hr}) => // /#.
      apply (perm_eq_on_trans t{hr}) => //.
      by rewrite -hsz; apply (perm_eq_on_eq_except _ _ l h) => // /#.
    (* a range of size 0 or 1 is dropped *)
    rcondf 3; 1: by auto.
    wp; skip => &hr [#] hsz hr hd hs hp.
    move: (st{hr}) hr hd hs => -[// | [l h] rest] hr hd hs _ /= hle.
    split => //; split; 1: by move=> r hin; apply hr; rewrite /= hin.
    split; 1: by case: hd.
    by split => //; apply (sorted_except_pop _ l h) => /#.
  wp; skip => />; split.
  + split; 1: by move=> r /= ->; smt(size_ge0).
    split; 2: by apply perm_eq_refl.
    by move=> i j hij; left; exists (0, size t0 - 1) => /#.
  move=> t1 hsz _ hs hp; split.
  + move=> i j hij; case: (i = j) => [-> | hne]; 1: by right.
    by have /# : 0 <= i < j < size t1 by smt().
  by move: hp; rewrite /perm_eq_on array_sub_full -hsz array_sub_full.
qed.
