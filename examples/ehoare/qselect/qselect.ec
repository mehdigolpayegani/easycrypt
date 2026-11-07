require import AllCore Distr List DInterval StdOrder.
require import Array.
require import Xreal.
import StdBigop.Bigreal.
import StdBigop.Bigint.

require Partition.

clone import Partition as Partition0.



lemma sumidE_rm (m n : int) : m <= n =>
   2 * sumid m n = (n-m) * (n + m - 1).
proof.
  move=> h.
  rewrite -{1}(add0r m) BIA.big_addn /= BIA.big_split /predT.
  have hnm : 0 <= n - m by smt().
  rewrite !Num.Domain.mulrDr sumidE_r 1://.
  rewrite bigi_constz 1://; ring.
qed.

(* cost less-th-an *)
op clt = 1.

lemma clt_ge0 : 0 <= clt.
proof. done. qed.

module QS = {
  var c : int

  proc swap_(t : elem array, i j : int) : elem array = {
    var aux;
    aux <- t.[i];
    t.[i] <- t.[j];
    t.[j] <- aux;
    return t;
  }

  proc partition(t : elem array, lo hi : int ) : elem array * int = {
    var pv, i, j;
    pv <- t.[hi];
    i <- lo - 1;
    j <- lo;
    while (j < hi) { 
      if (t.[j] < pv) {
        i <- i + 1;
        t <@ swap_(t, i, j);
      }
      c <- c + clt;
      j <- j + 1;
    }
    i <- i + 1;
    t <@ swap_(t, i, hi);
    return (t, i);
  }
  
  proc p_partition(t : elem array, lo hi : int) : elem array * int = {
    var p;
    p <$ [lo .. hi];
    t <@ swap_(t, p, hi);
    (t, p) <@ partition(t, lo, hi);
    return (t,p);
  }

  proc qselect(t : elem array, pos: int) : elem = {
    var lo, hi, p : int;
    c <- 0;
    lo <- 0;
    hi <- size t - 1;
    p <- 0;
    while (lo < hi) {
      (t, p) <@ p_partition(t, lo, hi);
      if (p = pos) { lo <- p; hi <- p; }
      else { if (p < pos) lo <- p + 1; else hi <- p - 1; }
    }
    return t.[pos];
  }

  proc p_partition_abs(lo hi : int) : int = {
    var p;
    p <$ [lo .. hi];
    c <- c + (hi - lo) * clt;
    return p;
  }

  proc qselect_abs(t : elem array, pos: int) = {
    var lo, hi, p : int;
    c <- 0;
    lo <- 0;
    hi <- size t - 1;
    p <- 0;
    while (lo < hi) {
      p <@ p_partition_abs(lo, hi);
      if (p = pos) { lo <- p; hi <- p; }
      else { if (p < pos) lo <- p + 1; else hi <- p - 1; }
    }
  }

}.

import var QS.

hoare h_swap t_ i_ j_ c_ : QS.swap_ : 
     t = t_ /\ i = i_ /\ j = j_ /\ c = c_ /\ 0 <= i < size t /\ 0 <= j < size t 
     ==>
     c = c_ /\ swapP t_ res i_ j_.
proof. by proc; auto => />; smt (get_set size_set). qed.

phoare h_swap_ll t_ i_ j_ c_ : [QS.swap_ : 
     t = t_ /\ i = i_ /\ j = j_ /\ c = c_ /\ 0 <= i < size t /\ 0 <= j < size t 
     ==>
     c = c_ /\ swapP t_ res i_ j_] = 1%r.
proof. by conseq (_: true ==> true) (h_swap t_ i_ j_ c_) => //; islossless. qed.

hoare h_partition (t_ : elem array) (c_ lo_ hi_ : int) : QS.partition :
    c = c_ /\ t = t_ /\ lo = lo_ /\ hi = hi_ /\ 0 <= lo <= hi < size t
    ==>
    let (t,p) = (res.`1, res.`2) in 
    perm_eq_on t_ t lo_ hi_ /\ partition_on t lo_ p hi_ /\ t.[p] = t_.[hi_] /\ lo_ <= p <= hi_ /\
    (* This is needed for for function correctness of qselect, only equality on size is needed for complexity *)
    eq_except t_ t lo_ hi_ /\  
    (* Only needed for complexity *)
    c = c_ + (hi_ - lo_) * clt.
proof.
  proc; ecall (h_swap t i hi c). wp.
  while ((forall k, 0 <= k < size t_ => 
         if lo <= k < j then 
           if k <= i then t.[k] < pv
           else pv <= t.[k]
         else t.[k] = t_.[k]) /\ 
         0 <= lo /\ i < j /\ lo <= i + 1 /\    
         lo <= j <= hi < size t /\ eq_except t_ t lo hi /\ 
         perm_eq_on t_ t lo hi /\ t.[hi] = pv /\
         c = c_ + (j - lo) * clt).
  + wp; if; last by skip => />; smt(clt_ge0 lt_nle).
    ecall (h_swap t i j c); wp; skip => |>.
    move=> &hr 8? hpe *; split; 1: smt().
    move=> 4? t' *; rewrite 4!andbA; split; 1: smt().
    split; 2: smt().
    apply: (perm_eq_on_trans _ _ _ _ _ hpe).
    by apply (swapP_perm_eq_on t{hr} t' lo{hr} hi{hr} (i{hr} + 1) j{hr}) => /#.
  wp; skip => |> &hr *; split; 1: smt(perm_eq_refl).
  move=> c0 i0 j0 t0 7? hpe *; split; 1: smt().
  move=> 3? t' hp; split; 2: smt().
  apply: (perm_eq_on_trans _ _ _ _ _ hpe).
  by apply: swapP_perm_eq_on hp => /#.
qed.

phoare h_partition_ll t_ c_ lo_ hi_: [ QS.partition :
    c = c_ /\ t = t_ /\ lo = lo_ /\ hi = hi_ /\ uniq_on t lo hi /\ 0 <= lo <= hi < size t
    ==>
    let (t,p) = (res.`1, res.`2) in 
    perm_eq_on t_ t lo_ hi_ /\ partition_on t lo_ p hi_ /\ t.[p] = t_.[hi_] /\ lo_ <= p <= hi_ /\
    eq_except t_ t lo_ hi_ /\
    c = c_ + (hi_ - lo_) * clt ] = 1%r.
proof.
  conseq (_: true ==> true) (h_partition t_ c_ lo_ hi_) => //.
  proc; inline QS.swap_; wp.
  by while true (hi - j); auto => /#.
qed.

equiv p_partitionE t_ lo_ hi_ : QS.p_partition ~ QS.p_partition_abs : 
  ={lo,hi,c} /\ lo{1} = lo_ /\ hi{1} = hi_ /\ t{1} = t_ /\ 0 <= lo_ <= hi_ < size t{1} /\ (uniq_on t lo hi){1} 
  ==> 
  ={c} /\ uniq_on res.`1{1} lo_ hi_ /\ res.`2{1} = res{2} /\ lo_ <= res.`2{1} <= hi_ /\ size res.`1{1} = size t_.
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
  ecall{1} (h_partition_ll t{1} c{1} lo{1} hi{1}).
  ecall{1} (h_swap_ll t{1} p{1} hi{1} c{1}); skip => |>.
  move=> &1 &2 hu *.
  split; 1: smt().
  move=> 3? t' hsw.
  have hp := swapP_perm_eq_on _ _ lo_ hi_ _ _ _ _ hsw => //.
  rewrite -(perm_uniq_on _ _ _ _ hp); split; 1: smt().
  move=> ?? [t'' p''] /= hp' hpart *.
  have hp2 := perm_eq_on_trans _ _ _ _ _ hp hp'.
  split; 1: by have /perm_uniq_on <- := hp2.
  have -> := perm_sindex t_ t'' lo_ hi_ p{1} p'' _ _ _ hp2 => //; 1:smt().
  rewrite sindex_countP //;  1: by rewrite -(perm_uniq_on _ _ _ _ hp2).
  rewrite (partition_on_sindex _ _ _ _ _ hpart) // /#. 
qed.

ehoare eh_p_partition f t_ c_ lo_ hi_: QS.p_partition :
  {c = c_ /\ lo = lo_ /\ hi = hi_ /\ t = t_ /\ uniq_on t lo hi /\ 0 <= lo_ <= hi_ < size t |
   Ep [lo .. hi] (fun p => f p (c + (hi - lo)*clt))} ==>
  {c = c_ + (hi_ - lo_) * clt /\ lo_ <= res.`2 <= hi_ /\ uniq_on res.`1 lo_ hi_ /\ size res.`1 = size t_ |
   f res.`2 c}.
proof.
  conseq (p_partitionE t_ lo_ hi_)
    (_: {c = c_ /\ lo = lo_ /\ hi = hi_ | Ep [lo .. hi] (fun p => f p (c + (hi - lo)*clt))} ==>
        {c = c_ + (hi_ - lo_) * clt | f res c}) => />.
  + by move=> &1 *; exists c_ (lo, hi){1}.
  proc; auto.
qed.

ehoare eh_qselect : QS.qselect :
  {0 <= pos < size t /\ uniq_on t 0 (size t - 1) | (4 * (size t - 1))%xr} ==> {true | c%xr}.
proof.
  proc.
  while ((0 <= lo <= pos <= hi < size t /\ uniq_on t lo hi /\ 0 <= c), c%xr + (4 * (hi - lo))%xr).
  + by move=> &hr /> *; smt().
  + wp; exlim t, c, lo, hi, pos => t_ c_ lo_ hi_ pos_.
    call
      (eh_p_partition (fun p (c : int) =>
        if p = pos_ then c%xr
        else if p < pos_ then c%xr + (4 * (hi_ - (p+1)))%xr
        else  c%xr + (4 * ((p-1) - lo_))%xr)
       t_ c_ lo_ hi_).
    skip => &hr /= [#] 5!-> [#] hlo hpos hhi huniq hc hlt hlohi; split.
    + split; 1: smt().
      by move=> _ [t0 p0] c0 /= [#] -> hp0lo hp0hi hu hsz; smt(uniq_on_sub).
    move: (pos{hr}) (lo{hr}) (hi{hr}) (t{hr}) (c{hr}) hlo hpos hhi huniq hc hlt hlohi
      => {&hr lo_ hi_ pos_ t_ c_} pos lo hi t c *.
    rewrite -(eq_Ep _ (
         (fun (p0 : int) =>
            if p0 = pos then 0%xr
            else if p0 < pos then (4 * (hi - (p0 + 1)))%xr
                 else (4 * (p0 - 1 - lo))%xr)
          + (fun (_:int) => (c + (hi - lo))%xr))).
    + by move=> p /supp_dinter hp /=; case: (p = pos) => //#.
    rewrite EpD EpC dinter_ll 1:/# /=.
    have -> : (c%rp + (4 * (hi - lo))%rp)%xr = (3 * (hi - lo))%xr + (c + (hi - lo))%xr.
    + by rewrite /= -!of_realD /#.
    apply xler_addr.
    rewrite Ep_dinterval (: lo <= hi) 1:/# /=.
    rewrite (BXA.big_cat_int pos) 1:// 1:/#.
    rewrite (BXA.eq_big_int lo pos _ (fun p => (4 * ((hi - 1) - p))%xr)) 1:/#.
    rewrite bigiXI 1:/# BXA.big_ltn 1:/#.
    rewrite (BXA.eq_big_int (pos + 1) (hi + 1) _ (fun p => (4 * (p - (1 + lo)))%xr)) 1:/#.
    rewrite bigiXI 1:/# /=.
    rewrite -!BIA.mulr_sumr BIA.big_split bigi_constz 1://.
    rewrite BIA.big_split bigi_constz 1:/#.
    have /= <- := BIA.sumrN<:int> predT (fun x => x).
    rewrite Num.Domain.mulrDr mulrN. 
    have -> : 4 * sumid lo pos = 2 * (2 * sumid lo pos) by ring.
    rewrite sumidE_rm 1://.
    have -> : 4 * ((hi - 1) * (pos - lo)) - 2 * ((pos - lo) * (pos + lo - 1)) = 
             (pos - lo) * (4 * (hi - 1) - 2 * (pos + lo - 1)) by ring.
    rewrite (Num.Domain.mulrDr 4 (sumid _ _)).
    have -> : 4 * sumid (pos + 1)(hi + 1) = 2 * (2 * sumid (pos + 1)(hi + 1)) by ring.
    rewrite sumidE_rm 1:/#.
    apply RealOrder.ler_pdivr_mulr; 1: smt().
    rewrite !to_pos_pos 1,3,4:/#.
    + rewrite le_fromint.
      pose h1 := hi + 1; pose p1 := pos + 1. pose lo1 := 1+ lo.
      have -> : 2 * ((h1 - p1) * (h1 + p1 - 1)) + 4 * ((- lo1) * (h1 - p1)) = 
                (h1 - p1) * (2 * (h1 + p1 - 1) - 4 * lo1) by ring. 
      by apply IntOrder.mulr_ge0 => /#.
    rewrite -!fromintD -!fromintM le_fromint -subz_ge0 /=.
    pose i := pos - lo; pose j := hi - pos; pose k := (_ - _)%Int.
    have -> : k = (i - j) ^ 2 + 5 * i + 5 * j by rewrite /k /i /j; ring.
    by have /# := IntOrder.ge0_sqr (i - j).
  by wp; skip => &hr /> *; smt().
qed.

(* -------------------------------------------------------------------- *)
(* Lower bound                                                          *)

(* Harmonic numbers: H m = 1 + 1/2 + ... + 1/m. *)
op H (m : int) : real = BRA.bigi predT (fun i => 1%r / i%r) 1 (m + 1).

(* The expected cost of qselect on a range of size m when the searched
   position is an extremity of the range. *)
op lbq (m : int) : real = 2%r * m%r - 2%r * H m.

lemma H_S m : 0 <= m => H (m + 1) = H m + 1%r / (m + 1)%r.
proof. by move=> hm; rewrite /H BRA.big_int_recr 1:/#. qed.

lemma lbq_S m : 0 <= m => lbq (m + 1) = lbq m + 2%r - 2%r / (m + 1)%r.
proof. by move=> hm; rewrite /lbq H_S // fromintD; ring. qed.

lemma lbq0 : lbq 0 = 0%r.
proof. by rewrite /lbq /H BRA.big_geq. qed.

lemma lbq1 : lbq 1 = 0%r.
proof. by rewrite (lbq_S 0) // lbq0. qed.

lemma lbq_mono s t : 0 <= s <= t => lbq s <= lbq t.
proof.
  move=> [hs hst]; have -> : t = s + (t - s) by ring.
  have : 0 <= t - s by smt().
  elim: (t - s) => // n hn hrec.
  rewrite addzA lbq_S 1:/#.
  have : 2%r / (s + n + 1)%r <= 2%r.
  + by apply RealOrder.ler_pdivr_mulr; smt().
  smt().
qed.

lemma lbq_ge0 m : 0 <= m => 0%r <= lbq m.
proof. by move=> hm; rewrite -lbq0 lbq_mono. qed.

(* The step of qselect is exact for the extremal positions:
   m * lbq m = m * (m - 1) + sum_{s=1}^{m-1} lbq s. *)
lemma lbq_sum m : 1 <= m =>
  m%r * lbq m = m%r * (m - 1)%r + BRA.bigi predT lbq 1 m.
proof.
  move=> hm; have -> : m = (m - 1) + 1 by ring.
  have : 0 <= m - 1 by smt().
  elim: (m - 1) => /= [| n hn hrec]; 1: by rewrite lbq1 BRA.big_geq.
  have -> : n + 2 = (n + 1) + 1 by ring.
  rewrite lbq_S 1:/# BRA.big_int_recr 1:/#.
  have -> : BRA.bigi predT lbq 1 (n + 1) = (n + 1)%r * lbq (n + 1) - (n + 1)%r * n%r.
  + by rewrite hrec; ring.
  by rewrite !fromintD; field; smt().
qed.

(* Since lbq is increasing, the sizes n + d, ..., 1 + d dominate n, ..., 1. *)
lemma lbq_sum_rev n d : 0 <= n => 0 <= d =>
  BRA.bigi predT lbq 1 (n + 1) <= BRA.bigi predT (fun i => lbq (n + d - i)) 0 n.
proof.
  move=> + hd; elim: n => [| n hn hrec]; 1: by rewrite !BRA.big_geq.
  rewrite BRA.big_int_recr 1:/# (BRA.big_ltn 0) 1:/# (BRA.big_addn 0 _ 1) /=.
  rewrite RField.addrC; apply RealOrder.ler_add; 1: by apply lbq_mono => /#.
  apply (RealOrder.ler_trans _ _ _ hrec); rewrite RealOrder.lerr_eq.
  by apply BRA.eq_big => // i /= _; congr; ring.
qed.

(* One step of qselect on [lo..hi] searching pos: m = hi - lo + 1 times the
   bound for size m is at most the cost m * (m - 1) of the m partitions plus
   the sum of the bounds for the sizes of the next range. *)
lemma lbq_step lo pos hi : lo <= pos <= hi =>
  (hi - lo + 1)%r * lbq (hi - lo + 1) <=
  (hi - lo + 1)%r * (hi - lo)%r +
  BRA.bigi predT (fun p => lbq (if p = pos then 1 else if p < pos then hi - p else p - lo))
    lo (hi + 1).
proof.
  move=> hpos; rewrite lbq_sum 1:/# /= RealOrder.ler_add2l.
  rewrite (BRA.big_cat_int pos lo) 1,2:/# (BRA.big_ltn pos) 1:/# /= lbq1 /=.
  rewrite (BRA.big_cat_int (pos - lo + 1) 1) 1,2:/#.
  apply RealOrder.ler_add.
  + apply (RealOrder.ler_trans _ _ _ (lbq_sum_rev (pos - lo) (hi - pos) _ _)); 1,2: smt().
    have := BRA.big_addn 0 pos lo predT; rewrite add0z => ->.
    have -> : (fun (i : int) => predT (i + lo)) = predT<:int> by done.
    by rewrite RealOrder.lerr_eq; apply BRA.eq_big_int => i /= hi_; smt().
  have := BRA.big_addn (pos - lo + 1) (hi + 1) lo predT.
  have -> : pos - lo + 1 + lo = pos + 1 by ring.
  move=> ->; have -> : (fun (i : int) => predT (i + lo)) = predT<:int> by done.
  have -> : hi + 1 - lo = hi - lo + 1 by ring.
  by rewrite RealOrder.lerr_eq; apply BRA.eq_big_int => i /= hi_; smt().
qed.

lemma eh_p_partition_le (f : int -> int -> xreal) (t_ : elem array) (c_ lo_ hi_ : int) :
  ehoare [<=] [QS.p_partition :
  {c = c_ /\ lo = lo_ /\ hi = hi_ /\ t = t_ /\ uniq_on t lo hi /\ 0 <= lo_ <= hi_ < size t |
   Ep [lo .. hi] (fun p => f p (c + (hi - lo)*clt))} ==>
  {c = c_ + (hi_ - lo_) * clt /\ lo_ <= res.`2 <= hi_ /\ uniq_on res.`1 lo_ hi_ /\ size res.`1 = size t_ |
   f res.`2 c}].
proof.
  conseq (p_partitionE t_ lo_ hi_)
    (_: {c = c_ /\ lo = lo_ /\ hi = hi_ | Ep [lo .. hi] (fun p => f p (c + (hi - lo)*clt))} ==>
        {c = c_ + (hi_ - lo_) * clt | f res c}) => />.
  + by move=> &1 *; exists c_ (lo, hi){1}.
  proc; auto.
qed.

(* The expected cost of qselect on an array of size n is at least
   2n - 2 H n, whatever the searched position; the bound is reached when
   the position is 0 or n - 1. *)
lemma eh_qselect_lower : ehoare [<=] [QS.qselect :
  {0 <= pos < size t /\ uniq_on t 0 (size t - 1) | (2%r * (size t)%r - 2%r * H (size t))%xr}
  ==> {true | c%xr}].
proof.
  proc.
  while /variant ((0 <= lo <= pos <= hi < size t /\ uniq_on t lo hi /\ 0 <= c),
                  c%xr + (lbq (hi - lo + 1))%xr) (hi - lo).
  + by move=> &hr [#] 3? hhi *; rewrite (: hi{hr} - lo{hr} + 1 = 1) 1:/# lbq1.
  + move=> k; wp; exlim t, c, lo, hi, pos => t_ c_ lo_ hi_ pos_.
    call (eh_p_partition_le (fun p (c : int) =>
            c%xr + (lbq (if p = pos_ then 1 else if p < pos_ then hi_ - p else p - lo_))%xr)
          t_ c_ lo_ hi_).
    skip => &hr /= [#] 5!-> [#] hlo hpos hhi hsz huniq hc hlt hk; split.
    + split; 1: smt().
      move=> _ [t0 p0] c0 /= [#] -> hp0lo hp0hi hu hsz'; split; 1: smt(uniq_on_sub).
      case: (p0 = pos{hr}) => //= _; case: (p0 < pos{hr}) => _.
      + by rewrite (: hi{hr} - (p0 + 1) + 1 = hi{hr} - p0) 1:/#.
      by rewrite (: p0 - 1 - lo{hr} + 1 = p0 - lo{hr}) 1:/#.
    move: (pos{hr}) (lo{hr}) (hi{hr}) (c{hr}) hlo hpos hhi hc
      => {&hr hk hsz huniq hlt lo_ hi_ pos_ t_ c_} pos lo hi c hlo hpos hhi hc.
    rewrite Ep_dinterval_le 1:/# /clt /=.
    rewrite (BXA.eq_big_int _ _ _ (fun p => ((c + (hi - lo))%r +
               lbq (if p = pos then 1 else if p < pos then hi - p else p - lo))%xr)).
    + by move=> i hi_ /=; rewrite (of_realD (c + (hi - lo))%r) 2:lbq_ge0 /#.
    rewrite bigiXR /=.
    + by move=> i hi_; apply RealOrder.addr_ge0; [smt() | apply lbq_ge0 => /#].
    rewrite BRA.big_split sumri_const 1:/# /=.
    have hs := lbq_step lo pos hi _; 1: smt().
    have -> : hi + 1 - lo = hi - lo + 1 by ring.
    rewrite !to_pos_pos.
    + smt().
    + by apply lbq_ge0 => /#.
    + apply RealOrder.addr_ge0; 1: smt().
      by apply StdBigop.Bigreal.sumr_ge0_seq => i /mem_range hi_ _ /=; apply lbq_ge0 => /#.
    + smt().
    rewrite RealOrder.ler_pdivl_mulr 1:/#.
    move: hs; pose S := BRA.bigi _ _ _ _; pose m := (hi - lo + 1)%r.
    by rewrite fromintD; smt().
  + by move=> &hr /#.
  by wp; skip => &hr /> *; smt().
qed.
