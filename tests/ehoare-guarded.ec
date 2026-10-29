(* Regression tests for guarded / comparison-directed eHoare judgments:
     ehoare [<=] | [=] | [>=]  [ f : {P | f} ==> {Q | g} ]
   - the guard braces  {P | f}  store an explicit boolean guard P alongside
     the xreal value f (default guard is [true]);
   - the leading direction marker relates PRE to POST, read left to right:
     [pre cmp post].  So [>=] means  pre >= E[post]  (an upper bound on the
     expected value) and [<=] means  pre <= E[post]  (a lower bound).
   - the DEFAULT (no marker) is the historical upper bound  E[post] <= pre,
     i.e.  pre >= post = [>=]. *)
require import AllCore Int Real Xreal Distr DBool StdOrder.
import RealOrder.

(* GEO example for upper bound*)
abbrev (`|`) b (i : int) = b `|` i%xr.

module Ex = {
  var ct : int

  proc rw (n: int) : int = {
    var b : bool;
    ct <- 0;

    while(0 < n){
      b <$ {0,1};
      if (b) { n <- n - 1; }
      ct <- ct + 1;
    }

    return ct;
  }
}.

(* { 0 <= n | 2 * n } rw { res } *)
ehoare rw_time : Ex.rw :
  (0 <= n) `|` (2 * n)%xr ==> res%xr.
proof.
  proc.
  while ((0 <= n /\ 0 <= Ex.ct) `|` (2 * n + Ex.ct)).
  (* ct <=  !(n < 0) | I *)
  + by smt().
  (* { 0 < n | I } Loop-Body { I } *)
  + auto => &hr />.
    (*Only line that was needed to be added to the proof *)
    move=> hn.
    apply xle_cxr_r => /> *.
    rewrite Ep_dbool /=.
    have -> /=: 0 <= n{hr} - 1 by smt().
    have -> /=: 0 <= Ex.ct{hr} + 1 by smt().
    by smt().
  by auto.
  qed.
(* proof.
  proc.
  while ((0 <= n /\ 0 <= Ex.ct) `|` (2 * n + Ex.ct)).
  (* ct <=  !(n < 0) | I *)
  (* + by smt(). *)
  + move=> &hr hstop.
  apply xle_cxr_r.
  move=> [hn0 hct].
  have hnle : n{hr} <= 0.
  - apply/lezNgt.
    exact hstop.
  have hnzero : n{hr} = 0 by
    rewrite eqz_leq hnle hn0.
  by rewrite hnzero.
  (* { 0 < n | I } Loop-Body { I } *)
  + auto => &hr /= hn.
    apply xle_cxr_r.
    move=> [hn0 hct0].
    rewrite Ep_dbool /=.
    have -> /=: 0 <= n{hr} - 1 by smt().
    have -> /= : 0 <= n{hr} by exact hn0.
    have -> /=: 0 <= Ex.ct{hr} + 1 by smt().
    by smt().
  by auto. *)

(* -------------------------------------------------------------------- *)
(* Upper-bound while with a GUARDED invariant:  [while (P, E)].

   [P] stays in the boolean guard instead of being folded into the value
   with [`|`], so both [P] and the loop condition reach the body premise as
   plain hypotheses and the proof needs no [xle_cxr_r] (compare [rw_time]
   above, which states the same theorem in the folded style).

   This is ergonomics, not extra power: for the upper bound [cxrA] gives
   [b1 `|` (b2 `|` f) = (b1 /\ b2) `|` f], so [while (P, E)] is exactly
   [while (P `|` E)].  The core rule already read the guard from the goal;
   only the wrapper used to hard-code [true]. *)
ehoare rw_time_guarded : Ex.rw :
  {0 <= n | (2 * n)%xr} ==> res%xr.
proof.
  proc.
  while ((0 <= n /\ 0 <= Ex.ct), (2 * n + Ex.ct)%xr).
  (* exit:  P /\ !(0 < n)  =>  E <= res *)
  + by smt().
  (* body:  {P /\ 0 < n | E} c {P | E}, guard and value split *)
  + auto => &hr /> hn hct hpos; split.
    + by move=> b0 _; smt().
    by rewrite Ep_dbool /=; smt().
  (* prefix: {0 <= n | 2 * n}  Ex.ct <- 0  {P | E} *)
  + by auto.
qed.

(* A bare value invariant keeps its implicit [true] guard, so [while E]
   produces exactly the subgoals it produced before the guarded form was
   added ([f_and_simpl true (!b)] is syntactically [!b]). *)
module WUp = {
  var b : bool

  proc loop() : unit = {
    while (WUp.b) {
      WUp.b <- false;
    }
  }
}.

lemma t_while_upper_bare :
  ehoare [WUp.loop : 1%xr ==> 1%xr].
proof.
  proc.
  while (1%xr).
  + by auto.
  + by auto.
  by auto.
qed.


module M = {
  proc f(x : int) : int = {
    var y : int;
    y <- x + 1;
    return y;
  }

  proc g() : unit = {}
}.


(* default direction (no marker) = upper bound: E[post] <= pre. *)
lemma t_default :
  ehoare [M.f : (1%xr) ==> (1%xr)].
proof. 
  proc. 
    wp. 
    skip => &hr //.
  qed.


(* explicit boolean guard, default direction *)
lemma t_guard (b : bool) :
  ehoare [M.g : {b | (1%xr)} ==> {b | (1%xr)}].
proof.
  proc.
  skip => &hr //.
qed.


(* [>=] = explicit upper bound (same as default): pre >= post.
   Genuinely true: with the guard x <= 1 we get res = x+1 <= 2 = pre, so the
   value obligation  res <= 2  and the post guard  res <= 2  both hold.
   This exercises the SEPARATED wp: the guard (res <= 2) and the value (res)
   are pushed back through "y <- x+1" INDEPENDENTLY, with no direction-
   dependent `|`-folding. *)
lemma t_ge :
  ehoare [>=] [M.f : {x <= 1 | 2%xr} ==> {res <= 2 | res%xr}].
proof. 
  proc. 
  wp. 
  skip => &hr /=. 
  move=> hx.

  have htwo : 2 = 1 + 1 by trivial.

  split.
  + rewrite htwo lez_add2r.
  exact hx.

  + rewrite -(@to_pos_pos 2%r) 1://.
    apply le_pos.
    rewrite le_fromint.
    rewrite htwo lez_add2r.
    exact hx.
qed.


(* [<=] = lower bound: pre <= E[post].  Here 1 <= 1. *)
lemma t_le :
  ehoare [<=] [M.f : {true | 1%xr} ==> (1%xr)].
proof. 
  proc. 
    wp. 
    skip => &hr //. 
  qed.


(* [=] = equality: pre = E[post].  True at x = 1 (res = 2).
   The equality direction was previously impossible to even state through wp
   (the `|` operator only had an upper-bound neutral, oo); separating guard
   and value makes it work. *)
lemma t_eq :
  ehoare [=] [M.f : {x = 1 | 2%xr} ==> {res = 2 | res%xr}].
proof.
  proc.
  wp.
  skip => &hr /=.
  move=> hx.
  rewrite hx //.
qed.


(* wp now CROSSES a random sampling: the guard is pushed back as
   [forall x, x \in supp d => Q[x]] and the value as its expectation
   [E_{x~d}[g]].  Here the post guard (res \/ !res) is a tautology, so it holds
   over the whole support of {0,1}. *)
module R = {
  proc h() : bool = {
    var b : bool;
    b <$ {0,1};
    return b;
  }
}.


lemma t_rnd_guard :
  ehoare [R.h : {true | (1%xr)} ==> {res \/ !res | (1%xr)}].
proof.
  proc.
  wp.
  skip => &hr /=.
  rewrite EpC dbool_ll /=.
  move=> b0 _.
  by case b0.
qed.


lemma t_rnd_lower_zero :
  ehoare [<=] [R.h : {true | (1%r / 2%r)%xr} ==> {res \/ !res | res%xr}].
proof.
  proc.
  wp.
  skip => &hr /=.

  split.
  + move=> b0 _.
    by case b0.
  
  + rewrite Ep_dbool //.
qed.


(* -------------------------------------------------------------------- *)
(* Multiplicative-decay LOWER-BOUND while rule:  invoked as
     while <value V> <factor beta>  on a [<=] goal whose post is exactly
     {P /\ !b | E}.  It splits into 5 premises (body-lower, E<=V, mass-decay
     [>=], 0<=beta<1, V finite).  Here E = 1, V = [b], beta = 0: the loop runs
     at most once, so decay by 0 is trivially valid. *)
module W = {
  var b : bool

  proc loop() : unit = {
    while (b) {
      b <- false;
    }
  }
}.

lemma t_while_mult :
  ehoare [<=] [W.loop : {true | 1%xr} ==> {!W.b | 1%xr}].
proof.
  proc.
  while (W.b%xr) 0%r.

  (* Goal 1: body preserves the lower invariant *)
  + wp.
    skip => &hr /=.
    by trivial.

  (* Goal 2: E <= V under the loop guard *)
  + move=> &hr hb /=.
    rewrite hb /=.
    by trivial.

  (* Goal 3: multiplicative decay *)
  + wp.
    skip => &hr.
    by trivial.

  (* Goal 4: 0 <= beta < 1 *)
  + move=> &hr /=.
    by trivial.

  (* Goal 5: V is finite *)
  + move=> &hr _ /=.
    by trivial.
qed.


(* Same loop, but the post is NOT in the exact canonical shape {P /\ !b | E}:
   here {W.b = false | 1}.  The user-facing wrapper reads the invariant {P | E}
   from the pre, builds the canonical exit post, and bridges it to the stated
   post with `conseq'.  So the FIRST subgoal is that post bridge, then the five
   decay premises (6 subgoals total). *)
lemma t_while_mult_noncanon :
  ehoare [<=] [W.loop : {true | 1%xr} ==> {W.b = false | 1%xr}].
proof.
  proc.
  while (W.b%xr) 0%r.

  (* Goal 1: post bridge *)
  + move=> &hr.
    by case (W.b{hr}).

  (* Goal 2: body preserves the invariant *)
  + wp.
    skip => &hr /=.
    by trivial.

  (* Goal 3: E <= V *)
  + move=> &hr hb /=.
    rewrite hb /=.
    by trivial.

  (* Goal 4: multiplicative decay *)
  + wp.
    skip => &hr /=.
    by trivial.

  (* Goal 5: 0 <= beta < 1 *)
  + move=> &hr /=.
    by trivial.

  (* Goal 6: V is finite *)
  + move=> &hr _ /=.
    by trivial.
qed.


(* Non-zero constant factor beta = 1/2.  The decay premise (g3) uses the exact
   scalar product  beta ** V  from the notes (realp ** xreal, with 0 ** oo = 0);
   a non-zero beta exercises its  else c%xr * x  branch, whereas beta = 0 above
   takes the  0 ** _ = 0  branch. *)
lemma t_while_mult_beta_half :
  ehoare [<=] [W.loop : {true | 1%xr} ==> {!W.b | 1%xr}].
proof.
  proc.
  while (W.b%xr) (1%r / 2%r).

  (* Goal 1: body preserves the invariant *)
  + wp.
    skip => &hr /=.
    by trivial.

  (* Goal 2: E <= V *)
  + move=> &hr hb /=.
    rewrite hb /=.
    by trivial.

  (* Goal 3: multiplicative decay *)
  + wp.
    skip => &hr /=.
    move=> hb.
    rewrite hb /=.
    rewrite invr_ge0 /=.
    by trivial.

  (* Goal 4: 0 <= beta < 1 *)
  + move=> &hr /=.
    split.

    - rewrite invr_ge0 /=.
      by trivial.

    - rewrite invr_lt1 1,2:// /=.
      by trivial.

  (* Goal 5: V is finite *)
  + move=> &hr _ /=.
    by trivial.
qed.


(* Full sequence wrapper.  The first argument is the guarded intermediate
   loop invariant (P,E); the wrapper separates the initialization prefix,
   applies While-Mult to the final loop, and leaves the prefix as the last
   subgoal. *)
module WPrefix = {
  var b : bool

  proc loop() : unit = {
    b <- true;
    while (b) {
      b <- false;
    }
  }
}.


lemma t_while_mult_prefix :
  ehoare [<=] [WPrefix.loop : {true | 1%xr} ==> {!WPrefix.b | 1%xr}].
proof.
  proc.
  while (true, 1%xr) (WPrefix.b%xr) 0%r.
  + wp. skip => &hr /=. smt(xle_cxr_l xle_cxr_r). (* g1 *)
  + move=> &hr /=. smt(xle_cxr_l xle_cxr_r).      (* g2 *)
  + wp. skip => &hr /=. smt(xle_cxr_l xle_cxr_r). (* g3 *)
  + move=> &hr /=. smt().                          (* g4 *)
  + move=> &hr /=. smt().                          (* g5 *)
  + wp. skip => &hr /=. smt(xle_cxr_l xle_cxr_r). (* prefix *)
qed.

(* Prefix + suffix workflow.  As for the historical upper-bound while tactic,
   [wp] first consumes the code after the loop.  The three-argument While-Mult
   wrapper then separates the initialization prefix from the final loop. *)
module WPrefixSuffix = {
  var b : bool

  proc loop() : unit = {
    b <- true;
    while (b) {
      b <- false;
    }
    b <- false;
  }
}.

lemma t_while_mult_prefix_suffix : 
  ehoare [<=] [WPrefix.loop : {true | 1%xr} ==> {!WPrefix.b | 1%xr}].
proof.
  proc.
  while (true, 1%xr) (WPrefix.b%xr) 0%r.

  (* Goal 1: body preserves the invariant *)
  + wp.
    skip => &hr /=.
    by trivial.

  (* Goal 2: E <= V *)
  + move=> &hr hb /=.
    rewrite hb /=.
    by trivial.

  (* Goal 3: multiplicative decay *)
  + wp.
    skip => &hr /=.
    by trivial.

  (* Goal 4: 0 <= beta < 1 *)
  + move=> &hr /=.
    by trivial.

  (* Goal 5: V is finite *)
  + move=> &hr _ /=.
    by trivial.

  (* Goal 6: initialization prefix *)
  + wp.
    skip => &hr /=.
    by trivial.
qed.

(* The two while directions are kept disjoint by design.  These are machine-
   checked with [fail t] (succeeds iff the inner tactic fails). *)

(* On a [<=] goal the direction-primary dispatcher routes to the decay rule, so
   the single-argument STANDARD form [while E] is refused (it wants [while V
   beta]).  This checks the dispatcher's direction split; the standard rule's
   own upper-bound guard is a second line of defense behind it. *)
lemma t_while_std_rejects_lower :
  ehoare [<=] [W.loop : {true | 1%xr} ==> {!W.b | 1%xr}].
proof. proc. fail while (W.b%xr). abort.

(* The DECAY rule refuses a factor that reads a body-written variable (unsound
   -- beta could drift towards 1 across iterations).  This exercises the core's
   independence guard directly, so deleting that guard turns the suite red. *)
lemma t_while_mult_rejects_written_beta :
  ehoare [<=] [W.loop : {true | 1%xr} ==> {!W.b | 1%xr}].
proof. proc. fail while (W.b%xr) (b2r W.b). abort.


(* Deterministic countdown, proved without SMT.  The guarded expectation
   invariant is {x >= 0 /\ c >= 0 | c+x}.  It is preserved exactly because
   the body transfers one unit from x to c.  For lower-bound soundness, the
   decay witness V = 2^x (c+x) contracts by beta = 1/2 at every iteration. *)
module WCountdown = {
  var x : int
  var c : int

  proc loop() : unit = {
    while (0 < x) {
      x <- x - 1;
      c <- c + 1;
    }
  }
}.

lemma t_while_mult_countdown :
  ehoare [<=] [WCountdown.loop :
    {0 <= WCountdown.x /\ 0 <= WCountdown.c |
       (WCountdown.c + WCountdown.x)%xr}
    ==>
    {WCountdown.x = 0 /\ 0 <= WCountdown.c |
       WCountdown.c%xr}].
proof.
  proc.
  while
    (((2%r ^ WCountdown.x) *
       (WCountdown.c + WCountdown.x)%r)%xr)
    (1%r / 2%r).

  (* Post bridge: P /\ !(0 < x) implies x = 0, and then c+x = c. *)
  + move=> &hr [[hx hc] hstop].
    have hxle : WCountdown.x{hr} <= 0 by apply/lezNgt.
    have hx0 : WCountdown.x{hr} = 0 by
      rewrite eqz_leq hxle hx.
    by rewrite hx0 /=.

  (* G1: the body preserves both P and E = c+x. *)
  + wp.
    skip => &hr /=.
    move=> [[hx hc] hxpos].
    split.
    + split.
      + rewrite subz_ge0.
        by move: hxpos; rewrite ltzE add0z.
      + apply: (lez_trans WCountdown.c{hr}); first exact hc.
        by rewrite lez_addl lez01.
    + by rewrite -addzA (addzC 1) subrK.

  (* G2: on active states, c+x <= 2^x(c+x). *)
  + move=> &hr [[hx hc] _].
    apply/xle_rle.
    have hsum : 0%r <= (WCountdown.c{hr} + WCountdown.x{hr})%r by
      rewrite le_fromint; apply/addz_ge0.
    split; first exact hsum.
    move=> _.
    apply/RealOrder.ler_pemull; first exact hsum.
    apply/RealOrder.exprn_ege1; first exact hx.
    by rewrite le_fromint.

  (* G3: wp(body,V) = V/2 = beta ** V. *)
  + wp.
    skip => &hr /=.
    move=> [[hx hc] hxpos].
    rewrite -addzA (addzC 1) subrK.
    have hpow : 2%r ^ WCountdown.x{hr} =
        2%r * (2%r ^ (WCountdown.x{hr} - 1)) by
      rewrite RField.expr_pred 1:hxpos.
    rewrite hpow.
    have hsum : 0%r <= (WCountdown.c{hr} + WCountdown.x{hr})%r by
      rewrite le_fromint; apply/addz_ge0.
    have hpow0 : 0%r <= 2%r ^ (WCountdown.x{hr} - 1) by
      apply/RealOrder.expr_ge0; rewrite le_fromint.
    have hprod : 0%r <=
        2%r ^ (WCountdown.x{hr} - 1) *
        (WCountdown.c{hr} + WCountdown.x{hr})%r by
      apply/RealOrder.mulr_ge0; [exact hpow0 | exact hsum].
    have hscaled : 0%r <=
        2%r * ((2%r ^ (WCountdown.x{hr} - 1)) *
        (WCountdown.c{hr} + WCountdown.x{hr})%r) by
      apply/RealOrder.mulr_ge0.
    rewrite !to_pos_pos.
    + exact hprod.
    + by rewrite -RField.mulrA.
    + apply RealOrder.lerr_eq.
      have hnum :
          2%r * (2%r ^ (WCountdown.x{hr} - 1)) *
            (WCountdown.c{hr} + WCountdown.x{hr})%r =
          2%r * ((2%r ^ (WCountdown.x{hr} - 1)) *
            (WCountdown.c{hr} + WCountdown.x{hr})%r) by
        rewrite -RField.mulrA.
      rewrite hnum.
      rewrite (RField.mulrC 2%r) RField.mulrK //.

  (* G4: beta = 1/2 belongs to [0,1). *)
  + move=> _.
    have htwo : 0%r < 2%r by
      rewrite (_ : 2%r = 1%r + 1%r) 1://.
    have hone_two : 1%r < 2%r by
      rewrite (_ : 2%r = 1%r + 1%r) 1://.
    split.
    + apply/RealOrder.divr_ge0.
      + exact RealOrder.ler01.
      + exact/RealOrder.ltrW/htwo.
    + rewrite RealOrder.ltr_pdivr_mulr 1:htwo RField.mul1r.
      exact hone_two.

  (* G5: V is a real-valued xreal, hence finite. *)
  + by move=> &hr _ /=.
qed.


module FDR6 = {
  var c : int
  var v : int
  proc sample() : int = {
    var b : bool;
    c <- 0;
    v <- 1;
    while (v < 6) {
      b <$ {0,1};
      c <- 2 * c + b2i b;
      v <- 2 * v;
      if (6 <= c) {
        c <- c - 6;
        v <- v - 6;
      }
    }
    return c;
  }
}.

(* -------------------------------------------------------------------- *)
(* Jensen-based consequence transform:  [conseq / fc <pterm>].
   The rule is now direction-generic; [fc] is applied to the VALUE
   component only and the guards are threaded through untouched.

     [>=]   concave_incr fc,  fc(pre') <= pre,  post <= fc(post')
     [<=]   convex_incr fc,   pre <= fc(pre'),  fc(post') <= post
     [=]    rejected -- Jensen holds in one direction only.

   [fc = fun y => y * 2] is both concave and convex (it is linear), so the
   same witness exercises both directions and the tests differ only in the
   ORIENTATION of the two value obligations. *)
module TC = {
  var x : int

  proc f() : unit = {
    TC.x <- TC.x + 1;
  }
}.

(* upper bound: solved in the [concave_incr] base *)
lemma t_transform_inner_ge :
  ehoare [>=] [TC.f : {true | 1%xr} ==> {true | 1%xr}].
proof.
  proc.
    wp.
    skip => /=.
    trivial.
  qed.

lemma t_transform_ge :
  ehoare [>=] [TC.f : {true | 2%xr} ==> {true | 2%xr}].
proof.
  conseq / (fun (y : xreal) => y * 2%xr) t_transform_inner_ge.
  (* g1 : fc(pre') <= pre *)
  + by move=> _ /=.
  (* g2 : post <= fc(post') *)
  by move=> _ /=.
qed.

(* lower bound with non-trivial guards: [fc] never touches them, so the
   inner judgment keeps the guards of the goal. *)
lemma t_transform_inner_le_guarded :
  ehoare [<=] [TC.f : {0 <= TC.x | 1%xr} ==> {0 < TC.x | 1%xr}].
proof. proc; wp; skip => /=; smt(). qed.

lemma t_transform_le_guarded :
  ehoare [<=] [TC.f : {0 <= TC.x | 2%xr} ==> {0 < TC.x | 2%xr}].
proof.
  conseq / (fun (y : xreal) => y * 2%xr) t_transform_inner_le_guarded.
  + by move=> _ /=.
  by move=> _ /=.
qed.

(* equality is rejected, on both the F and the S judgment. *)
lemma t_transform_inner_eq :
  ehoare [=] [TC.f : {true | 1%xr} ==> {true | 1%xr}].
proof. proc; wp; skip => /=; trivial. qed.

lemma t_transform_rejects_eq_F :
  ehoare [=] [TC.f : {true | 2%xr} ==> {true | 2%xr}].
proof. fail conseq / (fun (y : xreal) => y * 2%xr) t_transform_inner_eq. abort.

lemma t_transform_rejects_eq_S :
  ehoare [=] [TC.f : {true | 2%xr} ==> {true | 2%xr}].
proof. proc. fail conseq / (fun (y : xreal) => y * 2%xr) t_transform_inner_eq. abort.

(* A strictly convex witness. [fun y => y * y] is not reachable from the [convex_incr]
   hint base, which only derives affine combinations.  The side-condition
   therefore survives the automatic solver and has to be discharged by hand --
   which is exactly what makes it visible that the emitted obligation is
   [convex_incr] and not [concave_incr]. *)
lemma sq_convex_incr : convex_incr (fun (y : xreal) => y * y).
proof.
  split.
  + rewrite /convex /= => t ht x y; case: x => //=; case: y => //= /#.
  split.
  + by apply (increasingM (fun (y:xreal) => y) (fun (y:xreal) => y));
       apply increasing_id.
  split; 1: by [].
  by move=> h; have := h 1%rp => /=; smt().
qed.

lemma t_transform_inner_le2 :
  ehoare [<=] [TC.f : {true | 2%xr} ==> {true | 2%xr}].
proof. proc; wp; skip => /=; trivial. qed.

(* fc(2) = 4, so g1 is the strict [3 <= 4]: the transform really moves the
   bound instead of being an identity step. *)
lemma t_transform_le_strictly_convex :
  ehoare [<=] [TC.f : {true | 3%xr} ==> {true | 4%xr}].
proof.
  conseq / (fun (y : xreal) => y * y) t_transform_inner_le2.
  (* g0 : convex_incr fc -- left open by the automatic solver *)
  + by apply sq_convex_incr.
  (* g1 : pre <= fc(pre') *)
  + by move=> _; smt(xler_mul).
  (* g2 : fc(post') <= post *)
  by move=> _; smt(xler_mul).
qed.

(* Statement-level lower bound: with the goal in ehoareS shape the cut is an
   ehoareS too, so this exercises [t_ehoareS_transform] (the lemmas above go
   through [t_ehoareF_transform]). *)
lemma t_transform_le_stmt :
  ehoare [<=] [TC.f : {true | 2%xr} ==> {true | 2%xr}].
proof.
  proc.
  conseq / (fun (y : xreal) => y * 2%xr) (: 1%xr ==> 1%xr).
  (* g1 : pre <= fc(pre') *)
  + by move=> _ /=.
  (* g2 : fc(post') <= post *)
  + by move=> _ /=.
  (* g3 : the inner STATEMENT judgment *)
  by wp; skip => /=; trivial.
qed.

(* -------------------------------------------------------------------- *)
(* Two independent counterexamples for the extra lower-bound conditions. *)

(* a non-zero constant is rejected by [f 0 = 0] -- this is the conjunct
   that fixes the sub-distribution unsoundness. *)
lemma t_cst_missing_zero :
  (convex (fun (_ : xreal) => 1%xr) /\ increasing (fun (_ : xreal) => 1%xr)) /\
  cont_at_oo (fun (_ : xreal) => 1%xr) /\
  ! convex_incr (fun (_ : xreal) => 1%xr).
proof.
  split; 1: by split; [apply convex_cst | apply increasing_cst].
  split; 1: by rewrite /cont_at_oo; smt().
  rewrite /convex_incr; apply/negP => -[_ [_ [h _]]].
  by move: h; smt().
qed.

(* With zero output mass, Jensen would incorrectly require 1 <= 0. *)
lemma t_dnull_breaks_jensen :
  ! (1%xr <= Ep dnull<:int> (fun (_ : int) => 1%xr)).
proof. by rewrite Ep_dnull. qed.

(* [fun y => y * 0%xr] is convex, increasing and maps 0 to 0, so ONLY
   [cont_at_oo] rejects it.  Checking the conjunct directly is what would
   catch a [cont_at_oo] that is stated too weakly. *)
lemma t_bad_missing_oo :
  (convex (fun (y : xreal) => y * 0%xr) /\
   increasing (fun (y : xreal) => y * 0%xr)) /\
  0%xr * 0%xr = 0%xr /\
  ! cont_at_oo (fun (y : xreal) => y * 0%xr).
proof.
  split.
  + split; 1: by apply convexMr; apply convex_id.
    by apply (increasingM (fun (y : xreal) => y) (fun (_ : xreal) => 0%xr));
       [apply increasing_id | apply increasing_cst].
  split; 1: by [].
  rewrite /cont_at_oo negb_imply; split.
  + smt(mulm0).
  by [].
qed.

(* This is a failure of Jensen itself, not merely of the side-condition.
   A concrete mathematical witness is Pr[n] = 1/((n+1)(n+2)) on n >= 0,
   with g(n) = n+1: its total mass is 1, but E[g] is the divergent
   harmonic tail.  The distribution's divergence is a hypothesis here;
   constructing that countable distribution in EasyCrypt is not claimed. *)
lemma t_bad_jensen_on_divergent (d : int distr) (g : int -> realp) :
  Ep d (fun n => (g n)%xr) = oo =>
  ! ((Ep d (fun n => (g n)%xr)) * 0%xr <=
      Ep d (fun n => (g n)%xr * 0%xr)).
proof.
  move=> hdiv.
  have hz : Ep d (fun n => (g n)%xr * 0%xr) = 0%xr.
  + rewrite (eq_Ep d (fun n => (g n)%xr * 0%xr) (fun _ => 0%xr)) //.
    by rewrite EpC.
  by rewrite hdiv hz /=.
qed.

(* -------------------------------------------------------------------- *)
(* eHoare + equiv + eHoare consequence ([t_ehoareF_conseq_equiv]).

     P1 m1 => exists m2. Rpre m1 m2 /\ P2 m2 /\ f1 m1 <cmp> f2 m2
     Rpost m1 m2 => Q2 m2 => Q1 m1 /\ g2 m2 <cmp> g1 m1

   The inner judgment used to be rebuilt by wrapping an already-tupled side
   again, producing {true | (true, 1%xr)}; guards were ignored and the
   comparison was hard-coded to [<=].  The direction tests below use STRICT
   inequalities, so a hard-coded orientation cannot pass them. *)
module EQ1 = { var x : int  proc f() : unit = { EQ1.x <- EQ1.x + 1; } }.
module EQ2 = { var y : int  proc g() : unit = { EQ2.y <- EQ2.y + 1; } }.

equiv t_conseq_equiv_eq12 : EQ1.f ~ EQ2.g : EQ1.x{1} = EQ2.y{2} ==> EQ1.x{1} = EQ2.y{2}.
proof. proc; auto. qed.

(* reproduction: cut form, previously {true | (true, 1%xr)} *)
lemma t_conseq_equiv_repro : ehoare [EQ1.f : {true | 1%xr} ==> {true | 1%xr}].
proof.
  conseq t_conseq_equiv_eq12 (_: 1%xr ==> 1%xr).
  + by move=> &1 _; exists EQ1.x{1}.
  + by move=> &1 &2.
  by proc; auto.
qed.

(* [>=], strict: pre f2=1 <= f1=2, post g1=0 <= g2=1 *)
lemma t_conseq_equiv_inner_ge : ehoare [>=] [EQ2.g : {true | 1%xr} ==> {true | 1%xr}].
proof. by proc; auto. qed.

lemma t_conseq_equiv_ge : ehoare [>=] [EQ1.f : {true | 2%xr} ==> {true | 0%xr}].
proof.
  conseq t_conseq_equiv_eq12 t_conseq_equiv_inner_ge.
  + by move=> &1 _; exists EQ1.x{1} => /=; smt().
  by move=> &1 &2 _ _ /=; smt().
qed.

(* [<=], strict: pre f1=1 <= f2=2, post g2=2 <= g1=3 *)
lemma t_conseq_equiv_inner_le : ehoare [<=] [EQ2.g : {true | 2%xr} ==> {true | 2%xr}].
proof. by proc; auto. qed.

lemma t_conseq_equiv_le : ehoare [<=] [EQ1.f : {true | 1%xr} ==> {true | 3%xr}].
proof.
  conseq t_conseq_equiv_eq12 t_conseq_equiv_inner_le.
  + by move=> &1 _; exists EQ1.x{1} => /=; smt().
  by move=> &1 &2 _ _ /=; smt().
qed.

(* [=] *)
lemma t_conseq_equiv_inner_eq : ehoare [=] [EQ2.g : {true | 1%xr} ==> {true | 1%xr}].
proof. by proc; auto. qed.

lemma t_conseq_equiv_eq : ehoare [=] [EQ1.f : {true | 1%xr} ==> {true | 1%xr}].
proof.
  conseq t_conseq_equiv_eq12 t_conseq_equiv_inner_eq.
  + by move=> &1 _; exists EQ1.x{1}.
  by move=> &1 &2.
qed.

(* non-trivial guards in BOTH programs, state-dependent values *)
lemma t_conseq_equiv_inner_guarded :
  ehoare [EQ2.g : {0 <= EQ2.y | (EQ2.y + 1)%xr} ==> {0 < EQ2.y | EQ2.y%xr}].
proof. by proc; auto => /#. qed.

lemma t_conseq_equiv_guarded :
  ehoare [EQ1.f : {0 <= EQ1.x | (EQ1.x + 1)%xr} ==> {0 < EQ1.x | EQ1.x%xr}].
proof.
  conseq t_conseq_equiv_eq12 t_conseq_equiv_inner_guarded.
  + by move=> &1 h; exists EQ1.x{1}.
  by move=> &1 &2 -> h.
qed.

(* Q1 is really required: an unreachable goal guard must not go through *)
lemma t_conseq_equiv_requires_q1 :
  ehoare [EQ1.f : {0 <= EQ1.x | (EQ1.x + 1)%xr} ==> {false | EQ1.x%xr}].
proof.
  conseq t_conseq_equiv_eq12 t_conseq_equiv_inner_guarded.
  + by move=> &1 h; exists EQ1.x{1}.
  fail smt().
abort.
