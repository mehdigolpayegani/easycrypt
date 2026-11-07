(* Adaptive early stopping does not bias a sample mean.  An experimenter
   draws at most K samples from a distribution d on [0,1] of mean mu, and
   decides adaptively, from the running sum s and the number n of samples
   seen so far, when to stop.  Whatever the stopping strategy, the final
   sum is in expectation mu times the number of samples, E[s - mu n] = 0
   (Wald's identity for bounded stopping times); stated with non-negative
   quantities: E[s + mu (K - n)] = mu K.  The strategy is an abstract
   adversary, handled by the adversary rule with budget n bounded by K. *)
require import AllCore Int Real Xreal Distr StdOrder.
import RealOrder.

op d : real distr.
axiom d_ll : is_lossless d.
axiom d_bnd : forall x, x \in d => 0%r <= x <= 1%r.

op mu : real.
axiom d_mean : Ep d (fun x => x%xr) = mu%xr.
(* follows from d_mean and d_bnd *)
axiom mu_bnd : 0%r <= mu <= 1%r.

op K : int.
axiom K_ge0 : 0 <= K.

module type Stat = { proc look () : unit }.
module type Adv (S : Stat) = { proc play () : unit }.

module O : Stat = {
  var s : real
  var n : int

  proc look () : unit = {
    var x;
    if (n < K) {
      x <$ d;
      s <- s + x;
      n <- n + 1;
    }
  }
}.

module Main (A : Adv) = {
  proc main () : real = {
    O.s <- 0%r; O.n <- 0;
    A(O).play();
    return O.s + mu * (K - O.n)%r;
  }
}.

lemma look_budget (j : int) (v : real) :
  ehoare [=] [O.look :
    {(O.n <= K /\ 0%r <= O.s) /\ O.n = j /\ (O.s + mu * (K - O.n)%r)%xr = v%xr | (O.s + mu * (K - O.n)%r)%xr} ==>
    {(O.n <= K /\ 0%r <= O.s) /\ j <= O.n /\ (j < O.n \/ (O.s + mu * (K - O.n)%r)%xr = v%xr) | (O.s + mu * (K - O.n)%r)%xr}].
proof.
proc; if; last by auto.
auto => &hr /> hn hs hv hlt; split; 1: smt(d_bnd).
rewrite (eq_Ep _ _ ((fun (x : real) => x%xr) +
                    (fun (_ : real) => (O.s{hr} + mu * (K - (O.n{hr} + 1))%r)%xr))).
+ move=> x hx /=; rewrite Rp_to_real_eq /= !to_pos_pos; smt(d_bnd mu_bnd).
rewrite EpD EpC d_ll d_mean /=.
by rewrite Rp_to_real_eq /= !to_pos_pos; smt(mu_bnd).
qed.

lemma wald (A <: Adv{-O}) :
  (forall (S <: Stat{-A}), islossless S.look => islossless A(S).play) =>
  ehoare [=] [Main(A).main : {true | (mu * K%r)%xr} ==> {true | res%xr}].
proof.
move=> A_ll.
proc; wp.
call (: (O.n <= K /\ 0%r <= O.s, (O.s + mu * (K - O.n)%r)%xr) ==>
        (O.n <= K /\ 0%r <= O.s, (O.s + mu * (K - O.n)%r)%xr)).
+ proc (O.n <= K /\ 0%r <= O.s, (O.s + mu * (K - O.n)%r)%xr) O.n K.
  (* each look either is refused or counts in n, and keeps the expected
     value of s + mu (K - n) *)
  + by move=> j v; exact (look_budget j v).
  (* the strategy terminates: it is lossless and so is the oracle *)
  + proc (O.n <= K /\ 0%r <= O.s, 1%xr).
    + by move=> S S_ll; apply (A_ll S).
    by proc; auto => &hr /> hn hs; split; [smt(d_bnd) | rewrite EpC d_ll].
  (* at most K looks, and the invariant is finite *)
  + by move=> &hr /#.
  by move=> &hr _; rewrite /is_real.
by auto => /=; exact K_ge0.
qed.
