========================================================================
Expectation Hoare logic with directed judgments (``ehoare``)
========================================================================

The expectation Hoare logic bounds the expected value of a function of the
final memory of a program. Its judgments carry a *direction*, which says
whether the pre-expectation is an upper bound, a lower bound, or the exact
value of the expected post-expectation, and *guards*, boolean conditions
that play the role of the assertions of Hoare logic.

.. contents::
   :local:

------------------------------------------------------------------------
Judgments
------------------------------------------------------------------------

.. admonition:: Syntax

  ``ehoare [>=] [f : {P | e} ==> {Q | g}]``

  ``ehoare [<=] [f : {P | e} ==> {Q | g}]``

  ``ehoare [=]  [f : {P | e} ==> {Q | g}]``

Here ``P`` and ``Q`` are boolean formulas, the *guards*, and ``e`` and
``g`` are expectations, i.e. formulas of type ``xreal`` (non-negative reals
extended with ``oo``). The judgment ``ehoare [>=] [f : {P | e} ==> {Q | g}]``
states that, from any memory satisfying ``P``, every final memory of ``f``
satisfies ``Q``, and the expected value of ``g`` on the final memories is at
most ``e``. With ``[<=]`` the expected value is at least ``e``, and with
``[=]`` it is exactly ``e``. The direction marker is read from the pre to the
post: ``e >= E[g]``, ``e <= E[g]``, ``e = E[g]``. Without a marker, the
judgment is an upper bound, ``[>=]``. A side written as a bare expectation
``e`` stands for ``{true | e}``.

Judgments on statements, ``ehoare [cmp] [c : {P | e} ==> {Q | g}]``, arise
inside proofs, as for the other program logics.

An exact judgment implies each of the two bounds: a ``[=]`` lemma or
specification can be used by ``conseq``, ``conseq / F``, ``call`` and
``call / F`` on a ``[<=]`` or ``[>=]`` goal, which is then weakened to the
equality before the lemma is applied. Conversely, ``split`` on a ``[=]`` goal
produces the two goals ``[<=]`` and ``[>=]``, which may then be proved by
different rules or with different witnesses.

------------------------------------------------------------------------
Structural tactics
------------------------------------------------------------------------

The tactics ``skip``, ``wp``, ``rnd``, ``seq``, ``if``, ``case``, ``rcond``,
``proc`` (on a concrete procedure), ``exlim`` and ``conseq`` apply to
``ehoare`` goals in every direction. The weakest precondition of a sampling
``x <$ d`` turns the value side into an expected value ``Ep d (fun x => g)``
and the guard side into a universal condition on the support of ``d``.

The ``exfalso`` tactic reads the guard of the pre-condition: a judgment whose
guard is ``false`` holds, and ``exfalso`` reduces any judgment to the proof
that its guard is contradictory.

The consequence rule ``conseq (_: {P' | e'} ==> {Q' | g'})`` produces, in the
direction of the goal, the obligations on the pre (``P => P'`` and ``e cmp e'``)
and on the post (``Q' => Q`` and ``g' cmp g``). By default the post
obligation is stated on the frame of the variables the program does not
write: it only has to hold on the memories the program reaches from ``P``,
where those variables keep their value. ``conseq [-frame]`` disables this.

.. admonition:: Syntax

  ``conseq / F (_: {P' | e'} ==> {Q' | g'})``

The consequence transform applies a function ``F : xreal -> xreal`` to the
value side: it reduces ``{P | e} cmp c {Q | g}`` to ``{P | e'} cmp c {Q | g'}``
with ``F e' <= e`` and ``g <= F g'`` for an upper bound, and the converse
inequalities for a lower bound. By Jensen's inequality the function must be
concave and increasing for ``[>=]``, and convex and increasing for ``[<=]``,
with ``F 0 = 0``; the side condition is discharged automatically for the
functions built from constants, the identity, sums and scalings (hint bases
``concave_incr`` and ``convex_incr``). For an equality both conditions
apply, which leaves the linear functions, and the two value obligations are
equalities.

------------------------------------------------------------------------
Procedure calls
------------------------------------------------------------------------

.. admonition:: Syntax

  ``call (_: {P' | e'} ==> {Q' | g'})`` or ``call lemma``

  ``call / F (_: {P' | e'} ==> {Q' | g'})`` or ``call / F lemma``

The specification must have the direction of the goal. The guard of the
specification is pushed back through the call as in Hoare logic, so the
variables the callee does not write carry their value from the pre to the
post of the call; the value obligation on the post is pushed back with it.
With a function ``F``, the value side goes through the Jensen step described
above: ``F`` concave for ``[>=]``, convex for ``[<=]``, both (hence linear)
for ``[=]``. Guarded sides of a cut may also be written as pairs,
``(P', e') ==> (Q', g')``.

------------------------------------------------------------------------
Loops
------------------------------------------------------------------------

All loop rules work on a goal whose last statement is the loop and whose
post is ``{P /\ !b | E}`` for the loop invariant ``{P | E}``; another post is
bridged by a consequence step, which appears as a first goal. A guarded loop
invariant ``(P, E)`` given as first argument splits an initialisation prefix
from the loop (as ``seq``), and the invariant is otherwise read from the pre
of the goal.

**Upper bounds.** ``while E`` or ``while (P, E)``: the invariant rule of
``eHL`` (Park induction), with the single premise ``{P /\ b | E} >= c {P | E}``.

**Lower bounds and equalities.** The expected value of the post may be lost
by the runs that never terminate, so a lower bound needs a witness that the
expectation carried by the runs still inside the loop vanishes. Every rule
below has the premise ``{P /\ b | E} cmp c {P | E}`` in the direction of the
goal (for an equality, the upper half is Park induction), and ``E`` finite
inside the loop. The rule is named after a slash:

.. admonition:: Syntax

  ``while /variant V``, ``while /variant (P, E) V``

  ``while /decay V beta``, ``while /decay (P, E) V beta``

  ``while /sum r``, ``while /sum (P, E) r``

  ``while /ascent r``, ``while /ascent (P, E) r``

  ``while /bounded C``, ``while /bounded (P, E) C``

  ``while /ast V p d``, ``while /ast (P, E) V p d``

- ``/variant V``, for an integer expression ``V``: every iteration decreases
  ``V``, which is non-negative inside the loop, so the loop runs at most
  ``V`` more times. Premise: ``forall k, {P /\ b /\ V = k | E} cmp c {P /\ V < k | E}``.
  The bare form ``while V`` is the same rule.
- ``/decay V beta``: ``E <= V`` inside the loop, and the expected value of
  ``V`` on the runs staying in the loop decays by the factor ``beta < 1`` at
  each iteration: ``{P /\ b | beta ** V} >= c {true | [b] ** V}``. The bare
  form ``while V beta`` is the same rule.
- ``/sum r`` (summability): ``r`` bounds the sum over the iterations of ``E``
  on the running part, ``{P /\ b | r} >= c {true | [b] ** (r + E)}``.
- ``/ascent r``: ``r`` bounds the expected number of iterations plus the
  expected increases of ``E``,
  ``forall v, {P /\ b /\ E = v | r} >= c {true | [b] ** (r + 1 + monus E v)}``,
  where ``monus`` is the truncated subtraction on ``xreal``. This is the rule
  of Hark, Kaminski, Giesl and Katoen, with the expected increase in place of
  a bounded change.
- ``/bounded C`` (McIver and Morgan): ``E <= C`` under ``P`` for a real
  constant ``C``, and the loop terminates almost surely from ``P``, which is
  left as the goal ``{P | 1} <= while b do c {P /\ !b | 1}``.
- ``/ast V p d`` (McIver, Morgan, Kaminski and Katoen): the value of the
  invariant must be ``1``, and the rule proves almost-sure termination from
  a real variant ``V``, non-negative under ``P`` and positive inside the
  loop, that is a supermartingale,
  ``forall v, {P /\ b /\ V = v | v} >= c {P | V}``, and decreases by ``d v``
  with probability at least ``p v``,
  ``forall v, {P /\ b /\ V = v | 1 - p v} >= c {true | [v - d v < V]}``,
  for ``p : real -> real`` into ``(0, 1]`` and ``d : real -> real`` into
  ``(0, oo)``, both antitone. It applies to loops whose expected duration is
  infinite, such as the symmetric random walk.

The named rules are refused on upper bounds.

------------------------------------------------------------------------
Abstract procedures
------------------------------------------------------------------------

.. admonition:: Syntax

  ``proc (P, e)``, ``proc e``

  ``proc (P, e) q K``

On a goal about an abstract procedure (an adversary) with oracles, the
invariant ``{P | e}`` may only read global variables the procedure cannot
write. For an upper bound, ``proc (P, e)`` asks that every oracle preserve
the invariant, ``{P | e} >= o {P | e}``. For a lower bound with ``e = 1``,
it proves almost-sure termination from the usual losslessness hypothesis
``forall O, islossless O.o => islossless A(O).f`` and the premises
``{P | 1} <= o {P | 1}``. For any other lower bound, and for every equality,
a *budget* is needed: ``proc (P, e) q K`` asks, for every oracle,

  ``forall j v, {P /\ q = j /\ e = v | e} cmp o {P /\ j <= q /\ (j < q \/ e = v) | e}``,

i.e. the oracle may change the value of the invariant only while raising the
budget ``q``, which ``P`` bounds by ``K``, together with the almost-sure
termination of the call, ``{P | 1} <= A(O).f {P | 1}``. The budget reads
globals the procedure cannot write, and ``K`` contains no program variable.
This is an optional stopping argument: the adversary chooses the strategy
and when to stop, but can make at most ``K - q`` effective queries.

------------------------------------------------------------------------
Probabilities
------------------------------------------------------------------------

.. admonition:: Syntax

  ``byehoare``, ``byehoare lemma``, ``byehoare (_: (P, e) ==> (Q, g))``

``byehoare`` turns a bound on a probability into an ``ehoare`` judgment on
the procedure: ``Pr[f(a) @ &m : ev] <= bd`` into an upper bound ``[>=]``,
``bd <= Pr[...]`` into a lower bound ``[<=]``, and ``Pr[...] = bd`` into an
equality ``[=]``. The post-expectation defaults to the indicator of the
event and the pre-expectation to the bound; the remaining obligations are
the pre-condition on the arguments, the comparison of the pre-expectation
with the bound, and, on the final memories satisfying the post-condition,
the comparison of the post-expectation with the indicator of the event.
