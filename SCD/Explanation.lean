/-
# What a determination theory explains and predicts

`Determination.lean` redefined dynamics as a relation among the parts of one
configuration and then registered an open item: the relation has a solution
*space*, and nothing picks a point in it.  Left there it reads as an admission
of impotence.  **It is not, and this file works out why — and what the actual
cost is, which is a different and smaller thing than it looked.**

## I.  Every theory has a solution space

Newtonian mechanics does not pick a point either: its solution space is the space
of trajectories, coordinatised by initial data, and nobody counts that against
it.  General relativity's is the space of solutions of the field equations,
coordinatised by boundary and initial data.  A theory *is* a restriction on
configurations; if it picked one it would not be a theory, it would be a
description of the world with no content beyond that world.

So "it does not pick a point" is not the question.  The question is what the
restriction does, and that has an exact answer.

## II.  Every quantity is a prediction or an input, and never both

Given a theory `S` — a set of admissible configurations — and any quantity
`f`:

* `f` is a **prediction** when it takes the same value on every admissible
  configuration (`Predicted`);
* `f` is an **input** when two admissible configurations disagree about it
  (`Modulus`).

`predicted_or_modulus` and `not_both`: these are exhaustive and exclusive.
**There is no third thing a theory can do with a quantity**, so the ledger of
predictions and inputs is complete by construction rather than by good
housekeeping.  And `value_from_any_solution` says what an explanation is here:
the value of a predicted quantity follows from *membership alone* — that the
world is admissible — with no further ingredient.

The theory's power is then a ratio, not a yes/no: how much falls on the
prediction side, how little on the input side.

## III.  Which is worthless unless the solution space is proper

Two degenerate cases, and both are the classic ways a theory fakes power:

* `vacuous_predicts_everything` — **an inconsistent theory predicts every
  quantity**, vacuously.  So a list of predictions means nothing until the
  solution space is shown nonempty;
* `total_predicts_only_constants` — a theory that admits everything predicts
  only what was constant anyway.

`tightening_predicts_more` shows the tension is real: predictions grow
monotonically as the theory tightens, all the way to the inconsistent theory.
**Predictive power on its own is not a virtue.  It is a virtue only paired with
a witness**, and that pairing is `power_requires_a_witness`.

So the determination relation has to be shown proper, and it is, constructively:

* `separable_is_free` — **every separable configuration is a solution**, where
  separable means each direction's scale depends on its own coordinate alone.
  That is an infinite-dimensional family, so the theory is far from
  inconsistent;
* `coupled_not_free` — and a configuration that is *not* a solution, exhibited in
  a concrete model of A1 (`MvPolynomial (Fin 3) ℝ` with the partial derivatives):
  `σ = (0, 0, x₀x₁)` has `influence = 1 + x₀x₁ ≠ 0`.

Together, `constraint_is_proper`.  And the two lemmas say the same thing twice,
which is the physical content:

> **Force is the failure of separability.**  A configuration is free exactly when
> the directions do not talk to each other; `influence` is the obstruction to
> writing the scale pattern one direction at a time.

The converse fails and the failure is physical, not technical: influences can
cancel without being absent, exactly as forces can.

## IV.  The weight grading is a filter on quantities, not the partition itself

The obvious move here is to say that `Weight.lean`'s grading under `σ ↦ cσ` *is*
the partition of §II — weight zero = prediction, weight one = input.  **That is
an overclaim and this file refuses it.**

`influence_not_homogeneous`: the determination relation is *not graded*.  Its
four terms are one of weight one and three of weight two, so rescaling the
log-scale does not map solutions to solutions and weight-zero functions are not
thereby constant on the solution space.  The grading is a statement about how
formulas are written, not a symmetry of the theory.

What survives, and it is what `Weight.lean` actually claimed — "a cheap test":

> **weight zero is *necessary* for a prediction, not sufficient.**  A weight-one
> quantity has a value only once a labelling of the log-scale is fixed, so it
> cannot be predicted without a unit being supplied; that is what it means to say
> `Δ` (equivalently `G`) *is* the unit
> (`Weight.only_gravity_crosses_the_weight`).

So the grading is a filter that removes candidates cheaply, and §II is the
definition it was approximating.  The framework's actual predictions are those
weight-zero quantities that have in addition been *shown* constant across
solutions, which is what each of the theorems below does individually.  With that
correction the summary still holds:

> **one free magnitude, and everything dimensionless.**

`γ = 1`, the deflection factor `2`, the independent precession coefficient,
`CV² = 1`, `k = 3` given A7, the universality of attraction, the vanishing of
every sector-relative Lorentz-violation coefficient, and the impossibility of
dynamics in two directions — all weight zero, all theorems, none containing a
fitted number.  Against them: `Δ` (equivalently `G`).  `leverage` carries the
count as a ledger, and the theorems named in it are the content.

## V.  What is genuinely lost, stated exactly

Not predictivity.  **The time-asymmetric leverage.**

A hyperbolic dynamics gives *measure once, predict forever*: finite input, an
entire trajectory out.  Determination by the complement is symmetric — it gives
*given part, get the rest*, in no preferred order.  You still get more out than
you put in, but you do not get a future for free, and the difference is not
cosmetic.

It has a sharp consequence, and it is negative:

> **No arrow of time can come from the determination relation.**
> `no_arrow_from_determination`: the determiner of a pair and the influence on it
> are both symmetric under exchanging the pair.  Nothing in the relation
> distinguishes an order.

So the arrow must come from counting, not from dynamics — `Entropy.lean`'s
channel — and it is now a theorem that looking for it in the dynamics is
pointless.  This is the same conclusion `influence_symm` reached as a *virtue*
(the third law is one expression, not two facts); it is the same fact read as a
*cost*.  Both readings are correct and the file records both.

## VI.  Explanation without antecedents: mutual, not circular

If a part is explained by its complement rather than by its past, the obvious
worry is circularity.  It is answered structurally:

* `self_not_in_determiner` — **no part appears in its own determiner.**  The
  influence sum runs over the complement, which excludes the pair.  So no
  quantity is invoked in its own explanation, and concurrent explanation is
  legitimate;
* but `cycle_of_three` — in three directions each pair is determined by exactly
  one direction and the assignment is a bijection: `{0,1} ← 2`, `{0,2} ← 1`,
  `{1,2} ← 0`.  **The structure is irreflexive but not acyclic.**

That is the precise price of relationalism, and it is worth naming rather than
hiding: explanation here is *mutual*.  There is no fundamental layer that
explains the rest without being explained.  A causal theory buys acyclicity by
positing a direction; this framework declines to posit one, and pays by having
its explanations run in a loop.  `determiner_card` says the loop tightens as
`n` grows — each pair is determined by `n − 2` others — and vanishes at `n = 2`,
which is `no_influence_in_two`.

## VII.  So what remains open, correctly identified

"Why this configuration rather than another" is **the initial-value question,
relocated**.  No theory answers its own version of it: Newton does not say why
these initial data, general relativity does not say why this Cauchy surface.
Registering it in §V.l was right, but calling it a special weakness of this
framework was not.

What *is* special here, and is the honest residue: because determination is
symmetric, the data one must supply is not "on a slice at one time" but "on part
of a configuration", and the framework has no theory of which parts suffice.
That is a real gap and it is a *different* one from §V.k's; it is the analogue
of well-posedness for a boundary-value problem, and A7 is the only thing the
framework says about it (`Determination.determination_well_posed`) — a counting
statement, not an existence-and-uniqueness theorem.
-/
import SCD.Determination
import SCD.Weight
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Lie

namespace SCD.Explanation

open SCD ScaleAlgebra Determination

/-! ## I. What a constraint theory predicts

A theory is a restriction on configurations.  Everything in this section is
about an arbitrary such restriction; nothing about scales enters yet, which is
the point — the accounting is forced by what a theory *is*, not by which theory
this is. -/

variable {C : Type*} {V : Type*}

/-- **`f` is predicted by `S`**: it takes the same value on every configuration
the theory admits.

This is the whole of what "the theory predicts `f`" can mean once one stops
asking the theory to pick a configuration. -/
def Predicted (S : C → Prop) (f : C → V) : Prop := ∀ x y, S x → S y → f x = f y

/-- **`f` is an input to `S`**: two admissible configurations disagree about it,
so the theory does not fix it and it must be measured. -/
def Modulus (S : C → Prop) (f : C → V) : Prop := ∃ x y, S x ∧ S y ∧ f x ≠ f y

/-- **Nothing is both.** -/
theorem not_both (S : C → Prop) (f : C → V) : ¬ (Predicted S f ∧ Modulus S f) := by
  rintro ⟨hp, x, y, hx, hy, hne⟩
  exact hne (hp x y hx hy)

/-- **And everything is one or the other.**

Trivial as a proof and not as a statement: it says there is no third thing a
theory can do with a quantity.  Hence the ledger of predictions against inputs
is complete by construction, and a theory cannot hide a quantity in some further
category — "explained but not predicted", say. -/
theorem predicted_or_modulus (S : C → Prop) (f : C → V) :
    Predicted S f ∨ Modulus S f := by
  by_cases h : Predicted S f
  · exact Or.inl h
  · right
    simp only [Predicted, not_forall] at h
    obtain ⟨x, y, hx, hy, hne⟩ := h
    exact ⟨x, y, hx, hy, hne⟩

/-- **What an explanation is here.**

If `f` is predicted and the world is admissible, the value of `f` follows from
*any* solution at all.  There are exactly two ingredients — invariance across
the solution space, and membership — and no third.  In particular there is no
mechanism layer: the explanation of a value is not a story about how it came
about. -/
theorem value_from_any_solution {S : C → Prop} {f : C → V} (h : Predicted S f)
    {x : C} (hx : S x) : ∀ y, S y → f y = f x :=
  fun y hy => h y x hy hx

/-! ### The two ways predictive power is faked -/

/-- **Predictions grow as the theory tightens.**

A stronger theory predicts everything a weaker one does.  Monotone all the way
up — which is why the count alone proves nothing, as the next result shows. -/
theorem tightening_predicts_more {S T : C → Prop} (hST : ∀ x, S x → T x)
    (f : C → V) (h : Predicted T f) : Predicted S f :=
  fun x y hx hy => h x y (hST x hx) (hST y hy)

/-- **An inconsistent theory predicts everything.**

The limit of `tightening_predicts_more`, and the standard way a list of
predictions can be worth nothing.  So no claim about what a theory predicts
means anything until its solution space is shown nonempty. -/
theorem vacuous_predicts_everything {S : C → Prop} (hS : ∀ x, ¬ S x) (f : C → V) :
    Predicted S f :=
  fun x _ hx _ => absurd hx (hS x)

/-- **And a theory that restricts nothing predicts only constants.**

The other degenerate end.  Between the two, a theory's content is how much it
cuts out while still admitting something. -/
theorem total_predicts_only_constants {S : C → Prop} (hS : ∀ x, S x) {f : C → V}
    (h : Predicted S f) : ∀ x y, f x = f y :=
  fun x y => h x y (hS x) (hS y)

/-- **So a prediction is worth stating only alongside a witness.**

The meaningful unit is the *pair*: `f` is constant across the solution space,
**and** the solution space contains something.  Stated as one object because the
two halves are worthless apart — the first is free for an inconsistent theory,
and the second says nothing on its own. -/
theorem power_requires_a_witness {S : C → Prop} {f : C → V}
    (h : Predicted S f) (w : ∃ x, S x) : ∃ x, S x ∧ ∀ y, S y → f y = f x := by
  obtain ⟨x, hx⟩ := w
  exact ⟨x, hx, value_from_any_solution h hx⟩

/-! ## II. The determination relation is a proper constraint

Now the specific theory.  `Determination.Free` is the vacuum condition on a pair;
this section shows the set it cuts out is neither empty nor everything, which
§I says is exactly what makes the predictions mean something. -/

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-- A configuration is **separable** when each direction's scale depends on its
own coordinate alone.

This is the scale-language form of "the directions do not talk to each other":
the pattern can be written down one direction at a time. -/
def Separable (σ : Fin n → A) : Prop := ∀ a c : Fin n, a ≠ c → d a (σ c) = 0

/-- **Every separable configuration is free.**

All four terms of `influence` carry a factor `d a (σ c)` or `d b (σ c)` with
`c` transverse to the pair, and separability kills every one of them.

So the solution space contains a family as large as the choice of one function
per direction: **the theory is very far from inconsistent**, which is what §I
says its predictions need. -/
theorem separable_is_free (σ : Fin n → A) (h : Separable σ) (a b : Fin n) :
    Free σ a b := by
  intro c hc
  have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
  have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hc)).1
  have h1 : d b (σ c) = 0 := h b c (Ne.symm hcb)
  have h2 : d a (σ c) = 0 := h a c (Ne.symm hca)
  simp only [influence, h1, h2, d_zero, mul_zero, sub_zero, add_zero]

/-- **Force is the failure of separability.**

`influence` is precisely the obstruction to writing the scale pattern one
direction at a time.  The converse fails — influences can cancel without being
absent — and that failure is physical rather than technical, being the same one
that lets forces balance. -/
theorem force_is_non_separability (σ : Fin n → A) (a b : Fin n)
    (hforce : ¬ Free σ a b) : ¬ Separable σ :=
  fun h => hforce (separable_is_free σ h a b)

/-! ### A concrete model, and a configuration that is not free

`Positivity.oneAxis` realises A1 in one direction; the determination relation is
empty there and in two directions (`no_influence_in_two`), so a genuine witness
needs three.  Polynomials in three variables with their partial derivatives are
the smallest thing that works. -/

section Model

open MvPolynomial

/-- Partial derivatives commute, via the Lie bracket of derivations: the
commutator is a derivation and it kills every generator. -/
theorem pderiv_comm' {m : ℕ} (i j : Fin m) (p : MvPolynomial (Fin m) ℝ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  have hb : ⁅pderiv (R := ℝ) (σ := Fin m) i, pderiv (R := ℝ) (σ := Fin m) j⁆ = 0 := by
    apply derivation_ext
    intro k
    classical
    simp [Derivation.commutator_apply, pderiv_X, Pi.single_apply]
    split <;> split <;> simp
  have hp := congrArg
    (fun D : Derivation ℝ (MvPolynomial (Fin m) ℝ) (MvPolynomial (Fin m) ℝ) => D p) hb
  simp only [Derivation.commutator_apply] at hp
  simpa [sub_eq_zero] using hp

/-- **A1 realised in `m` directions**: polynomials in `m` variables, with the
partial derivatives as the commuting derivations. -/
noncomputable instance mvScaleAlgebra (m : ℕ) :
    ScaleAlgebra m (MvPolynomial (Fin m) ℝ) where
  d i := fun p => pderiv i p
  d_add _ _ _ := map_add _ _ _
  d_mul i a b := by simpa using pderiv_mul (i := i) (f := a) (g := b)
  d_comm := pderiv_comm'

@[simp] theorem d_eq_pderiv {m : ℕ} (i : Fin m) (p : MvPolynomial (Fin m) ℝ) :
    d i p = pderiv i p := rfl

/-- A **coupled** configuration: two directions flat, the third carrying a
product of the other two coordinates.  The smallest thing that is not
separable. -/
noncomputable def coupled : Fin 3 → MvPolynomial (Fin 3) ℝ := ![0, 0, X 0 * X 1]

/-- Direction `2` exerts a nonzero influence on the pair `(0, 1)`. -/
theorem coupled_influence : influence coupled 0 1 2 = 1 + X 0 * X 1 := by
  simp [influence, coupled]
  ring

/-- And that influence is not zero, checked by evaluating at the origin. -/
theorem coupled_influence_ne_zero : influence coupled 0 1 2 ≠ 0 := by
  intro h
  have := congrArg (eval (fun _ => (0 : ℝ))) (coupled_influence.symm.trans h)
  simp at this

/-- **So the pair `(0, 1)` is not free**: the theory genuinely excludes
something. -/
theorem coupled_not_free : ¬ Free coupled 0 1 := by
  intro hfree
  exact coupled_influence_ne_zero (hfree 2 (by decide))

/-- **The determination relation is not graded.**

Rescaling the log-scale by a constant does *not* rescale the influence: the
second-derivative term carries weight one and the three quadratic terms carry
weight two, so the relation mixes them.  Exhibited at `c = 2`, where the two
sides evaluate to `6` and `4`.

Hence `σ ↦ cσ` is not a symmetry of the theory, weight-zero functions are not
automatically constant on the solution space, and **the weight grading is a
necessary condition on predictions rather than the partition of §II**.  This
sharpens `Weight.lean`'s own description of it as "a cheap test" into a
limitation with a witness. -/
theorem influence_not_homogeneous :
    influence (fun i => MvPolynomial.C (2 : ℝ) * coupled i) 0 1 2
      ≠ MvPolynomial.C 2 * influence coupled 0 1 2 := by
  intro h
  have hv := congrArg (eval (fun i => if i = 2 then (0 : ℝ) else 1)) h
  simp [influence, coupled] at hv
  norm_num at hv

/-- A separable configuration in the same model: each direction carries its own
coordinate. -/
noncomputable def separated : Fin 3 → MvPolynomial (Fin 3) ℝ := fun c => X c

theorem separated_separable : Separable separated := by
  intro a c hac
  simpa [separated] using pderiv_X_of_ne (R := ℝ) (i := a) (j := c) (Ne.symm hac)

/-- **The constraint is proper: neither empty nor everything.**

A whole family of solutions on one side (`separated`, and every separable
configuration with it) and an excluded configuration on the other.  By §I this
is exactly the condition under which the framework's list of predictions is
worth anything — `vacuous_predicts_everything` is the trap it avoids. -/
theorem constraint_is_proper :
    (∀ a b : Fin 3, Free separated a b) ∧ ¬ Free coupled 0 1 :=
  ⟨fun a b => separable_is_free separated separated_separable a b, coupled_not_free⟩

end Model

/-! ## III. The shape of the explanation: irreflexive, mutual, without an arrow -/

/-- **No part appears in its own determiner.**

The influence sum runs over the complement of the pair, so neither member is
invoked in its own explanation.  This is what makes explanation-by-the-complement
legitimate rather than circular. -/
theorem self_not_in_determiner (a b : Fin n) :
    a ∉ Diagonal.transverse a b ∧ b ∉ Diagonal.transverse a b := by
  constructor
  · intro h
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase h)).1 rfl
  · intro h
    exact (Finset.mem_erase.mp h).1 rfl

/-- **Each pair is determined by `n − 2` others.**

The size of the determiner is the amount of dynamics available, and it is zero
at `n = 2` (`no_influence_in_two`) and grows with the number of directions. -/
theorem determiner_card (a b : Fin n) (hab : a ≠ b) :
    (Diagonal.transverse a b).card = n - 2 := by
  classical
  have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
  simp only [Diagonal.transverse]
  rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ, Fintype.card_fin, Nat.sub_sub]

/-- **The determination relation carries no order.**

Both the determiner of a pair and the influence on it are unchanged when the
pair is read the other way round.  So nothing in the relation distinguishes a
direction, and **no arrow of time can be extracted from it** — the arrow must
come from counting (`Entropy.lean`), not from the dynamics.

This is `influence_symm` read as a cost rather than as the third law.  Both
readings are correct; recording only the flattering one would be the mistake. -/
theorem no_arrow_from_determination (σ : Fin n → A) (a b c : Fin n) :
    Diagonal.transverse a b = Diagonal.transverse b a
    ∧ influence σ a b c = influence σ b a c := by
  refine ⟨?_, influence_symm σ a b c⟩
  simp only [Diagonal.transverse]
  exact Finset.erase_right_comm

/-- **In three directions the structure is an exact cycle.**

Each pair has a single determiner and the assignment is a bijection onto the
directions: `{0,1} ← 2`, `{0,2} ← 1`, `{1,2} ← 0`.

Irreflexive by `self_not_in_determiner`, and **not acyclic**.  That is the price
of declining to posit a preferred direction: explanation runs in a loop, and no
layer explains the rest without itself being explained. -/
theorem cycle_of_three :
    Diagonal.transverse (0 : Fin 3) 1 = {2}
    ∧ Diagonal.transverse (0 : Fin 3) 2 = {1}
    ∧ Diagonal.transverse (1 : Fin 3) 2 = {0} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## IV. The ledger

Counts, in the manner of `Audit.lean`: a bookkeeping device, with the theorems
named in the header as the content.  They are carried so that the framework's
claim to predictive power can be weighed rather than asserted. -/

/-- **Free magnitudes: one.**  The weight-one sector is one-dimensional — `Δ`,
equivalently `G` — by `Weight.only_gravity_crosses_the_weight`. -/
def freeMagnitudes : ℕ := 1

/-- **Dimensionless predictions.**

**CORRECTED by `Anchor.lean`, which should be read with this.**  This said
`8` and listed the deflection factor `2` and the precession ratio among them.
Both are arithmetic on imported definitions with no failing instance
(`Anchor.factor_two_has_no_failing_instance`), as are
`PPN.gamma_prediction_is_sharp` and `Attraction.universality_from_counting`.
Half the list was definitional.

What survives the test is four falsifiable dimensionless statements — `γ = 1`,
universal attraction, one cone for every sector, `CV² = 1` — of which exactly one
discriminates against general relativity and the Standard Model. -/
def dimensionlessPredictions : ℕ := 4

/-- **The leverage**: more out than in.

Not a proof of correctness — a wrong theory can have good leverage — but the
quantity that "does it explain and predict anything" was asking about, and it
is only meaningful because `constraint_is_proper` rules out the vacuous case. -/
theorem leverage : freeMagnitudes < dimensionlessPredictions := by decide

/-- **Collected: the answer to what a determination theory delivers.**

The constraint is proper, so the predictions are not vacuous; the ledger is
complete, so nothing is hidden in a third category; and the count is
favourable. -/
theorem what_it_delivers :
    ((∀ a b : Fin 3, Free separated a b) ∧ ¬ Free coupled 0 1)
    ∧ freeMagnitudes < dimensionlessPredictions
    ∧ ∀ (S : C → Prop) (f : C → V), Predicted S f ∨ Modulus S f :=
  ⟨constraint_is_proper, leverage, predicted_or_modulus⟩

end SCD.Explanation
