/-
# Dynamics, redefined: not "what happens next" but "what determines what"

Dynamics is normally the relation between force and motion, and it presupposes
three things this framework does not have: a state at a time, a time parameter
external to the state, and the persistence of a thing across times.

* time is not external — it is the direction the scale drifts (`Signature.lean`);
* there is no state-at-a-time — content is a *slice*, and what exists depends on
  the scale one asks at (`Emergence.lean`);
* nothing persists — there are no fundamental particles to persist
  (`Emergence.no_fundamental_list`).

So the usual shape is unavailable, and `Native.no_global_field_equation` says so
outright.  The question is whether that is a hole or a position.

## The reformulation

Dynamics answers one question: **given part of the world, what is the rest?**
"Given the state now, what is it later" is one way to cut that question, and it
needs a time.  The general form does not:

> **Dynamics is a determination relation among the parts of one configuration.**

And in that form the framework already has a dynamics, uniform across everything
computed here.  The recurring result of the whole development is:

> **A part is determined by its complement, never by itself.**

* `Diagonal.ric_offdiag` — no pair of directions carries its own curvature; every
  term built from `σ_a` and `σ_b` alone cancels, and what is left is a sum over
  the complement;
* `Diagonal.combination_is_transverse` — the same for the vacuum combination;
* `Emergence.resolved` — the content at a scale is fixed by the thresholds below
  it;
* `Transport.transport_unique_of_nondegenerate` — the relation between two
  patterns is unique when nothing is degenerate.

This file makes that the definition rather than an observation.

## Force, and interaction

If dynamics is determination, then:

* **free** means a part determines itself — the complement contributes nothing
  (`Free`);
* **force** is the failure of that: the complement's contribution, term by term
  (`influence`);
* **two things interact** when each appears in the other's complement.

That last is automatically reciprocal, and the third law comes out as a
*symmetry of the influence itself*: `influence_symm`, hence `ric_offdiag_symm`.
Action and reaction are not two facts that happen to match; they are one
expression read from either end.

## Two consequences that are not restatements

**There is no dynamics in two directions.**  `no_influence_in_two`: with two
directions a pair has no complement, so nothing can determine anything and every
configuration is free.  The amount of dynamics available is the size of the
complement, `n − 2`.  That is the same shape as
`Openness.no_dissipation_in_one_direction` — a thing that needs somewhere
transverse to happen.

**A7 says the dynamics is well posed.**  The determination relations are indexed
by unordered pairs, which is what `Pattern.rotDim2` counts; the things determined
are the scale functions, which is what `scaleDim2` counts.  So `rotDim2 =
scaleDim2` reads:

> the number of determination relations equals the number of functions they
> determine — the system is neither over- nor under-determined.

`Locus.lean` reads A7 as being about which labels are observable.  This is a
second reading of the same equation, and it is about **well-posedness**.  Both
are readings; A7 remains an axiom.

## What this does not do

It does not produce trajectories, and it does not say why this configuration
rather than another.  A constraint system has a solution *space*, and nothing
here picks a point in it.

That is either the framework's honest limit or its position, and the difference
matters: if it is the position, then "why this world" is not a dynamical question
here at all, and the framework owes an account of what kind of question it is.
Nothing in the development supplies that account, and this file does not either.
It supplies the vocabulary in which the question can be posed correctly.
-/
import SCD.Diagonal

namespace SCD.Determination

open SCD ScaleAlgebra Diagonal

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A] (σ : Fin n → A)

/-! ## I. Influence: what one direction contributes to a pair -/

/-- The **influence** of direction `c` on the pair `(a, b)`: the term `c`
contributes to the pair's curvature.

This is the summand of `Diagonal.ric_offdiag`, named because it is the
framework's own notion of one part acting on another. -/
def influence (a b c : Fin n) : A :=
  d a (d b (σ c)) - d b (σ a) * d a (σ c)
    - d a (σ b) * d b (σ c) + d a (σ c) * d b (σ c)

/-- **The third law, as a symmetry of the influence.**

`influence σ a b c = influence σ b a c`: what `c` contributes to the pair read
one way is what it contributes read the other.  The two cross terms exchange and
`d_comm` handles the second derivative.

Action and reaction are not two facts that agree; they are one expression. -/
theorem influence_symm (a b c : Fin n) :
    influence σ a b c = influence σ b a c := by
  simp only [influence]
  rw [d_comm a b (σ c)]
  ring

/-- **A pair is free when nothing outside it contributes.**

The framework's notion of "no force": the complement's influence vanishes term by
term. -/
def Free (a b : Fin n) : Prop := ∀ c ∈ transverse a b, influence σ a b c = 0

/-! ## II. Determination: the curvature of a pair is a function of its complement -/

variable (η : Fin n → A) (w : Fin n → Aˣ)

/-- **The off-diagonal curvature is minus the total influence of the
complement.**

`Diagonal.ric_offdiag` restated in this vocabulary: the pair contributes nothing
to itself, and what it has is what the rest of the world puts there. -/
theorem curvature_is_total_influence (hη : ∀ a : Fin n, η a * η a = 1)
    (a b : Fin n) (hab : a ≠ b) :
    Diagonal.Ric η w σ a b = -∑ c ∈ transverse a b, influence σ a b c :=
  Diagonal.ric_offdiag η w σ hη a b hab

/-- **A free pair is flat off the diagonal.**

If nothing outside contributes, the pair's off-diagonal curvature vanishes.  The
converse fails, and the failure is physical: influences can cancel without being
absent, exactly as forces can. -/
theorem free_implies_offdiag_zero (hη : ∀ a : Fin n, η a * η a = 1)
    (a b : Fin n) (hab : a ≠ b) (hfree : Free σ a b) :
    Diagonal.Ric η w σ a b = 0 := by
  rw [curvature_is_total_influence σ η w hη a b hab, Finset.sum_eq_zero hfree, neg_zero]

/-- **And the curvature is symmetric**, which is the third law at the level of
the geometry rather than of a single influence. -/
theorem ric_offdiag_symm (hη : ∀ a : Fin n, η a * η a = 1)
    (a b : Fin n) (hab : a ≠ b) :
    Diagonal.Ric η w σ a b = Diagonal.Ric η w σ b a := by
  rw [curvature_is_total_influence σ η w hη a b hab,
    curvature_is_total_influence σ η w hη b a (Ne.symm hab)]
  have hset : transverse a b = transverse b a := by
    simp only [transverse]
    exact Finset.erase_right_comm
  rw [hset]
  exact congrArg Neg.neg
    (Finset.sum_congr rfl fun c _ => influence_symm σ a b c)

/-! ## III. The amount of dynamics is the size of the complement -/

section TwoDirections

variable {B : Type*} [CommRing B] [ScaleAlgebra 2 B]

/-- **In two directions there is no dynamics.**

A pair has no complement, so the influence sum is empty: nothing determines
anything and every configuration is free.  The amount of dynamics available is
the size of the complement, `n − 2`.

Same shape as `Openness.no_dissipation_in_one_direction`: a thing that needs
somewhere transverse to happen. -/
theorem no_influence_in_two (τ : Fin 2 → B) (a b : Fin 2) (hab : a ≠ b) :
    Free τ a b := by
  intro c hc
  rw [transverse_empty_of_two a b hab] at hc
  exact absurd hc (Finset.notMem_empty c)

/-- Hence every configuration in two directions has vanishing off-diagonal
curvature, whatever the scales are. -/
theorem two_directions_always_free (ζ : Fin 2 → B) (v : Fin 2 → Bˣ) (τ : Fin 2 → B)
    (hζ : ∀ a : Fin 2, ζ a * ζ a = 1) (a b : Fin 2) (hab : a ≠ b) :
    Diagonal.Ric ζ v τ a b = 0 :=
  free_implies_offdiag_zero τ ζ v hζ a b hab (no_influence_in_two τ a b hab)

end TwoDirections

/-! ## IV. A7 as well-posedness

The determination relations are indexed by unordered pairs — `Pattern.rotDim2`
counts them doubled — and what they determine is the scale functions, which
`scaleDim2` counts doubled.  A7 equates the two.

`Locus.lean` reads A7 as a commitment about which labels are observable.  This is
a second reading of the same equation, and it is about whether the system of
determinations closes.  Both are readings of an axiom, and A7 remains one. -/

/-- **A7, read as well-posedness**: as many determination relations as functions
determined, at exactly one dimension. -/
theorem determination_well_posed (m : ℕ) : Observability m ↔ m = 2 :=
  observability_iff_two m

/-- And away from that dimension the system is genuinely over- or
under-determined: more relations than functions above, fewer below. -/
theorem over_or_under_determined (m : ℕ) :
    (2 < m → scaleDim2 m < rotDim2 m) ∧ (m < 2 → rotDim2 m < scaleDim2 m) :=
  ⟨more_rotations_than_directions m, fewer_rotations_than_directions m⟩

end SCD.Determination
