/-
# Predictions carry no information about inputs

`Spacing.lean` §II withdrew an exclusion: the spectrum is *not* structurally
blind to the scale period, it determines it up to the one pure number `Δρ`, and
`Δρ` is weight zero while the gap data has weight-zero content.  So a spectral
determination of `Δρ` was left type-correct and unproposed — an **empty** route
rather than a closed one.

The obvious next move is a survey: list the framework's weight-zero quantities
and ask of each whether it could fix `Δρ`.  That was the plan, and it is the
wrong instrument.  One theorem settles the whole class.

## The theorem

`predicted_cannot_determine_modulus`: if `f` is constant across a theory's
solutions and `g` is not, then `g` is not a function of `f` — the two solutions
that disagree about `g` agree about `f`.

Trivial as a proof and not as a statement.  It says the two columns of
`Explanation.predicted_or_modulus` are **informationally disjoint**: a theory's
predictions can never be used to determine its inputs.  And
`modulus_may_determine_modulus` shows the restriction is one-directional, so it
is a restriction and not a triviality.

## What it does to the question

`CV² = 1` is what the framework **predicts** (`Spectrum.predictedCvSq`).  `Δρ` is
what it does **not** (`Period.no_prediction_of_the_coupling`,
`Weight.invariant_but_not_predicted`).  So `CV²` cannot fix `Δρ` — and neither
can `γ = 1`, universal attraction, one cone for every sector, or `2β = 1 + γ`.
**Every prediction in the ledger is excluded at a stroke**, and the survey never
needed running.

What is left on the spectral side is the quantities the framework does *not*
predict — `ρ`, the threshold positions.  A relation `Δρ = f(ρ)` is permitted
(`modulus_may_determine_modulus`), but it is **another input**, not a
determination: it trades one free number for one assumed relation.

## And what survives, which is the half that matters

The theorem blocks *determining* a modulus from a prediction.  It does not block
**deriving** one from the axioms.  A derivation of `Δρ` is untouched — and a count
of windings per threshold is exactly that: not a reading-off of data but a
statement about which labels the framework's own structures carry.

> So the combinatorial route is not one option among two.  It is the only kind of
> route the accounting permits, and for a reason that has nothing to do with A5.

## A correction, and why the difference matters

Two passes ago the spectral route was said to be closed because A5 blinds the
spectrum to the period.  That was wrong and `Spacing.lean` §II withdrew it.  The
route *is* closed, but by this instead — and the difference is not cosmetic.  The
earlier argument would have made `ρ` unusable as well, since `ρ` is read from the
same gaps; and `ρ` is measured and used throughout the development.  The correct
argument leaves `ρ` exactly where it was and removes only the predictions.

## Scope

The general theorem is proved.  Its application to `CV²` and `Δρ` is a **reading**:
the framework has no formal solution space over which to instantiate `Predicted`
and `Modulus` for those two, so the instantiation is by inspection and is
labelled as one.  What is not a reading is the general fact, and the general fact
is what retires the survey.
-/
import SCD.Spacing
import SCD.Explanation

namespace SCD.Information

open SCD Explanation


variable {C : Type*} {V : Type*} {W : Type*}

/-- **A predicted quantity carries no information about an input.**

If `f` is constant across the theory's solutions and `g` is not, then `g` cannot
be a function of `f`: the two solutions that disagree about `g` agree about `f`.

Trivial as a proof and not as a statement.  It says the two columns of
`Explanation.predicted_or_modulus` are *informationally disjoint* — a theory's
predictions can never be used to determine its inputs — and it settles a whole
class of questions of the form "could this measured invariant fix that free
number?" without examining the invariants one at a time. -/
theorem predicted_cannot_determine_modulus {S : C → Prop} {f : C → V} {g : C → W}
    (hf : Predicted S f) (hg : Modulus S g) :
    ¬ ∃ φ : V → W, ∀ x, S x → g x = φ (f x) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨x, y, hx, hy, hne⟩ := hg
  exact hne ((hφ x hx).trans (by rw [hf x y hx hy, ← hφ y hy]))

/-- **And the converse direction is open**, which is why the result is a
restriction and not a triviality: a modulus can perfectly well be a function of
another modulus. -/
theorem modulus_may_determine_modulus :
    ∃ (S : ℝ → Prop) (g h : ℝ → ℝ), Modulus S g ∧ Modulus S h
      ∧ ∃ φ : ℝ → ℝ, ∀ x, S x → h x = φ (g x) := by
  refine ⟨fun _ => True, id, id, ⟨0, 1, trivial, trivial, by norm_num⟩,
    ⟨0, 1, trivial, trivial, by norm_num⟩, id, fun x _ => rfl⟩


end SCD.Information
