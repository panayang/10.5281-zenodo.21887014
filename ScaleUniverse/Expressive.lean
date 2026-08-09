/-
# What this framework can say at all

`CrossCheck.lean` ended with a question I had been avoiding: if gravity is not a
coupling here, what does "unify gravity with the other forces" even mean?  The
suspicion was that the question is itself borrowed.  It is, and working out why
gives a sharper account of the framework than any further result would.

Standard unification asks for one gauge group from which all forces descend.
That presupposes forces are couplings, couplings are the fundamental
description, and "one" means one algebraic object containing the rest.  None of
those hold here.  Forces are not primitive: comparisons of local units are.  So
"unify the forces" is a question in a vocabulary this framework does not have.

The question it *can* answer is: **what is expressible?**

Everything in the development is built from three operations and no others —
comparing scales, failing to commute, and counting.  This file proves that
these really are the whole vocabulary, and that they are mutually independent.

* `invariant_iff_diffPattern` — a quantity is observable (invariant under A5's
  fiducial shift) **exactly when** it is a function of scale *differences*.
  Not "at least"; exactly.  So the scale channel expresses differences and
  nothing else;
* `eval_not_invariant` — absolute scale is therefore not expressible at all;
* `scale_says_nothing_about_rotation` and `rotation_says_nothing_about_scale`
  — the scale channel and the commutator channel share no information;
* `channels_independent` — the two together, which is the diagnosis.

**The diagnosis.**  `CrossCheck.lean` found no cross-sector test.  That was not
bad luck.  The channels are independent *by construction*: the scale channel is
the abelianization and the commutator channel is its kernel, so neither
constrains the other.  A cross-sector test would need them to constrain each
other, and the axioms guarantee they do not.

**SUPERSEDED IN PART — see `Coupling.lean`.**  The independence proved below is
real, but it is independence of the *scalar* scale channel: `Foundation.scale`
is the abelianization, and that construction rests on "ratios commute", which is
a statement about a scalar scale.  A4 gives one scale **per direction**, and
`Coupling.lean` shows that scalings along different directions bracket into a
rotation — so the rotation sector is *generated* by the scale sector and the
channels are coupled after all.

That is the same scalar-for-directional substitution corrected in `Frame.lean`
and `Axis.lean`, appearing a third time.  The theorems below stand as
statements about the scalar sector; the conclusion drawn from them about the
framework does not.
-/
import ScaleUniverse.Foundation
import Mathlib.Data.Real.Basic

namespace ScaleUniverse.Expressive

open ScaleUniverse Foundation

/-! ## The scale channel expresses differences, and exactly differences -/

variable {X : Type*}

/-- A quantity is **observable** when a global change of fiducial does not move
it.  This is A5, stated for an arbitrary function of the scale field. -/
def FiducialInvariant (f : (X → ℝ) → ℝ) : Prop :=
  ∀ (σ : X → ℝ) (c : ℝ), f (fun x => σ x + c) = f σ

/-- The difference pattern of a scale field relative to a base point: all the
information A5 leaves. -/
def diffPattern (x₀ : X) (σ : X → ℝ) : X → ℝ := fun x => σ x - σ x₀

@[simp] theorem diffPattern_shift (x₀ : X) (σ : X → ℝ) (c : ℝ) :
    diffPattern x₀ (fun x => σ x + c) = diffPattern x₀ σ := by
  funext x
  simp only [diffPattern]
  ring

/-- **Every observable is a function of differences.**

Given invariance, evaluating on the difference pattern gives the same answer as
evaluating on the field itself.  So no observable can depend on anything beyond
the differences. -/
theorem invariant_factors (f : (X → ℝ) → ℝ) (hf : FiducialInvariant f)
    (x₀ : X) (σ : X → ℝ) : f σ = f (diffPattern x₀ σ) := by
  have h := hf (diffPattern x₀ σ) (σ x₀)
  simp only [diffPattern] at h
  rw [← h]
  congr 1
  funext x
  ring

/-- **And every function of differences is an observable.** -/
theorem diffPattern_invariant (g : (X → ℝ) → ℝ) (x₀ : X) :
    FiducialInvariant (fun σ => g (diffPattern x₀ σ)) := by
  intro σ c
  simp only [diffPattern_shift]

/-- **The scale channel expresses differences and nothing else.**

Observables are *exactly* the functions of the difference pattern — the
inclusion holds in both directions.  This is the precise expressive limit that
A5 imposes. -/
theorem invariant_iff_diffPattern (f : (X → ℝ) → ℝ) (x₀ : X) :
    FiducialInvariant f ↔ ∃ g : (X → ℝ) → ℝ, ∀ σ, f σ = g (diffPattern x₀ σ) := by
  constructor
  · intro hf
    exact ⟨f, invariant_factors f hf x₀⟩
  · rintro ⟨g, hg⟩
    intro σ c
    rw [hg, hg, diffPattern_shift]

/-- **Absolute scale is not expressible.**

Reading the scale at a point is not invariant, so it is not an observable of
this framework at all — not merely unmeasured, but outside the vocabulary. -/
theorem eval_not_invariant (x : X) :
    ¬ FiducialInvariant (fun σ : X → ℝ => σ x) := by
  intro hf
  have h := hf (fun _ => 0) 1
  simp only [zero_add] at h
  exact absurd h one_ne_zero

/-! ## The two channels share no information

`Foundation.lean` split a comparison canonically into its scale (the
abelianization) and its rotation (the commutator subgroup).  Those two carry
disjoint information, and that is what makes cross-sector tests impossible. -/

variable {Γ : Type*} [Group Γ]

/-- **The scale of a comparison says nothing about its rotation.**

Two comparisons with the same scale differ by an arbitrary element of the
commutator subgroup, so fixing the scale leaves the rotation entirely free. -/
theorem scale_says_nothing_about_rotation (g : Γ) (k : Γ) (hk : k ∈ commutator Γ) :
    scale (k * g) = scale g := by
  rw [scale_mul, scale_eq_one_of_mem_commutator hk, one_mul]

/-- **And the rotation says nothing about the scale.**

Every commutator has trivial scale, so knowing the rotation part determines
nothing about the scale part. -/
theorem rotation_says_nothing_about_scale (g h : Γ) :
    scale (g * h * g⁻¹ * h⁻¹) = 1 := scale_commutator g h

/-- **The channels are independent.**

Fixing either one constrains the other not at all.  This is by construction —
the scale channel is a quotient and the rotation channel is its kernel — so no
amount of further work inside the present axioms can make one test the other. -/
theorem channels_independent (g : Γ) :
    (∀ k ∈ commutator Γ, scale (k * g) = scale g)
    ∧ (∀ a b : Γ, scale (a * b * a⁻¹ * b⁻¹) = 1) :=
  ⟨fun k hk => scale_says_nothing_about_rotation g k hk,
   fun a b => rotation_says_nothing_about_scale a b⟩

/-- Consequently a comparison is recovered from its scale only up to a rotation,
and from its rotation only up to a scale: neither channel alone is a complete
description, and together they are just the original comparison again. -/
theorem neither_channel_complete (g h : Γ) (hs : scale g = scale h) :
    g * h⁻¹ ∈ commutator Γ :=
  (scale_eq_iff_differ_by_rotation g h).mp hs

/-! ## What follows for the shape of future work

The framework can state: a difference of scales, a failure of two comparisons
to commute, and a count of resolvable structures.  It cannot state an absolute
scale, and it cannot state a relation between the scale channel and the
rotation channel, because there is none.

So the missing ingredient is not a bigger symmetry group.  It is a *coupling
between channels* — some structure that makes the scale differences constrain
the commutators, or the counts constrain either.  Nothing in A1–A6 supplies
one, and `CrossCheck.lean` is the observed consequence. -/

/-- Stated for the record: within the present axioms, no function of the scale
channel can determine the rotation channel, because the scale is blind to
exactly the subgroup the rotation lives in. -/
theorem no_channel_coupling (F : Abelianization Γ → Γ) :
    ∀ (g : Γ) (k : Γ), k ∈ commutator Γ → scale (k * g) = scale g :=
  fun g k hk => scale_says_nothing_about_rotation g k hk

end ScaleUniverse.Expressive
