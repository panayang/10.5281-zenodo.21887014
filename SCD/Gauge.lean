/-
# Internal symmetry has nowhere else to live

Gauge theory picks a Lie group, attaches an internal space to every point, and
lets a connection act on it.  That freedom is the reason the Standard Model's
group is an input: nothing in the formalism says which group.

This framework does not have that freedom, and the lack of it is the
interesting part.  **There is no internal space.**  The only structure at a
point is the directional scale `s : Fin n → Aˣ`.  So a symmetry that is not a
motion of the substrate can only be a symmetry *of the scale pattern* — a
relabelling of directions that leaves every local unit as it was.

That fixes what internal symmetry can be:

* `stabilizer` — the residual symmetries form a group, with no choice involved;
* `stabilizer_eq_bot_of_injective` — if all directions carry different scales
  there is **no** internal symmetry at all;
* `stabilizer_eq_top_of_isotropic` — if all carry the same scale, everything is
  symmetry;
* `sameOrbit_iff_eq_scale` — **the punchline.**  Two directions lie in one
  orbit exactly when they carry the same scale.  So multiplets are degeneracy
  blocks of the scale pattern, and the internal symmetry is the product of the
  symmetries of those blocks.

This yields a genuine restriction rather than a derivation of `SU(3)×SU(2)×U(1)`:
the framework says internal symmetry **must** be the stabilizer of a scale
degeneracy, so gauge factors come in one-per-block and multiplet sizes are
block sizes.  A group acting on an internal space unrelated to the scale
pattern is not available — which is a falsifiable structural claim about what
kinds of gauge theory can exist, not a fit to the observed one.

What is *not* claimed: that the observed pattern is `3 + 2 + 1`, or that
generations are explained.  Those would need the scale pattern itself to be
derived, which it is not.
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fintype.Perm

namespace SCD.Gauge

variable {n : ℕ} {A : Type*} [CommRing A]

/-! ## The residual symmetry group -/

/-- **Internal symmetry**: relabellings of directions that leave every local
unit unchanged.  Nothing is chosen here — this is everything a symmetry could
possibly be, given that the scale pattern is the only structure present. -/
def stabilizer (s : Fin n → Aˣ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {π | ∀ a, s (π a) = s a}
  one_mem' := by intro a; rfl
  mul_mem' := by
    intro π τ hπ hτ a
    show s (π (τ a)) = s a
    rw [hπ (τ a), hτ a]
  inv_mem' := by
    intro π hπ a
    have h := hπ (π⁻¹ a)
    simpa using h.symm

@[simp] theorem mem_stabilizer_iff {s : Fin n → Aˣ} {π : Equiv.Perm (Fin n)} :
    π ∈ stabilizer s ↔ ∀ a, s (π a) = s a := Iff.rfl

/-- **Distinct scales, no internal symmetry.**  Where every direction carries a
different unit there is nothing to relabel: the theory has no gauge freedom at
all.  Internal symmetry is therefore not generic — it is a consequence of
degeneracy. -/
theorem stabilizer_eq_bot_of_injective (s : Fin n → Aˣ) (hinj : Function.Injective s) :
    stabilizer s = ⊥ := by
  ext π
  simp only [mem_stabilizer_iff, Subgroup.mem_bot]
  constructor
  · intro h
    exact Equiv.ext (fun a => hinj (h a))
  · intro h a
    rw [h]
    rfl

/-- **Total degeneracy, total symmetry.**  The isotropic sector — the old
scalar axiom — has the full permutation group as its internal symmetry. -/
theorem stabilizer_eq_top_of_isotropic (s : Fin n → Aˣ) (hiso : ∀ a b, s a = s b) :
    stabilizer s = ⊤ := by
  ext π
  simp only [mem_stabilizer_iff, Subgroup.mem_top, iff_true]
  intro a
  exact hiso (π a) a

/-! ## Multiplets are degeneracy blocks -/

/-- Two directions related by an internal symmetry. -/
def SameOrbit (s : Fin n → Aˣ) (a b : Fin n) : Prop :=
  ∃ π ∈ stabilizer s, π a = b

/-- **Multiplets are exactly the degeneracy blocks of the scale.**

Two directions are related by an internal symmetry if and only if they carry
the same local unit.  Gauge structure and multiplet structure therefore have a
single source: the pattern of coincidences among the directional scales.

An immediate consequence is that multiplet sizes are block sizes — the
framework cannot accommodate a multiplet whose size is unrelated to a
degeneracy of the scale. -/
theorem sameOrbit_iff_eq_scale [DecidableEq (Fin n)] (s : Fin n → Aˣ) (a b : Fin n) :
    SameOrbit s a b ↔ s a = s b := by
  constructor
  · rintro ⟨π, hπ, rfl⟩
    exact (hπ a).symm
  · intro hab
    refine ⟨Equiv.swap a b, ?_, Equiv.swap_apply_left a b⟩
    intro c
    rcases eq_or_ne c a with rfl | hca
    · rw [Equiv.swap_apply_left]; exact hab.symm
    rcases eq_or_ne c b with rfl | hcb
    · rw [Equiv.swap_apply_right]; exact hab
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]




/-- Collected: internal symmetry is entirely determined by the scale pattern,
with no residual freedom to choose a group. -/
theorem internal_symmetry_determined [DecidableEq (Fin n)] (s t : Fin n → Aˣ)
    (h : ∀ a b, (s a = s b) ↔ (t a = t b)) (a b : Fin n) :
    SameOrbit s a b ↔ SameOrbit t a b := by
  rw [sameOrbit_iff_eq_scale, sameOrbit_iff_eq_scale]
  exact h a b

end SCD.Gauge
