/-
# What the framework says about a size, which is one conditional law

`Size.lean` found that the cosmological escapes are a **size** of content and its
derivative, that the framework never defined the step, and that G4's missing
weight on outcomes is the same missing object.  So: does the framework's own
structure constrain a size, or is it free?

The answer is one law, and it is conditional on one property.

## The property

`Size.SizeSystem` asked only for monotonicity, which is far too little to weight
anything — "one if anything is there" is monotone.  The next condition is
**modularity**, the inclusion–exclusion law, which is what makes a size a *count*
rather than merely a monotone number.

`modularity_is_a_restriction`: it is not free.  A monotone size can count two
disjoint things as one.

## The law

`Internal.record_union` says joining two observers **intersects** their records —
the lattice turns over, which §V.t recorded as the surprise of internality.  Feed
that to a modular size and `observer_counting_law` follows: inclusion–exclusion
transfers to the observer lattice, and the record of a joint observer is measured
by the two separate records and their union.

> **This is the first thing in the development that weighs anything**, and it is
> one property away from free.

## What that changes about G4, and what it does not

`Layers.lean` left G4 as *nothing weights the outcomes*, and it was natural to
read that as the structure resisting a weight.  It does not.

> The observer lattice **accepts** a weight the moment modularity is granted, and
> uses it immediately.  What is missing is not a place for the weight to live —
> it is anything that picks one.

That is a smaller and more specific gap than "no probability", and it names the
condition rather than the absence.

**But it is not G4.**  What is weighed here are **records** — sets of thresholds
crossed — and G4 asked for a weight on the *indistinguishability classes* of
`Layers.lean`, which are classes of ring elements.  Those are different objects
and nothing here relates them.  So this is adjacent to G4, not G4, and saying so
is the difference between progress and the appearance of it.

**And modularity granted is another input.**  Nothing in A1–A7 supplies it; the
framework's counts are counts, and a count is modular, but *that the size is a
count* is exactly the assumption.  `Attraction.lean` made the same assumption
about the source and the register anchored it against antihydrogen; there is no
comparable anchor here.
-/
import SCD.Size
import SCD.Internal

namespace SCD.Valuation

open SCD


/-- **Modularity**: the inclusion–exclusion law, which is what makes a size a
*count* rather than merely a monotone number.

`Size.SizeSystem` asked only for monotonicity, which is too little to weight
anything.  This is the next condition and, as it turns out, the only one the
framework's own structure has any purchase on. -/
def Modular {X : Type*} (Z : Set X → ℝ) : Prop :=
  ∀ A B : Set X, Z (A ∪ B) + Z (A ∩ B) = Z A + Z B

/-- **It is a restriction.**

A monotone size need not be modular: "one if anything is there" is monotone and
counts two disjoint things as one. -/
theorem modularity_is_a_restriction : ∃ Z : Set ℕ → ℝ, ¬ Modular Z := by
  refine ⟨fun A => if A = ∅ then 0 else 1, ?_⟩
  intro h
  have hAB : ({0} : Set ℕ) ∩ {1} = ∅ := by ext x; simp
  have hU : ({0} : Set ℕ) ∪ {1} ≠ ∅ := by
    intro hc
    have hm : (0 : ℕ) ∈ ({0} : Set ℕ) ∪ {1} := by simp
    rw [hc] at hm; exact hm
  have hA : ({0} : Set ℕ) ≠ ∅ := by
    intro hc
    have hm : (0 : ℕ) ∈ ({0} : Set ℕ) := rfl
    rw [hc] at hm; exact hm
  have hB : ({1} : Set ℕ) ≠ ∅ := by
    intro hc
    have hm : (1 : ℕ) ∈ ({1} : Set ℕ) := rfl
    rw [hc] at hm; exact hm
  have hh := h {0} {1}
  simp only [hAB, if_neg hU, if_neg hA, if_neg hB] at hh
  norm_num at hh

/-- **And the framework's own union law then becomes a counting law.**

`Internal.record_union` says joining observers *intersects* their records.  Feed
that to a modular size and inclusion–exclusion transfers to the observer
lattice: the record of a joint observer is measured by the two separate records
and their union.

This is the first thing in the development that weighs anything, and it is
conditional on exactly one property. -/
theorem observer_counting_law {n : ℕ} {ι : Type*} (Z : Set ι → ℝ) (hZ : Modular Z)
    (μ : ι → Observer.Threshold n) (σ : Observer.Resolution n)
    (S S' : Finset (Fin n)) :
    Z (Internal.record (S ∪ S') μ σ)
        + Z (Internal.record S μ σ ∪ Internal.record S' μ σ)
      = Z (Internal.record S μ σ) + Z (Internal.record S' μ σ) := by
  rw [Internal.record_union]
  have h := hZ (Internal.record S μ σ) (Internal.record S' μ σ)
  linarith


end SCD.Valuation
