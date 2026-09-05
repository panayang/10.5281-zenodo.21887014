/-
# Way out (b), written: the degree source, and why it fails too

§V.k left the codimension mismatch two ways out and `Codimension2.lean` closed
*(a)*.  This file writes *(b)* — the source law with a **degree** density — and
asks the question that motivated it: does the same `κ` come out?

**Yes, and the answer is worth nothing.**  Then *(b)* fails anyway, for a reason
neither branch anticipated, and the reason closes the whole question.

## I.  The coefficient is a shape, not a result

`degree_gives_the_same_kappa` is `Index.A6'_from_index` **applied**, not reproved.
That is the finding: A6″'s `Δ` was already an arbitrary ring element, and the
derivation of `κ = −2(n−1)Δ` never used a single property of it — not that it is
a period, not that it is non-zero, not that it is real.  Any constant whatever
gives the same formula with itself in the slot.

> So "does the degree version give the same `κ`?" was a malformed question, and
> reproducing the formula is not evidence for anything.

The one-line proof is the honest form of that answer.  It is worth writing
precisely because the expected answer — a solid-angle factor, an `n`-dependent
normalisation, *some* arithmetic to check — does not arise.

## II.  The degree passes the test the block failed

`Codimension2.lean` killed *(a)* because `ℤ/2` is torsion and an additive real
map on it vanishes.  `ℤ` is torsion-free, and `degree_admits_an_additive_source`
exhibits `k ↦ λ·k`.  So *(b)* is **not** killed by that argument.  It had a real
chance, and this file is not a foregone conclusion.

## III.  It dies on attraction, and so would anything else

`additive_nonneg_on_group_is_trivial`: on a **group**, an additive map to `ℝ`
that is non-negative is identically zero.  Three lines — `f(1) = 0`, then
`f(a) + f(a⁻¹) = 0` with both terms non-negative.

Non-negativity is not an aesthetic preference.  It is what
`Attraction.attraction_from_counting` needs, and it is there because gravity is
**universally attractive** — antihydrogen falls.

And the theorem subsumes `Codimension2.lean`'s: the block died at `a = a⁻¹`, the
degree dies at `f(k) + f(−k) = 0`.  One theorem, two branches, and it did not need
to know which codimension anything was.

> **No group-valued charge can be a universally attractive additive source.**

Every topological charge in this development is group-valued — `π₁` and `π₂` are
groups, and that is what makes them topological.  So the source of the geometry
**cannot be topological at all**, and §V.k's question — *which* codimension — was
malformed on both branches.  It has an answer, and the answer is neither.

## IV.  Sharp, and not proving too much

`monoid_source_exists`: on `Multiplicative ℕ` the map `k ↦ k` is additive,
non-negative and non-zero.  So it is **inverses** that do the killing, not
additivity and not positivity.  `Particle.Species.threshold` survives for exactly
that reason: content is a cardinality and there is no anti-content.

Two checks that the theorem is not too strong:

* real gravity's source is not a topological charge either, and mass is
  non-negative — the conclusion agrees with the world rather than embarrassing
  itself against it;
* electric charge **is** signed and **does** source an interaction — permitted,
  because that interaction is not universally attractive.  The theorem isolates
  attraction as the killer, which is the right joint.

## V.  What *(b)* would have cost, had it survived

Recorded because it is what the trade would have been.  The degree is a property
of the **axis** field; `Δ` is the period of the **scalar** `σ`.  Nothing relates
them, so *(b)* introduces `λ`, the scale flux per unit degree, and
`ratio_is_weight_zero` says `λ/Δ` survives rescaling — a **second pure number**
beside `Δρ`.  `two_pure_numbers_where_there_was_one` is the consequence: gravity
would carry `λρ` and the action step `Δρ`, and
`link_survives_only_if_equal` says the `G`–`ℏ` common origin holds only if `λ = Δ`
is separately postulated.

So *(b)* was never the cheap option.  It is closed on other grounds, and this is
noted so the closure is not mistaken for a rescue.

## What is not claimed

That A6″ is false, or that its consequences fail.  They are untouched — §V.aq
already recorded that the factor is algebraic in `ν`.  What is claimed is that
**no reading of A6″ makes it an index**, because the only sources an index could
have are group-valued and none of those can attract.  A6″ is a posit about how
counting sources scale, and this file removes the last route by which it might
have been something more.
-/
import SCD.Index
import SCD.Attraction
import SCD.Charges
import SCD.Weight

namespace SCD.DegreeSource

open SCD


/-! ## I. The coefficient survives, and that is worth nothing -/

/-- **The degree version gives the same `κ`, and this proof is why that is
empty.**

It is `Index.A6'_from_index` applied with `λ` in the slot — no new argument,
because the original never used a property of `Δ`.  The coefficient is a shape
the derivation has for *any* constant. -/
theorem degree_gives_the_same_kappa {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]
    (lam nu s : A) (hlin : gradsq n s = 0)
    (h : Index.IndexResponse n lam nu s) :
    RscBare n s = (-2 * ((n : A) - 1) * lam) * nu :=
  Index.A6'_from_index lam nu s hlin h

/-! ## II. The degree passes the test the block failed -/

/-- **`ℤ` admits a non-zero additive real source**, which `ℤ/2` did not.

`k ↦ λ·k` is the map, and it is why way out *(b)* is not disposed of by
`Codimension2.two_valued_source_is_trivial`. -/
theorem degree_admits_an_additive_source (lam : ℝ) (a b : Multiplicative ℤ) :
    lam * ((Multiplicative.toAdd (a * b) : ℤ) : ℝ)
      = lam * ((Multiplicative.toAdd a : ℤ) : ℝ)
        + lam * ((Multiplicative.toAdd b : ℤ) : ℝ) := by
  show lam * ((Multiplicative.toAdd a + Multiplicative.toAdd b : ℤ) : ℝ) = _
  push_cast
  ring

/-! ## III. But no group-valued charge can attract universally -/

/-- **On a group, an additive non-negative real source is identically zero.**

`f(1) = 0`, then `f(a) + f(a⁻¹) = 0` with both non-negative.  Non-negativity is
what `Attraction.attraction_from_counting` requires, and it is required because
gravity attracts universally.

This subsumes `Codimension2.two_valued_source_is_trivial`: torsion and sign are
two ways for the same inverse to close the argument. -/
theorem additive_nonneg_on_group_is_trivial {G : Type*} [Group G] (f : G → ℝ)
    (hadd : ∀ a b : G, f (a * b) = f a + f b) (hpos : ∀ a : G, 0 ≤ f a) (a : G) :
    f a = 0 := by
  have h1 : f 1 = 0 := by
    have := hadd 1 1
    rw [one_mul] at this
    linarith
  have hinv : f a + f a⁻¹ = 0 := by
    have := hadd a a⁻¹
    rw [mul_inv_cancel, h1] at this
    linarith
  have := hpos a
  have := hpos a⁻¹
  linarith

/-- **So the hedgehog degree cannot source an attractive geometry** — which is
`Attraction.signed_source_would_antigravitate` again, now as an algebraic
identity rather than an appeal to the data. -/
theorem signed_degree_cannot_attract (f : Multiplicative ℤ → ℝ)
    (hadd : ∀ a b, f (a * b) = f a + f b) (hpos : ∀ a, 0 ≤ f a) (a : Multiplicative ℤ) :
    f a = 0 :=
  additive_nonneg_on_group_is_trivial f hadd hpos a

/-! ## IV. And that is sharp: a monoid escapes -/

/-- **And that is sharp: a monoid escapes.**

`k ↦ k` on `Multiplicative ℕ` is additive, non-negative and non-zero.  So the
obstruction is **inverses**, not additivity and not positivity — and
`Particle.Species.threshold` survives because content is a cardinality with no
anti-content. -/
theorem monoid_source_exists :
    ∃ f : Multiplicative ℕ → ℝ,
      (∀ a b, f (a * b) = f a + f b) ∧ (∀ a, 0 ≤ f a) ∧ f (Multiplicative.ofAdd 1) ≠ 0 := by
  refine ⟨fun k => ((Multiplicative.toAdd k : ℕ) : ℝ), ?_, ?_, ?_⟩
  · intro a b
    show ((Multiplicative.toAdd a + Multiplicative.toAdd b : ℕ) : ℝ) = _
    push_cast
    ring
  · intro a
    exact Nat.cast_nonneg _
  · norm_num

/-! ## V. And what the swap costs -/

/-- **`λ/Δ` is a pure number**: it survives the rescaling that moves both.  So
way out *(b)* would have introduced a second modulus beside `Δρ`. -/
theorem ratio_is_weight_zero (c lam D : ℝ) (hc : c ≠ 0) :
    (c * lam) / (c * D) = lam / D := by
  rw [mul_div_mul_left _ _ hc]

/-- **And the two would not have coincided.**  Gravity would carry `λρ`, the
action step `Δρ`, and they differ exactly when `λ ≠ Δ`. -/
theorem two_pure_numbers_where_there_was_one (lam D rho : ℝ) (hrho : rho ≠ 0)
    (h : lam ≠ D) : lam * rho ≠ D * rho := fun hc => h (by
      field_simp at hc; tauto)

/-- **The `G`–`ℏ` common origin would survive only by separate postulate.**

Under A6″ the gravitational coefficient *was* the scale period, so one number
served both.  Way out *(b)* splits them unless `λ = Δ` is assumed. -/
theorem link_survives_only_if_equal (lam D rho : ℝ) (h : lam = D) :
    lam * rho = D * rho := by rw [h]


end SCD.DegreeSource
