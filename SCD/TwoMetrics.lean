/-
# Two metrics: the coupling and the observables are computed in different
# geometries

The framework's founding statement needs a group and the ring's remaining job is
a **bilinear pairing** (§V.at).  This file asks the obvious next question — *which*
pairing — and finds that the development has been using **two**, in two sectors,
joined by one theorem whose hypothesis the physics cannot satisfy.

## I.  The two sectors

`Conformal.lean` builds `Chr`, `Rm`, `Ric` and

        `RscBare σ = ∑_b Ric σ b b` ,

whose own docstring calls it *the `δ`-trace of Ricci* and whose metric is
`e^{2σ}δ`.  The pairing is the ring's multiplication summed with **all plus
signs** — Euclidean.  This is the sector `Index.A6'_from_index` computes in, so
**`κ = −2(n−1)Δ` is a Euclidean result**.

`Diagonal.lean` builds its own `Chr η w σ` and `Ric η w σ` on the metric
`met η w`, with `η : Fin n → A` satisfying `η² = 1` — a signature carried as a
parameter.  `Chain.lean`'s own table shows **the whole gravity chain runs here**:
`Diagonal.Chr`, `Diagonal.ric_tt`, `Diagonal.ric_rr`,
`Diagonal.combination_is_transverse`, `Diagonal.vacuum_scale_sum`, then `γ = 1`
and the deflection.  And `combination_is_transverse` needs

        `hLor : η t * η r = -1` .

## II.  The join, and where it is

`Anisotropic.ChrDir_of_isotropic` is the one theorem carrying the anisotropic
connection back to `Conformal.Chr`.  Its docstring states its own scope:
*on the isotropic locus **with Euclidean signature***, and its hypothesis is
`hη : ∀ a, η a = 1`.

`euclidean_excludes_lorentzian` says those two hypotheses cannot both hold:
`η ≡ 1` gives `η_tη_r = 1`, and `1 = -1` forces `2 = 0`.
`bridge_unavailable_at_lorentzian` is the same fact stated as the obstruction.

> **The only bridge between the two sectors holds exactly where the physics does
> not.**

And the difference is not a convention that cancels: `delta_trace_ne_eta_trace`
exhibits a Lorentzian `η` and a Ricci diagonal on which the unweighted trace and
the `η`-weighted trace differ — `2` against `0`.

## III.  What this means, stated narrowly

**`κ` and the observables have never been shown to be about the same geometry.**
`γ = 1`, the deflection ratio and the vacuum solution are internally derived in
the `η` sector and nothing here disturbs them.  `κ = −2(n−1)Δ` is derived in the
`δ` sector.  The sentence "the framework fixes the coupling **and** predicts the
deflection" is two results in two geometries, and the register has been reading
it as one chain.

**What is not claimed.**  That `κ` is wrong, that the observables are wrong, or
that the repair fails.  The likely repair is visible — redo `RscBare_eq` with an
`η`-weighted trace and see whether `−2(n−1)` survives — and this file does not do
it.  What is claimed is that the step has never been taken and that the chain has
been quoted as though it had.

**And why it was invisible.**  `§V.at` is the reason: a commutative ring supplies
the unit group and the pairing in one move, so the pairing never had to be
chosen, and a `δ` was inherited from the ring rather than selected.  The
signature then had to be reintroduced by hand as a parameter `η` in a second
sector.  `Signature.lean` derives a codimension-one **splitting** from the drift
and calls it "the Lorentzian shape" — correctly, and it is not a signature: a
splitting is a flag, a signature is a property of a form.  That file's own
closing paragraph already says the timelike sign is not derived.

So the suspicion that the mathematical form went astray has a first concrete
instance, and it is this: **the pairing was never chosen, and the framework has
two.**
-/
import SCD.Anisotropic
import SCD.Conformal

namespace SCD.TwoMetrics

open SCD


/-! ## I. The two hypotheses are exclusive -/

/-- **Euclidean signature and a Lorentzian pair are exclusive.**

`η ≡ 1` gives `η_tη_r = 1`, and `1 = -1` forces `2 = 0`.  So
`Anisotropic.ChrDir_of_isotropic`'s hypothesis and
`Diagonal.combination_is_transverse`'s cannot both hold. -/
theorem euclidean_excludes_lorentzian {A : Type*} [CommRing A] (h2 : (2 : A) ≠ 0)
    {n : ℕ} (η : Fin n → A) (t r : Fin n)
    (hEuc : ∀ a, η a = 1) (hLor : η t * η r = -1) : False := by
  rw [hEuc t, hEuc r, one_mul] at hLor
  exact h2 (by linear_combination hLor)

/-! ## II. And the two traces are different functionals -/

/-- **And the difference does not cancel.**

A Lorentzian `η` on two directions and a Ricci diagonal of ones: the unweighted
trace is `2` and the `η`-weighted trace is `0`.  `Conformal.RscBare` is the
unweighted one. -/
theorem delta_trace_ne_eta_trace :
    ∃ (η : Fin 2 → ℝ) (R : Fin 2 → ℝ),
      (∀ a, η a * η a = 1) ∧ η 0 * η 1 = -1
        ∧ (∑ b, R b) ≠ ∑ b, η b * R b := by
  refine ⟨![1, -1], ![1, 1], ?_, by norm_num, ?_⟩
  · intro a; fin_cases a <;> norm_num
  · norm_num [Fin.sum_univ_two]

/-! ## III. So the one bridge between the sectors is unavailable where it is needed -/

/-- **So the one bridge between the sectors is unavailable where the physics
lives.**

`Chain.lean`'s table runs the gravity chain through `Diagonal.*`, which needs the
Lorentzian pair; the only theorem carrying that sector back to `Conformal.Chr`
needs `η ≡ 1`. -/
theorem bridge_unavailable_at_lorentzian {A : Type*} [CommRing A] (h2 : (2 : A) ≠ 0)
    {n : ℕ} (η : Fin n → A) (t r : Fin n) (hLor : η t * η r = -1) :
    ¬ (∀ a, η a = 1) :=
  fun hEuc => euclidean_excludes_lorentzian h2 η t r hEuc hLor


end SCD.TwoMetrics
