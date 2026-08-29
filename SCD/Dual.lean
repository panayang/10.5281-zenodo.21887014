/-
# A3′: the scale group and its dual, and the two branches that follow

## What A3 actually says, and what it was read as saying

`Axioms.scale_energy_duality_is_inversion` shows the whole content of A3 is
`F · F⁻¹ = 1` — **inversion in the group of scale fields**.  Inversion is a map
`G → G`.  Physical energy is the generator of translation along the drift, which
belongs to the **dual** `Ĝ`, and calling `s⁻¹` "the energy" identifies the two.

`Momentum.lean` already had to unpick this once: reading A3 per direction gave
`ε_t` as energy and `ε_i` as momentum, and the dispersion relation followed.
This file asks the next question — *what does it cost to say that the scale group
and its dual are the same size?* — and finds that it costs a **classification**
rather than an assumption.

## A3′, and why it is a gain

> **A3′.**  The scale group carries a nondegenerate pairing with its own dual;
> "energy–momentum" is the scale's partner under it.  `ε·s = 1` is the
> normalisation of that pairing — a choice of unit for `ħ` — not a separate law.

The cost is honest and should be stated first: **`Crossed.lean`'s "ħ is an exact
scale step" is demoted from a discovery to a restatement**, in the same way A7
was demoted from "almost derived" to "an axiom".  What is bought is that
self-dual locally compact abelian groups are *classified*, so the scale group is
no longer free: it is `ℝⁿ`, or a compact–discrete pair like `𝕋 × ℤ`, or finite,
or adelic.  **That is the same shape of argument as `Algebra.lean`'s real rank
one**: a structural condition cutting an infinite space of possibilities to a
short list.

The classification itself is standard harmonic analysis and is **cited, not
proved** — on the same footing as the rank-one classification and the homotopy of
projective spaces (`Audit.lean` §IV).

## The two branches the development already has, and their relation

The framework has been carrying **both** of the first two branches without ever
relating them:

* the **`ℝ` branch** — `Axioms.ScaleField`, a real-valued log-scale;
* the **`𝕋` branch** — `Defect.ScaleDefect`, a log-scale defined modulo a period
  `Δ`, which is what lets a defect wind.

`Audit.lean` §I registers a retraction (`Codimension.lean`) that was really a
collision between these two readings.  Under A3′ they are not two models: they
are two branches of one classification, and `Defect.lift` is exactly the covering
map `ℝ → ℝ/ΔZ` that relates them.

And the framework now *needs* the second: `Index.no_period_no_gravity` says a
scale with no period sources nothing.  So

> **gravity selects the `𝕋` branch**, and the `ℝ` branch is its `Δ → 0`
> degeneration — flat, and with no defects to wind.

`R_branch_has_no_holonomy` and `T_branch_has_holonomy` below make the contrast a
pair of theorems rather than a remark.

## W2 and W3, which the `𝕋` branch makes available

Once the scale is circle-valued there are objects with no analogue in the `ℝ`
branch, and they are the ones `Well.lean` could not state:

* **W2, scale monodromy.**  `∮dσ = Δk` around a non-contractible loop.  This is
  not a shortcut — it is a **change of unit**: you come back with a different
  ruler.  `monodromy_shifts_the_unit`;
* **W3, a multivalued scale over one bare place.**  The fibre of the covering
  over a bare location is a **`ℤ`-torsor**: "here with unit `u`" and "here with
  unit `u·e^{Δ}`" are different physical situations.  `fibre_is_a_torsor`,
  `fibre_no_fixed_origin`.

W3 is the one that deserves the word *wormhole*, and it is worth being precise
about why it is not the GR object: there is no second region and no throat.  What
there is is that the same bare place carries a `ℤ` of distinguishable states, so
"where you are" does not determine "what your unit is".  A traversal is a move in
the torsor, and by `Well.stretch_ne_zero` every such move has strictly positive
measured length.

**Not claimed:** that these objects occur.  As in `Attraction.lean`, existence is
a question for the source law, and `Index.no_period_no_gravity` only says the
period must be nonzero for gravity to exist at all — not how large it is, which
is the undetermined `Δρ` of `Index.coupling_is_one_dimensionless_number`.
-/
import SCD.Axioms
import SCD.Defect
import SCD.Index

namespace SCD.Dual

open SCD

/-! ## I. The two branches, and what separates them -/

/-- **The `ℝ` branch has no holonomy.**

A real-valued log-scale is single-valued, so following it around a loop returns
it exactly: the winding is forced to zero, and by `Index.no_period_no_source`
there is nothing to source a geometry.

Stated as `Defect.ScaleDefect` at period `0`, which is what "no period" means. -/
theorem R_branch_has_no_holonomy (D : Defect.ScaleDefect (0 : ℝ)) (x : ℝ) :
    D.lift (x + 1) = D.lift x := by
  have h := D.quasiperiodic x
  rw [mul_zero, add_zero] at h
  exact h

/-- And hence the `ℝ` branch is trivial in the sense `Defect.lean` defines: no
configuration in it is a defect. -/
theorem R_branch_is_trivial (D : Defect.ScaleDefect (0 : ℝ)) :
    Defect.ScaleDefect.IsTrivial D := R_branch_has_no_holonomy D

/-- **The `𝕋` branch has holonomy, and it is quantised.**

With a nonzero period the log-scale is defined modulo `Δ`, and a circuit shifts
it by an integer number of periods.  That integer is the defect charge, and by
`Index.lean` it is what sources the geometry. -/
theorem T_branch_has_holonomy {Δ : ℝ} (D : Defect.ScaleDefect Δ) (x : ℝ) :
    D.lift (x + 1) - D.lift x = (D.winding : ℝ) * Δ := by
  rw [D.quasiperiodic x]
  ring

/-- **Gravity selects the branch.**

`Index.no_period_no_gravity` says a scale with no period sources nothing, and
`R_branch_is_trivial` says the `ℝ` branch has no period.  So the two readings the
development carried side by side are not alternatives: **the `ℝ` branch is the
flat degeneration of the `𝕋` branch**, and everything gravitational lives in the
latter.

This is what dissolves the `Codimension.lean` collision registered in
`Audit.lean` §I: those theorems are true of the `𝕋` branch's *scalar* shadow, and
the framework's scale is directional, but the branches themselves were never in
conflict. -/
theorem gravity_selects_T_branch (D : Defect.ScaleDefect (0 : ℝ))
    {A : Type*} [CommRing A] {n : ℕ} [ScaleAlgebra n A] (ν σ : A)
    (hlin : gradsq n σ = 0) (h : Index.IndexResponse n (0 : A) ν σ) :
    Defect.ScaleDefect.IsTrivial D ∧ RscBare n σ = 0 :=
  ⟨R_branch_is_trivial D, Index.no_period_no_gravity ν σ hlin h⟩

/-! ## II. W2 — monodromy is a change of unit

Going around a defect does not take you anywhere.  It changes the unit you came
back with, by a quantised amount.  That is a genuinely new kind of non-locality
and it has no analogue in the `ℝ` branch. -/

/-- **A circuit shifts the log-scale by a whole number of periods**, so the unit
you return with differs from the one you left with by `e^{kΔ}`.

The word to avoid here is "shortcut": nothing has moved.  What has happened is
that the *ruler* has changed, which is exactly what a scale is. -/
theorem monodromy_shifts_the_unit {Δ : ℝ} (D : Defect.ScaleDefect Δ) (x : ℝ) :
    Real.exp (D.lift (x + 1)) = Real.exp ((D.winding : ℝ) * Δ) * Real.exp (D.lift x) := by
  rw [D.quasiperiodic x, Real.exp_add]
  ring

/-- **The shift composes additively over circuits**, so the monodromy is a
homomorphism from loops to `ℤ` — an index, not a magnitude.  This is why
`Index.enclosed_charge_additive` can treat the source as a count. -/
theorem monodromy_additive {Δ : ℝ} (D E : Defect.ScaleDefect Δ) :
    (D.combine E).winding = D.winding + E.winding :=
  Defect.ScaleDefect.combine_winding D E

/-- **And it is trivial exactly when there is no period.**  So W2 exists in the
`𝕋` branch and nowhere else. -/
theorem monodromy_trivial_iff_no_period {Δ : ℝ} (D : Defect.ScaleDefect Δ)
    (hw : D.winding ≠ 0) (h : ∀ x, D.lift (x + 1) = D.lift x) : Δ = 0 := by
  have h1 := D.quasiperiodic 0
  rw [h 0] at h1
  have hz : (D.winding : ℝ) * Δ = 0 := by linarith
  rcases mul_eq_zero.mp hz with hk | hd
  · exact absurd (by exact_mod_cast hk) hw
  · exact hd

/-! ## III. W3 — the fibre over a bare place is a `ℤ`-torsor

The deepest of the three, and the one that earns the word.  In the `𝕋` branch the
log-scale is a section of a covering, so a single bare location does not
determine the unit: the possible units over it differ by whole periods, and they
are physically distinguishable because `Light.scale_determined_of_nonnull` says
matter reads the scale.

There is no second region and no throat.  What there is is that **"where you are"
does not determine "what your unit is"**. -/

/-- The **fibre** over a bare place with base log-scale `σ₀`: the units reachable
from it, indexed by how many periods have been accumulated. -/
noncomputable def fibre (Δ σ₀ : ℝ) (k : ℤ) : ℝ := Real.exp (σ₀ + (k : ℝ) * Δ)

/-- **The fibre is a `ℤ`-torsor**: moving by `j` periods and then by `k` is
moving by `j + k`, and every element is reachable from every other. -/
theorem fibre_is_a_torsor (Δ σ₀ : ℝ) (j k : ℤ) :
    fibre Δ σ₀ (j + k) = Real.exp ((j : ℝ) * Δ) * fibre Δ σ₀ k := by
  simp only [fibre]
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- **Distinct sheets are distinct units.**  With a nonzero period, different
winding numbers give different scales over the *same* bare place, so the fibre is
not a formality: its points are physically distinguishable by
`Light.scale_determined_of_nonnull`. -/
theorem fibre_injective {Δ : ℝ} (hΔ : Δ ≠ 0) (σ₀ : ℝ) {j k : ℤ}
    (h : fibre Δ σ₀ j = fibre Δ σ₀ k) : j = k := by
  simp only [fibre] at h
  have h' : σ₀ + (j : ℝ) * Δ = σ₀ + (k : ℝ) * Δ := Real.exp_injective h
  have : (j : ℝ) * Δ = (k : ℝ) * Δ := by linarith
  exact_mod_cast mul_right_cancel₀ hΔ this

/-- **And the torsor has no preferred origin**, which is A5 again: the fibre is
acted on simply transitively by `ℤ`, so there is no distinguished sheet, only
differences of sheets.

That is why W3 is a *scale* structure and not a *spatial* one: what is physical
is the number of periods **between** two states, never the absolute sheet. -/
theorem fibre_no_fixed_origin (Δ σ₀ : ℝ) (j k : ℤ) :
    fibre Δ σ₀ j / fibre Δ σ₀ k = Real.exp (((j : ℝ) - (k : ℝ)) * Δ) := by
  simp only [fibre]
  rw [← Real.exp_sub]
  congr 1
  ring

/-- **Collected: W3, and what it is not.**

Over one bare place the `𝕋` branch supplies a `ℤ` of physically distinct units,
freely and transitively permuted by the period.  Traversing between sheets is a
move in the torsor.

It is **not** a GR wormhole: there is no second region, no throat, and no
topology change in space.  It is a failure of the bare location to determine the
unit — which is the framework's own kind of non-locality, and by
`Well.stretch_ne_zero` every move between sheets has strictly positive measured
length. -/
theorem W3_summary {Δ : ℝ} (hΔ : Δ ≠ 0) (σ₀ : ℝ) :
    (∀ j k : ℤ, fibre Δ σ₀ (j + k) = Real.exp ((j : ℝ) * Δ) * fibre Δ σ₀ k)
    ∧ (∀ j k : ℤ, fibre Δ σ₀ j = fibre Δ σ₀ k → j = k) :=
  ⟨fibre_is_a_torsor Δ σ₀, fun _ _ h => fibre_injective hΔ σ₀ h⟩

end SCD.Dual
