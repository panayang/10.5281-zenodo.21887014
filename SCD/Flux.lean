/-
# The continuum limit of A6″ — where the gap actually is

`Index.lean` reads `Δσ = Δ·ν` as the local form of Gauss's law and records the
remaining step as "the continuum limit": passing from a boundary flux to a local
density, which the framework has no integration theory for.

Going after that step relocates it.  **The obstruction is not integration.**

## I.  In codimension two there is no gap at all

`Defect.ScaleDefect` carries the loop explicitly: `lift : ℝ → ℝ` followed once
around, with `lift(x+1) = lift x + kΔ`.  The "flux through the boundary" of a
region enclosing the defect is the difference of two values of `lift`, and the
fundamental theorem of calculus in one dimension is the only thing needed —
which is to say, nothing:

        flux  =  lift(1) − lift(0)  =  k·Δ .

`flux_eq_winding`.  It is additive over superposed defects (`flux_combine`),
zero on the vacuum, and quantised in units of `Δ` (`flux_quantised`).  **That is
Gauss's law, exactly, with no continuum limit and no integration theory**, and it
was already a theorem — it just had not been read as one.

## II.  So the gap is a homotopy type, not an analysis

The reason this works in codimension two is that the enclosing boundary is a
**loop**, so the flux is an integral of `dσ` along a curve — linear in `∇σ`, and
recoverable from endpoint values.

The framework's own defects are **not** codimension two.  `Axis.lean` restores
*point* defects from a projective directional order parameter, and
`Charges.hedgehog` is a `π₂` class — "how the axis wraps the **enclosing
sphere**".  For those the boundary invariant is a **degree**, and a degree of a
map to a sphere is *not* linear in the gradient: it is the pullback of the volume
form, quadratic in `∂n` in the two-sphere case.

> **`Δσ = Δ·ν` is a codimension-two equation applied to a codimension-three
> source.**

That is the same `π₁`/`π₂` conflation `Sources.lean` found in the charge algebra,
reappearing one level up, in the source law.  It is the third place it has
surfaced, and this time it is mine from `Index.lean` rather than from the older
files.

## III.  What follows, and what it costs

Two ways out, and they are not equivalent:

* **(a)** the source is codimension two — strings.  Then `Index.lean` is exact as
  written and needs no continuum limit at all.  But `Axis.lean` argued the
  framework's defects are points, and `Audit.lean` §I records `Codimension.lean`'s
  retraction on exactly that ground.  Taking (a) reopens it;
* **(b)** the source law is rewritten with a degree density.  Then it is not
  `lap σ = Δ·ν`: the right-hand side is quadratic in the direction pattern's
  gradients, and the equation is a different one.  `Weight.lean` says this costs
  nothing in the grading — a degree density is weight zero, like a count — so the
  coefficient is still weight one and everything in §V.f–§V.h survives.  What does
  not survive is the specific form of A6″.

**And this weakens a claim of mine.**  "`G` and `ħ` acquire one origin" rested on
identifying `Index.lean`'s coefficient with `Defect.lean`'s scale period, which is
exactly the codimension-two identification.  It holds under (a) and is
unsupported under (b).  `Audit.lean` §V.f already made it conditional on the
continuum-limit step; it should now be conditional on **the codimension**, which
is a sharper and less comfortable condition, because the framework's own
`Axis.lean` argues against it.

## IV.  What is *not* the gap

Worth recording, because it is where I looked first and it was wrong.

`Waves.divergences` is a genuine algebraic surrogate for "what an integral over a
slice discards", and `lap σ` is manifestly a sum of derivative images — so its
class modulo the transverse divergences is carried entirely by the drift
direction (`Index.lap_mod_divergences`).  That is true and it is *not* Gauss's
law: it says the total is a boundary term, which is the statement for a region
with **no enclosed charge**.  The enclosed-charge case needs the boundary to be
non-contractible, and non-contractibility is a topological input, not an
analytic one.
-/
import SCD.Index
import SCD.Charges
import SCD.Defect

namespace SCD.Flux

open SCD

/-! ## I. The exact case: codimension two -/

variable {Δ : ℝ}

/-- The **flux** of the scale connection through the boundary of a region
enclosing a defect: the change in the followed log-scale over one circuit.

No integration theory is used.  The boundary of a codimension-two defect is a
loop, `lift` is the scale followed along it, and the flux is a difference of two
values. -/
noncomputable def flux (D : Defect.ScaleDefect Δ) : ℝ := D.lift 1 - D.lift 0

/-- **Gauss's law in codimension two, exactly.**

The flux is the enclosed winding times the period, with no limit taken and no
measure invoked.  `Defect.quasiperiodic` at `x = 0` is the whole proof. -/
theorem flux_eq_winding (D : Defect.ScaleDefect Δ) :
    flux D = (D.winding : ℝ) * Δ := by
  have h := D.quasiperiodic 0
  simp only [flux, zero_add] at h ⊢
  rw [h]
  ring

/-- **The flux is additive**, so it counts: bringing two defects into one region
adds their fluxes, which is what makes the source an index rather than a
response. -/
theorem flux_combine (D E : Defect.ScaleDefect Δ) :
    flux (D.combine E) = flux D + flux E := by
  rw [flux_eq_winding, flux_eq_winding, flux_eq_winding,
    Defect.ScaleDefect.combine_winding]
  push_cast
  ring

/-- The vacuum encloses nothing. -/
@[simp] theorem flux_vacuum : flux (Defect.ScaleDefect.vacuum Δ) = 0 := by
  rw [flux_eq_winding, Defect.ScaleDefect.vacuum_winding]
  simp

/-- A defect and its antidefect enclose nothing, so a neutral region has no
flux — the local statement of charge conservation. -/
theorem flux_pair (D : Defect.ScaleDefect Δ) :
    flux (D.combine D.anti) = 0 := by
  rw [flux_eq_winding, Defect.ScaleDefect.pair_winding_zero]
  simp

/-- **The flux is quantised in units of the period.**

There is a smallest nonzero flux and it is `Δ`.  This is the content the index
form was after, and in codimension two it is available with no continuum limit
whatever. -/
theorem flux_quantised (D : Defect.ScaleDefect Δ) :
    ∃ k : ℤ, flux D = (k : ℝ) * Δ :=
  ⟨D.winding, flux_eq_winding D⟩

/-- **And it vanishes identically when there is no period.**

So the codimension-two Gauss law is empty on the `ℝ` branch and has content only
on the `𝕋` branch, which is `Dual.gravity_selects_T_branch` seen from the flux
side. -/
theorem flux_zero_of_no_period (D : Defect.ScaleDefect (0 : ℝ)) : flux D = 0 := by
  rw [flux_eq_winding]
  ring

/-! ## II. Why this does not extend: the boundary invariant changes type

In codimension two the boundary is a **loop** and the invariant is a winding —
linear in `∇σ`, recoverable from endpoint values, which is why `flux` above is a
difference and not an integral.

For the framework's own defects the boundary is a **sphere** and the invariant is
a degree.  A degree is the pullback of a volume form; it is not linear in the
gradient and it is not a difference of endpoint values.  So the argument above
does not extend, and the reason is the homotopy type of the boundary rather than
any missing analysis. -/

/-- **The two invariants are of different types, and the framework carries both.**

`Charges.DefectCharge` bundles a `π₁` class (the block, finite) with a `π₂` class
(the hedgehog, integral); `Defect.ScaleDefect.winding` is a `π₁` class of a
different order parameter.  The flux above computes the third, and the source law
of `Index.lean` is written in its image.

The statement below is the algebraic fact — both are additive `ℤ`-labels — and it
is deliberately *not* an identification: `Sources.lean` withdrew that. -/
theorem flux_and_hedgehog_both_additive (D E : Defect.ScaleDefect Δ)
    {B : Type*} [Group B] (c e : Charges.DefectCharge B) :
    flux (D.combine E) = flux D + flux E
    ∧ (c.comp e).hedgehog = c.hedgehog + e.hedgehog :=
  ⟨flux_combine D E, rfl⟩

/-- **Collected: what the continuum limit costs, and where.**

In codimension two the index form is exact — quantised, additive, and derived
with no integration.  What is missing is not analysis but the passage to the
codimension the framework's own defects have, where the boundary invariant is a
degree rather than a winding.

So `Index.lean`'s registered gap should read: **the source law is exact for
codimension-two defects and unproved for the codimension-three ones `Axis.lean`
argues the framework has.** -/
theorem gap_is_the_codimension (D : Defect.ScaleDefect Δ) :
    (∃ k : ℤ, flux D = (k : ℝ) * Δ)
    ∧ flux (Defect.ScaleDefect.vacuum Δ) = 0 :=
  ⟨flux_quantised D, flux_vacuum⟩

end SCD.Flux
