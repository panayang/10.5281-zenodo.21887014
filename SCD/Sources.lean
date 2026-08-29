/-
# Three things called "the source", and why none of them fixes the coupling

The geometric mass tower, the mass spectrum and the undetermined `Δρ` are one
problem, and this file names it.  It also refutes the escape I proposed for it,
which is the more useful half.

## I. The conflation

Three integers have been used interchangeably as "the charge that sources the
geometry", and they are three different invariants of two different order
parameters:

| name | order parameter | homotopy | carried by |
|---|---|---|---|
| `Defect.ScaleDefect.winding` | circle-valued **scalar** scale `S¹` | `π₁ = ℤ` | the **magnitude** |
| `Charges.DefectCharge.block` | projective **directional** axis `ℝP²` | `π₁ = ℤ/2` | the direction |
| `Charges.DefectCharge.hedgehog` | the same `ℝP²` | `π₂ = ℤ` | the **direction** |

`Charges.lean` says of the third, in its own docstring, "how the axis wraps the
**enclosing sphere**"; `Defect.lean` says of the first, "the log-scale read
**around a loop**".  A sphere and a loop.

**My error, from the unification pass.**  `Defect.toCharge` sends the winding to
the `hedgehog` slot and its docstring claims the two files describe "one charge
algebra, not two".  That is a `π₁` object in a `π₂` slot.  What the maps actually
prove is that both are additive `ℤ`-labels — an algebraic fact — and the physical
identification is withdrawn here and in `Audit.lean`.

**And it matters for scope.**  `Audit.lean` §I already records that the
circle-valued *scalar* scale does not describe this framework: A4 is directional,
and `Axis.lean` replaces the winding picture with the projective one.  So
`Defect.lean`'s `Δ` — an `ℝ`-valued period of a scalar scale — belongs to a
picture the register has already scoped out, and `Index.lean` built its
coefficient on it.

## II. Why the three failures are one failure

* the **geometric tower** assigns mass by *winding*, i.e. makes the threshold a
  function of a topological label.  `Particle.Species` carries threshold and
  charge as **separate** labels and nothing links them, so the tower contradicts
  the framework's own label structure and not merely the data;
* the **spectrum** measures `CV²` of a *process*.  It can refute a consequence of
  the tower (equal gaps) but it cannot test a relation between labels;
* **`Δρ`** is the ratio of a period (from the scoped-out scalar picture) to a
  threshold density (a live measurement).  Expecting the framework to fix it is
  expecting it to relate two independent labels.

## III. The escape I proposed, and its refutation

I suggested that sourcing the geometry with the `π₂` degree instead of the `π₁`
winding would remove the free constant, because a degree is normalised by the
volume of the direction sphere — a fixed pure number — while a winding is
normalised by the scale circle's circumference, which is a free magnitude.

**That is wrong, and `source_coefficient_scales` is why.**  Any law of the shape

        Δσ  =  C · ν      with `ν` a dimensionless count

has, under `σ ↦ cσ`, the response `Δσ ↦ c·Δσ` while `ν` does not move.  So
`C ↦ cC`: **the coefficient carries the unit, whatever the count counts.**
Changing `π₁` for `π₂` for a threshold tally changes what `ν` means and changes
nothing about `C`.

So the free number is not a gap in anyone's cleverness.  It is forced by the
*shape* of a law that couples a count to a scale, and there is exactly one such
coupling, so exactly one free number.  That is `Dimension.only_ratios_are_fixed`
arriving from a new direction, and it sharpens what the free number *is*: not
"the magnitude of the scale pattern" but **the conversion from counting to
scale**.

## IV. What would give a prediction — and the framework has the second half

A single count-to-scale coupling can always be absorbed into the unit.  **Two**
of them cannot: their ratio is invariant and is a pure number the framework could
predict.

There is a second coupling in the development — `Running.invSqCoupling` shifts a
gauge coupling by `κ` per resolvable defect — and I proposed `Δ / κ_run` as the
target.

**That proposal is withdrawn; see `Weight.lean`.**  `couplings_scale_together`
below proves `invSqCoupling` is **linear in `(u₀, κ)`**, and I read it as a
statement about the rescaling `σ ↦ cσ`.  It is not one.  Doing that computation
properly (`Weight.invSqCoupling_invariant`) shows the gauge coupling is invariant
with `κ` *untouched*: `κ_run` has weight **zero**, `Δ` has weight one, and their
ratio has weight one.  Not a pure number.

What the correct bookkeeping gives instead is better than the target was:
**gravity is the only interaction whose law crosses the grading**, which is why
its coefficient is the unit and gauge couplings are pure numbers
(`Weight.only_gravity_crosses_the_weight`), and why the framework predicts the
weight-zero sector and nothing else.
-/
import SCD.Index
import SCD.Running
import SCD.Charges
import SCD.Defect
import SCD.Particle

namespace SCD.Sources

open SCD ScaleAlgebra

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-! ## I. Rescaling the scale, and what moves with it -/

/-- A constant of the substrate: killed by every derivation.  Rescaling the
log-scale by such a constant is the operation the whole section is about. -/
theorem lap_const_mul (c σ : A) (hc : ∀ i : Fin n, d i c = 0) :
    lap n (c * σ) = c * lap n σ := by
  have hh : ∀ i j : Fin n, hess (c * σ) i j = c * hess σ i j := by
    intro i j
    show d i (d j (c * σ)) = c * d i (d j σ)
    rw [d_mul, hc j, zero_mul, zero_add, d_mul, hc i, zero_mul, zero_add]
  simp only [lap, hh, ← Finset.mul_sum]

/-- **The source coefficient carries the unit, whatever the source counts.**

Rescaling the log-scale by `c` rescales the Laplacian by `c` and leaves a
dimensionless count untouched, so the coefficient must absorb the factor.  This
holds for any `ν` — a `π₁` winding, a `π₂` degree, a threshold tally — so **no
choice of charge removes the free constant.**

This refutes the proposal that using the degree, whose normalisation is the fixed
volume of the direction sphere, would fix the coupling. -/
theorem source_coefficient_scales (c C ν σ : A) (hc : ∀ i : Fin n, d i c = 0)
    (h : Index.IndexResponse n C ν σ) :
    Index.IndexResponse n (c * C) ν (c * σ) := by
  show lap n (c * σ) = (c * C) * ν
  rw [lap_const_mul c σ hc]
  have hl : lap n σ = C * ν := h
  rw [hl]
  ring

/-- **So the coefficient is not invariant, and is therefore the unit.**

Two rescalings of the same configuration give coefficients differing by the
rescaling factor.  A quantity that moves under a redescription of the scale is
not a prediction; it is what the predictions are expressed in. -/
theorem coefficient_is_not_invariant (c C ν σ : A) (hc : ∀ i : Fin n, d i c = 0)
    (h : Index.IndexResponse n C ν σ) :
    Index.IndexResponse n C ν σ ∧ Index.IndexResponse n (c * C) ν (c * σ) :=
  ⟨h, source_coefficient_scales c C ν σ hc h⟩

/-! ## II. The second coupling, and the ratio that survives

`Running.invSqCoupling` shifts a gauge coupling by `κ` per resolvable defect.
That is a count-to-scale conversion of the same kind as the source coefficient,
so it carries the same weight — and a ratio of two weight-one quantities is
weight zero. -/

/-- **Linearity of the accumulated response in `(u₀, κ)`.**

**Do not read this as a weight.**  It says that scaling both the base coupling
and the per-defect response by `c` scales the total by `c`, which is linearity
and nothing more; it makes no statement about the rescaling `σ ↦ cσ`.  I read it
as one, and `Weight.invSqCoupling_invariant` does the actual computation:
`κ_run` has weight zero. -/
theorem couplings_scale_together (c u₀ κ ρ t₀ t : ℝ) :
    Running.invSqCoupling (c * u₀) (c * κ) ρ t₀ t
      = c * Running.invSqCoupling u₀ κ ρ t₀ t := by
  simp only [Running.invSqCoupling, Running.resolvedCount]
  ring

/-- Arithmetic, retained because it is used to state the withdrawal: *if* two
quantities had the same weight their ratio would be invariant.  `Weight.lean`
shows `Δ` and `κ_run` do **not**. -/
theorem coupling_ratio_invariant (c Δ κ : ℝ) (hc : c ≠ 0) :
    (c * Δ) / (c * κ) = Δ / κ :=
  mul_div_mul_left Δ κ hc

/-- Stated without division, so it is an identity rather than a computation:
the cross-product of the two couplings is unchanged by rescaling. -/
theorem coupling_cross_product (c Δ κ : ℝ) :
    (c * Δ) * κ = Δ * (c * κ) := by ring

/-! ## III. The three sources, kept apart

The maps below are true and are retained; what is withdrawn is the *reading* that
made them identifications.  `Defect.ScaleDefect.winding` and
`Charges.DefectCharge.hedgehog` are both additive `ℤ`-labels, and that is all
they share: one is `π₁` of a circle-valued scalar scale, the other `π₂` of a
projective directional axis. -/

/-- **Both are additive, and that is the whole of the resemblance.**

`Defect.combine_winding` and `Charges.comp_hedgehog` say the same algebraic
thing.  Neither says the two integers are the same invariant, and they are not:
a loop class and a sphere class of two different order parameters. -/
theorem both_additive {Δ : ℝ} (D E : Defect.ScaleDefect Δ)
    {B : Type*} [Group B] (c e : Charges.DefectCharge B) :
    (D.combine E).winding = D.winding + E.winding
    ∧ (c.comp e).hedgehog = c.hedgehog + e.hedgehog :=
  ⟨Defect.ScaleDefect.combine_winding D E, rfl⟩

/-- **And the threshold is a third label, independent of both.**

`Particle.Species` carries a threshold and a charge as separate fields.  The
geometric mass tower assumed the first was a function of the second; nothing in
the framework says so, which is why its failure was structural and not merely
empirical. -/
theorem threshold_independent_of_charge (t : ℝ) (c₁ c₂ : Particle.Charge) :
    (⟨t, c₁⟩ : Particle.Species).threshold = (⟨t, c₂⟩ : Particle.Species).threshold :=
  rfl

end SCD.Sources
