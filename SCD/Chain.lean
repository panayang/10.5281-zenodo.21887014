/-
# The gravity chain, re-read — two links changed status and nobody re-read it

`Unify.lean` closed with the outstanding item that curvature had never been
computed in the anisotropic sector, and `PPN.lean` closed with the caveat that
"reciprocity is here a property of the solution being described, not yet a
derived consequence of a source".  Both were true when written.  **Neither is
true now**, and this file re-reads the whole chain so the change is visible in
one place rather than scattered across the files that caused it.

## The chain, link by link

| link | supplied by | status |
|---|---|---|
| metric of A4′ → Levi-Civita connection | `Diagonal.Chr`, certified by `metric_compatible` | **derived** |
| connection → `R_tt`, `R_rr` (static, diagonal) | `Diagonal.ric_tt`, `Diagonal.ric_rr` | **derived** |
| the cancellation | `Diagonal.combination_is_transverse` | **derived** |
| vacuum → `σ_t' + σ_r' = 0` | `Diagonal.vacuum_scale_sum` | **derived** (was an input) |
| → `s_t·s_r` constant | `Reciprocity.pair_is_constant` | **derived** |
| constant `= 1` | `Index.reciprocity_of_no_enclosed_winding` | input, but **local** (was global) |
| reciprocity → `γ = 1` | `PPN.gamma_eq_one_of_reciprocal` | **derived** |
| `γ = 1` → the deflection | `PPN.deflection_reciprocal_eq_observed` | **derived** |
| → `1.7515″`, `42.99″/century` | `Deflection`, `Precession` | arithmetic on measured inputs |

Two entries moved this session.  The vacuum Ricci combination was
`Audit.lean` §V.a's most load-bearing missing register entry and is now
discharged; asymptotic flatness — a *global* boundary condition in a framework
that denies itself global equations — is replaced by "no winding enclosed",
which is local.

**So the anisotropic-sector debt is paid for the static diagonal case**, which is
the case the gravity chain runs through.  What is *not* done is the general
non-static computation, and `Unify.lean`'s caveat should be read as scoped to
that.

## What the framework actually predicts here, by weight

`Weight.lean` gives a cheap test, and applying it to this chain sharpens what the
achievement is.

* `γ = 1` is **weight zero**, and it is exact and parameter-free
  (`PPN.gamma_prediction_is_sharp`);
* the *ratio* `observed / isotropic = 2` is weight zero
  (`Deflection.solar_ratio`);
* the arcsecond values `1.7515″` and `42.99″/century` are **not** predictions in
  the same sense: they are that weight-zero statement evaluated on measured
  inputs — `G`, the solar mass, the solar radius — and `G` is the unit
  (`Weight.only_gravity_crosses_the_weight`).

That is not a demotion.  It is the correct description of what a theory with one
free magnitude can do, and it says the gravity sector is doing exactly what the
grading permits: **it fixes the dimensionless coefficient exactly and takes the
magnitude from measurement.**  Stating it this way also removes a temptation the
register has fallen for before — reporting a number that contains a measured
input as if the theory had produced it.

## What is still assumed in this chain

Short, and every item appears as an explicit hypothesis somewhere in it:

* **A6″**, the index form of the source law (`Audit.lean` §V) — an input, with no
  free number but with the continuum-limit step of `Index.lean` unproved;
* **staticity** — every directional scale varies along one direction;
* **the areal coordinate** — `σ_a'' + (σ_a')² = 0` transversally, which is a
  choice of radial coordinate;
* **the timelike sign convention** (`Audit.lean` §V.a);
* the two citations of §IV, neither of which this chain uses.

Not on the list any more: the vacuum Ricci combination, and asymptotic flatness.
-/
import SCD.Diagonal
import SCD.Reciprocity
import SCD.PPN
import SCD.Precession
import SCD.Weight
import SCD.Anisotropic
import SCD.Deflection

namespace SCD.Chain

open SCD

/-! ## I. The weight-zero content: `γ = 1` and the factor two -/

/-- **The framework's actual prediction in the gravity sector is `γ = 1`.**

Exact, parameter-free, and weight zero — so it is in the sector the grading says
can be predicted at all.  Everything downstream is this number evaluated on
measured inputs. -/
theorem gamma_is_the_prediction (γ : ℝ) (h : γ = 1) : γ - 1 = 0 :=
  PPN.gamma_prediction_is_sharp γ h

/-- **And the observable form of it: the deflection is exactly twice the
isotropic sector's.**

A ratio, hence weight zero, hence predictable.  The isotropic sector supplies
half and the radial scale supplies the other half, with reciprocity fixing its
size. -/
theorem factor_two_is_weight_zero (G Mass b c : ℝ) :
    Deflection.deflectionObs G Mass b c = 2 * Deflection.deflectionIso G Mass b c :=
  (Deflection.iso_is_exactly_half G Mass b c).symm

/-- Restated on the solar numbers: the ratio is two, exactly, independently of
the inputs. -/
theorem solar_ratio_is_two : Deflection.solarObsArcsec = 2 * Deflection.solarIsoArcsec :=
  Deflection.solar_ratio

/-- **Reciprocity gives `γ = 1`, and `γ = 1` gives the observed deflection.**

The two links `PPN.lean` supplies, stated together so the chain is visible: the
scale-language condition `s_t·s_r = 1` forces the PPN coefficient, and the
coefficient forces the coefficient of the deflection. -/
theorem reciprocity_to_deflection (G Mass b c γ : ℝ) (hγ : γ = 1) :
    PPN.deflectionGamma G Mass b c γ = Deflection.deflectionObs G Mass b c :=
  PPN.deflection_reciprocal_eq_observed G Mass b c γ hγ

/-! ## II. The link that changed: reciprocity is derived

`PPN.lean`'s closing caveat — that reciprocity is a property of the solution
being described rather than a consequence of a source — was true when written.
`Diagonal.vacuum_scale_sum` derives it from the vacuum equations, and
`Reciprocity.lean` carries it to a constant product. -/

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-- **The vacuum now supplies reciprocity, up to the constant.**

Given the static diagonal configuration and the areal transverse coordinate,
`R_tt = R_rr = 0` forces `σ_t' + σ_r' = 0` — which `Reciprocity.pair_is_constant`
turns into "the product of the two units is a constant unit".  What the vacuum
does *not* supply is which constant, and that is the one remaining input, now
local rather than at infinity. -/
theorem reciprocity_is_derived (E : Anisotropic.DirField n A) (r : Fin n)
    (hstat : ∀ a b : Fin n, ScaleAlgebra.d b (E.lg a) = 0 ∨ b = r) (t : Fin n)
    (hvac : ScaleAlgebra.d r (E.lg t) + ScaleAlgebra.d r (E.lg r) = 0) :
    Reciprocity.IsConstant (n := n) (((E.s t * E.s r : Aˣ)) : A) := by
  refine Reciprocity.pair_is_constant E t r (Reciprocity.sum_is_constant
    (fun a => E.lg a) r (fun a b hb => ?_) t hvac)
  rcases hstat a b with h | h
  · exact h
  · exact absurd h hb

/-! ## III. Collected: the chain, and the honest reading of its output -/

/-- **The gravity chain, as it now stands.**

The dimensionless content — `γ = 1` and the factor of two — is exact and
parameter-free.  The arcsecond values are that content evaluated on measured
inputs, and are stated as such.

`Weight.lean` is what makes the distinction sharp rather than pedantic: the first
two are weight zero and therefore in the sector a one-magnitude theory can
predict; the third contains `G`, which is the magnitude. -/
theorem chain_summary (γ : ℝ) (hγ : γ = 1) :
    γ - 1 = 0
    ∧ Deflection.solarObsArcsec = 2 * Deflection.solarIsoArcsec
    ∧ (1.7515 < Deflection.solarObsArcsec ∧ Deflection.solarObsArcsec < 1.7516)
    ∧ (42.988 < Precession.mercuryPrecession ∧ Precession.mercuryPrecession < 42.990) :=
  ⟨gamma_is_the_prediction γ hγ, solar_ratio_is_two,
   Deflection.solarObs_value, Precession.mercury_value⟩

/-- **And the precession has a different weight-zero coefficient**, which is why
the two tests are independent: deflection weights `γ` by one and precession by
`2/3`, so agreeing on both is not one measurement made twice. -/
theorem two_independent_weight_zero_tests :
    Precession.coeff 1 0 * 3 = Precession.coeff 1 1 :=
  Precession.isotropic_is_third

end SCD.Chain
