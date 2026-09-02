/-
# The bridge: reading the algebra along the drift

`RateWeight.lean` left one thing between the framework and a cross-domain
prediction, and left it at the level of the types: `Index.IndexResponse` is
ring-valued, `lap σ = Δ·ν`; `Response.FactorsThroughCount` is real-valued,
`ΔD = κ·ΔN`.  Same shape, different types.  What was missing was a way to carry
an equation from one to the other.

`DriftEval` is that, and it asks for **one** property.

## What it asks

A reading `val : A → ℝ → ℝ` of ring elements along the scale axis, such that the
source coefficient reads as a **constant**: `val (Δ·x) t = κ · val x t`.

Nothing else — not linearity, not continuity.  Asking for less matters, because
every property demanded of a bridge is a property some model has to supply, and
the first draft of this file asked for two and needed one.

## What it gives, and it is more than transport

`factorsThroughCount_of_indexResponse`: **given a drift evaluation, the scanning
hypothesis is a theorem.**

`Response.lean` calls factorisation through the count a *proposal*, and shows A5
and the weight grading do not force it — `weight_zero_does_not_force_constancy`
exhibits a response that satisfies every constraint the framework imposes and
does not factor.  Those constraints do not force it.  **The index law does**,
once the algebra can be read: `lap σ = Δ·ν` becomes `ΔD = κ·ΔN` after reading,
and the proportionality is **one**, because both sides carry the image of the
same `Δ`.

That is precisely the residue `RateWeight.lean` isolated.  With it,
`RateWeight.prediction_at_unit_factor` applies: `Δρ = −λ/6`, and the
gravitational coupling follows from a cosmological rate and the mass spectrum's
threshold density.

## And the bridge is inhabited

`polyDriftEval`: polynomials *are* functions, evaluation along a line is a ring
homomorphism, and a coupling is a constant polynomial.  So the structure is not
an empty hypothesis.

## What is still not established, and it is three things

* **the witness is over `MvPolynomial`**, where — by `ExpPoly.lean`'s whole
  argument — the units are constants and there is **no non-constant scale
  field**.  So `DriftEval` is shown *inhabited*, not shown to coexist with A2's
  varying scale.  `Witness.lean`'s "compatible is not forced" applies, twice
  over: once for the bridge and once for the pair;
* **`coeff_const` is doing real work.**  In the witness it holds because `Δ` is
  literally a constant polynomial.  Whether a genuine scale *period* reads as a
  constant along the drift is not established, and that is the property a serious
  model would have to earn;
* **and the far end is still an identification.**  The bridge produces a function
  of type `ℝ → ℝ` satisfying factorisation.  That *that* function is what a
  `w₀wₐ` fit measures remains one of the two identifications `Anchor.lean` names
  and neither is formalised.

## So the honest accounting

`Anchor.lean` records the `w`/`H₀` link as **three inputs deep**: the scanning
hypothesis, plus two unformalised identifications.  This removes the first.

> **Two inputs deep, not three** — and the one removed was the one the framework
> could remove, since the other two are about what an astronomical fit measures
> and no amount of algebra decides that.

No number is offered, for the reason `RateWeight.lean` gave: the unit bookkeeping
between the framework's scale-axis time and cosmological time has not been done.
-/
import SCD.RateWeight
import SCD.Index
import SCD.Response

namespace SCD.Bridge

open SCD MvPolynomial


variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-- **A drift evaluation**: a reading of the algebra along the scale axis.

This is the bridge `RateWeight.lean` said was missing — the two laws have the
same shape and different types, one ring-valued and one real-valued, and this is
what would carry an equation from the first to the second.

It asks for **one** thing: that the source coefficient reads as a *constant* `κ`.
Nothing else is needed — not linearity, not continuity — and asking for less is
the point, since every property demanded of the bridge is a property some model
must supply.  A coefficient that varies along the drift is not a coupling, and
that is the whole content. -/
structure DriftEval (n : ℕ) (A : Type*) [CommRing A] [ScaleAlgebra n A]
    (Δ : A) (κ : ℝ) where
  /-- The value of a ring element at log-scale `t`. -/
  val : A → ℝ → ℝ
  /-- The coefficient reads as a constant. -/
  coeff_const : ∀ (x : A) (t : ℝ), val (Δ * x) t = κ * val x t

/-- **Given a drift evaluation, the scanning hypothesis is a theorem.**

`Response.lean` calls factorisation through the count a *proposal* and says A5
and the weight grading do not force it.  They do not — but the **index law**
does, once the algebra can be read along the drift: `lap σ = Δ·ν` is exactly
`ΔD = κ·ΔN` after reading, with the proportionality **one** because both sides
carry the image of the same `Δ`.

That is the bridge doing its job: not a new assumption, but the transport of one
the framework already has. -/
theorem factorsThroughCount_of_indexResponse {Δ : A} {κ : ℝ}
    (E : DriftEval n A Δ κ) (ν σ : A) (h : Index.IndexResponse n Δ ν σ) :
    Response.FactorsThroughCount (E.val (lap n σ)) (E.val ν) κ := by
  intro t t'
  rw [h, E.coeff_const, E.coeff_const]
  ring

/-! ## And the structure is inhabited -/

/-- **A drift evaluation on the polynomial model.**

Polynomials *are* functions, so reading them along a line is evaluation, and
evaluation is a ring homomorphism — which gives both properties at once.  The
coefficient is a constant polynomial, which is what "a coupling" means here. -/
noncomputable def polyDriftEval (m : ℕ) (d : Fin m → ℝ) (κ : ℝ) :
    DriftEval m (MvPolynomial (Fin m) ℝ) (MvPolynomial.C κ) κ where
  val f t := MvPolynomial.eval (fun i => t * d i) f
  coeff_const x t := by simp


end SCD.Bridge
