/-
# Witnesses: the structures are inhabited, and by objects satisfying A1

An external audit found that six structures carrying load-bearing theorems were
never **constructed** anywhere in the development.  A theorem of the form "given
a structure `S`, …" is true but *unwitnessed* if nothing builds an `S`; its
physical reading is then a conditional, not a result.  The most consequential
case was `Crossed.ScaleShift`, the carrier of "`ħ` is an exact scale step".

This file builds them.  What that does and does not settle is stated first,
because the distinction is the whole point of the exercise.

## What a witness settles

* the theorems are **not vacuous** — there is something they apply to;
* the structure is **compatible with A1** — the same object can carry both, so
  the framework does not forbid it;
* in the `ScaleShift` case the shift is **exact and finite**, not a first-order
  truncation, which is what the original claim needed.

## What a witness does **not** settle

**It is not a derivation.**  Exhibiting one model that satisfies A1 and carries
a scale shift does not show the axioms *force* a scale shift; a different model
of A1 may have none.  So `ħ`'s identification with the step remains an
identification.  The audit's finding stands in that reduced form, and
`Audit.lean` §V.b now says so.

The gap between "compatible" and "forced" is real and is not closed here.

## The model

`ℝ[X]` with `d/dX` is the log-scale axis with its derivation: it satisfies A1
for `n = 1`.  The shift `X ↦ X + 1` is a ring homomorphism — **this is why the
construction works and why "multiply by the scale factor" does not**: for a unit
`u`, `(u·x)(u·y) = u²xy ≠ u(xy)`, so multiplication by a scale factor is
additive but not multiplicative and is *not* a `ScaleShift`.  Translation along
the scale axis is.

`shift_is_exact` shows the step is not infinitesimal: `Δ X = 1`, a finite
difference, not a derivative.  `shift_commutes_with_derivation` shows the two
structures are compatible rather than merely coexisting.
-/
import SCD.Crossed
import SCD.Invariant
import SCD.Direction
import SCD.RG
import SCD.Covariance
import SCD.Waves
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Trace

namespace SCD.Witness

open Polynomial

/-! ## I. The scale axis satisfies A1 -/

/-- **`ℝ[X]` with `d/dX` is a model of A1** for one direction: the log-scale
axis carrying its own derivation. -/
noncomputable instance polyScaleAlgebra : ScaleAlgebra 1 (Polynomial ℝ) where
  d := fun _ => Polynomial.derivative
  d_add := fun _ a b => Polynomial.derivative_add
  d_mul := fun _ a b => by simpa [mul_comm] using Polynomial.derivative_mul (p := a) (q := b)
  d_comm := fun _ _ _ => rfl

/-! ## II. And it carries an exact scale shift -/

/-- **The witness for `ScaleShift`: translation by one step along the scale
axis.**

A ring homomorphism, hence a legitimate `ScaleShift`.  Note what is *not* a
`ScaleShift`: multiplication by a scale factor `u`, since
`(u·x)(u·y) = u²xy ≠ u(xy)` — additive but not multiplicative.  The shift is the
translation, not the rescaling. -/
noncomputable def polyShift : Crossed.ScaleShift (Polynomial ℝ) where
  T := fun p => p.comp (X + 1)
  map_add := fun x y => by simp [add_comp]
  map_mul := fun x y => by simp [mul_comp]

/-- **The step is finite, not infinitesimal.**

`Δ X = (X+1) − X = 1`.  So the non-commutativity `Crossed.commutator_eq`
produces is exact, which is what the original claim required and what a
first-order deformation could not give. -/
theorem shift_is_exact : Crossed.delta polyShift X = 1 := by
  simp [Crossed.delta, polyShift]

/-- **And the shift is not the identity**, so the commutator it generates is
genuinely nonzero: the witness is not degenerate. -/
theorem shift_nontrivial : polyShift.T X ≠ X := by
  intro h
  have := congrArg (fun p => Polynomial.eval 0 p) h
  simp [polyShift] at this

/-- **The two structures are compatible, not merely coexisting**: translation
commutes with differentiation, so the shift moves along the scale axis without
disturbing A1's derivation. -/
theorem shift_commutes_with_derivation (p : Polynomial ℝ) :
    Polynomial.derivative (polyShift.T p) = polyShift.T (Polynomial.derivative p) := by
  simp [polyShift, derivative_comp]

/-! ## III. The remaining five structures

Each was flagged as never constructed.  Witnesses are cheap for four of them
and are given so the theorems are known non-vacuous; the fifth is discussed. -/

/-- **`Trace`**: the matrix trace is one, and it is the canonical example — the
`cyclic` field is exactly `trace (AB) = trace (BA)`.  Valued in the ring itself
via the scalar embedding. -/
noncomputable def matrixTrace (n : ℕ) : Invariant.Trace (Matrix (Fin n) (Fin n) ℝ) where
  τ := fun M => (Matrix.trace M) • (1 : Matrix (Fin n) (Fin n) ℝ)
  map_add := fun x y => by simp [Matrix.trace_add, add_smul]
  cyclic := fun x y => by rw [Matrix.trace_mul_comm]

/-- **`DirTransport`**: the adjoint action of a ring on itself.  Transport along
`x` is `[x, ·]`, which is additive in the direction, additive in the value, and
a derivation — the three fields, in order. -/
def adTransport (M : Type*) [Ring M] : Direction.DirTransport M M where
  D := fun x m => Quantum.ad x m
  add_dir := fun x y m => by simp only [Quantum.ad]; noncomm_ring
  add_val := fun x m m' => by simp only [Quantum.ad]; noncomm_ring
  leibniz := fun x m m' => Quantum.ad_leibniz x m m'

/-- **`ScaleFlow`**: the trivial flow, which fixes everything.  A witness that
the structure is inhabited; it is also the degenerate case in which every
coupling is a fixed point, so it shows the definitions are consistent without
pretending to model running. -/
def trivialFlow (S : Type*) : RG.ScaleFlow S where
  flow := fun _ g => g
  flow_zero := fun _ => rfl
  flow_add := fun _ _ _ => rfl

/-- A non-degenerate witness as well: translation of a real coupling by the
log-scale, which is the linear running of `Running.lean` in flow form. -/
def linearFlow : RG.ScaleFlow ℝ where
  flow := fun t g => g + t
  flow_zero := fun g => by ring
  flow_add := fun t u g => by ring

/-- And it genuinely moves: the linear flow has no fixed point at all, so the
fixed-point theorems of `RG.lean` are not about an empty case. -/
theorem linearFlow_moves (g : ℝ) : linearFlow.flow 1 g ≠ g := by
  simp only [linearFlow]
  linarith

/-- **`Conserved`** (from `Waves.lean`): a constant moment.  This is the witness
that the monopole and dipole theorems are non-vacuous — and it is also exactly
the physical content, since conservation *means* the moment is constant. -/
theorem constMoment_conserved (c : ℝ) : Waves.Conserved (fun _ => c) :=
  fun _ => hasDerivAt_const _ _

/-- **`CosmicHistory`**: a history whose drift is a real multiple of `1`, which
is spatially constant because derivations kill constants.  The `drift` field is
therefore satisfiable rather than an unfulfillable demand. -/
noncomputable def constantDrift (base : Polynomial ℝ) :
    Covariance.CosmicHistory 1 (Polynomial ℝ) where
  base := base
  drift := fun t => Polynomial.C t
  drift_spatially_constant := fun t i => by
    simp only [ScaleAlgebra.d]
    exact Polynomial.derivative_C

/-! ## IV. What is now settled, and what is not -/

/-- **Collected: the flagship structure is inhabited by an object satisfying
A1, and the step it produces is exact.**

That removes "unwitnessed" from `ScaleShift`.  It does **not** remove
"identification": one model carrying both structures does not show every model
of A1 must carry a scale shift, so `ħ = ` the step remains an identification and
stays registered as such. -/
theorem scaleShift_is_witnessed :
    Crossed.delta polyShift X = 1 ∧ polyShift.T X ≠ X :=
  ⟨shift_is_exact, shift_nontrivial⟩

end SCD.Witness
