/-
# SCD — the seven postulates, in one place

Scale-Coupled Dynamics.  *Field* is deliberately absent from the name: the
development concludes that there is no field whose excitations are particles
(`Emergence.lean`, `Slice.lean`), and gravity here is not a field on a geometry
but the inhomogeneity of the scale itself.  Calling it field dynamics would
write into the title the ontology the theory rejects.

Everything is dimensionless.  No quantity carries a unit; each is a pure number
defined as a ratio against a fiducial whose choice is itself declared
unobservable, which is A5.

## The seven

**A1 — Substrate.**  A bare counting structure carrying `n` derivations that
commute as operators.  Formal carrier: `Connection.DiffRing`.
*Status:* postulated.  Commuting derivations are a **chart**, not a flatness
assumption — an earlier reading claimed otherwise and is withdrawn
(`Dynamics.no_flatness_from_commuting_derivations`).  The commutative
specialisation `ScaleAlgebra` is the *same* axiom over a commutative ring, and
`scaleAlgebra_is_diffRing` below proves it rather than leaving it to the reader.

**A2 — Scale.**  A dimensionless log-scale `σ`, with multiplicative
representative `s = e^σ` postulated as a **unit** of the ring.  Formal carrier:
`ScaleField`.  *Status:* postulated.  That `s` is a unit — never zero, never
infinite — is what later removes the singularity, the horizon and the minimum
length in one stroke.

**A3 — Scale–energy duality.**  `ε · s = 1`: the local energy scale is the
reciprocal of the local length scale.  Formal carrier: `ScaleField.en`.
*Status:* postulated.  This is the axiom the whole programme turns on, and it
came from putting Heisenberg's relation and Einstein's equation side by side.

**A4 — Measurement, directional.**  One scale **per direction**; physical length
is bare length read in the local unit.  Formal carrier: `Frame.DirScale`.
*Status:* postulated, **after correction**.  The original A4 gave a single
scalar scale; `Frame.isotropic_reciprocal_forces_flat` proves that version
*forbids* Schwarzschild, so it was demoted to the isotropic locus
(`Unify.lean`).  Reading the directional axiom as if it were scalar is the
error this development made five times; see the register in `Audit.lean`.

**A5 — Fiducial covariance.**  Only differences of `σ` are observable; a global
shift `σ ↦ σ + c` is a symmetry.  Formal carrier:
`geometry_fiducial_invariant`.  *Status:* postulated, and load-bearing beyond
its appearance: it is what makes the geometry exactly dimensionless, and it is
what forces the dissipation rate to be constant
(`Cosmos.rate_constant_of_fiducial_invariance`), hence `w = −1` with no
evolution.  **The DESI tension is a tension with A5, not with a fitted
parameter.**

**A6 — Openness.**  The universe is not closed; its total energy scale
dissipates.  Formal carrier: `Cosmology.dissipation_solution`.
*Status:* postulated.  A6 gives time a direction (`Signature.lean`) and, because
a dissipating source is not conserved, removes any *global* field equation
(`Native.no_global_field_equation`).

**A7 — Observability.**  Every structure the coupling generates carries a label
the axioms provide.  Formal carrier: `Locus.Observability`.
*Status:* postulated, **and promoted late**.  It was carried for several
revisions as a "judgement"; `Dimension.two_matching_conditions_differ` shows a
condition of that shape is a choice, so it is now stated as an axiom.  Given
A7, `k = 3` is a theorem and `n = 4` follows.  This is a demotion of a claim,
not a promotion of a result — it is the framework's commitment about what
counts as an observation, and someone may refuse it and obtain a different `k`.

## What is *not* an axiom

The scale/rotation split, the bookkeeping form, the Lorentzian signature, the
coupling between scale and rotation, the algebra family, the dimension `n`, and
the conservation law are all **derived**.  Two external results are cited and
not proved: the classification of real-rank-one simple Lie algebras, and the
homotopy of projective spaces.  One assumption is registered separately:
defects uniform in the symmetric space's volume.  The full register is in
`Audit.lean`.

## The one free number

Everything the theory predicts is a *ratio* (`Dimension.only_ratios_are_fixed`).
The overall magnitude of the scale pattern is not predicted and cannot be: it is
the unit in which the predictions are expressed.  A dimensionless theory must
carry exactly one such number and this one carries exactly one, which is the
minimum possible.
-/
import SCD.Connection
import SCD.Axioms
import SCD.Frame

namespace SCD.Postulates

/-! ## A1 has one carrier, not three

An earlier state of this development declared the substrate three times — once
over a commutative ring (`ScaleAlgebra`), once over a ring (`DiffRing`), and
once again over a ring under another name.  The third was removed in the
reorganisation; the first two differ only in whether the ring is commutative,
and the bridge is proved here rather than asserted. -/

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-- **The commutative substrate is the substrate.**

`ScaleAlgebra` is `DiffRing` with a commutative ring underneath: same
derivations, same Leibniz rule, same commuting mixed partials.  Constructing the
one from the other makes the identification formal, so "A1 has one carrier" is
checked rather than claimed. -/
def scaleAlgebra_is_diffRing : Connection.DiffRing n A where
  D := ScaleAlgebra.d
  D_add := ScaleAlgebra.d_add
  D_mul := ScaleAlgebra.d_mul
  D_comm := ScaleAlgebra.d_comm

/-- And the transfer is the identity on the derivations: nothing is lost or
added in passing between the two presentations. -/
theorem scaleAlgebra_is_diffRing_d (i : Fin n) (a : A) :
    (scaleAlgebra_is_diffRing (n := n) (A := A)).D i a = ScaleAlgebra.d i a := rfl

/-! ## A7, restated where the other six are

`Locus.Observability` is the formal carrier; it is repeated here so that the
seven postulates can be read in one place without following a chain of
imports. -/

/-- **A7 (Observability).**  The rotations the coupling generates are as
numerous as the scale directions A4 labels.

Stated as `2·dim Λ²p = 2·dim p` in the doubled form that avoids natural-number
division, with `k = m + 1`. -/
def Observability (m : ℕ) : Prop := (m + 1) * m = 2 * (m + 1)

/-- Given A7, `k = 3`; and `n = k + 1 = 4` follows because naming the algebra
already fixed `n` as its defining representation's dimension. -/
theorem three_from_A7 {m : ℕ} (h : Observability m) : m = 2 := by
  have h' : m * (m + 1) = 2 * (m + 1) := by rw [mul_comm]; exact h
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) h'

/-- A7 is a genuine restriction: it holds at exactly one dimension. -/
theorem A7_holds_only_at_three (m : ℕ) : Observability m ↔ m = 2 := by
  constructor
  · exact three_from_A7
  · rintro rfl; norm_num [Observability]

end SCD.Postulates
