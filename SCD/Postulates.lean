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
commute as operators.  Formal carrier: `ScaleAlgebra`, stated over a ring.
*Status:* postulated.  Commuting derivations are a **chart**, not a flatness
assumption — an earlier reading claimed otherwise and is withdrawn
(`Dynamics.no_flatness_from_commuting_derivations`).  Commutativity of the ring
is not part of the axiom: the commutative sector is the classical one and the
general case is the quantum one, and they are the same axiom (§ below).

**A2 — Scale.**  A dimensionless log-scale `σ`, with multiplicative
representative `s = e^σ` postulated as a **unit** of the ring.  Formal carrier:
`ScaleField`.  *Status:* postulated.  That `s` is a unit — never zero, never
infinite — is what later removes the singularity, the horizon and the minimum
length in one stroke.

*Measured, and the statement carries more than it uses.*  `Gradient.lean` shows
the geometry never reads `σ`, only its gradient, and that the gradient is forced:
`Amendment.sig_eq_logDeriv` makes it the logarithmic derivative `s⁻¹∂s` of the
unit, so `Amendment.same_unit_same_geometry` gives two scale fields with the same
unit the same geometry — all of it.  The potential is a *choice*, unique up to a
fiducial (`Amendment.potential_unique_up_to_fiducial`), which is exactly A5's
freedom and nothing more.  **What A2 adds beyond "the scale is a unit" is the
assertion that a potential exists at all**, and `Torus.torGradient_not_isExact`
shows that is a real assumption in every dimension: it is the `ℝ` branch of A3′,
which `Dual.lean` says is not the branch gravity selects.  The axiom is left as
it stands; what is new is that it is now known what it is choosing.

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
the axioms provide.  Formal carrier: `Observability`, stated once in
`Pattern.lean` as `rotDim2 m = scaleDim2 m`.
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

/-! ## A1 has one carrier

An earlier state of this development declared the substrate three times — over a
commutative ring as `ScaleAlgebra`, over a ring as `Connection.DiffRing`, and
once more under a third name in `NCConformal.lean`.  Two were removed in earlier
passes and the last is removed now: **A1 is one class**, `ScaleAlgebra`, stated
over a ring in `Basic.lean`.

Nothing had to be given up to merge them, because commutativity was never used
to *state* A1 — only to prove some of its consequences.  The two theorems below
record what that costs and what it does not.  `Conformal.hess_symm` and
`Conformal.Chr_symm` are the consequences that survive without it; the whole
classical curvature computation is the part that does not, and
`NCConformal.lean` computes the difference exactly. -/

variable {n : ℕ} {M : Type*} [Ring M] [ScaleAlgebra n M]

/-- **Equality of mixed partials is a chart, and survives non-commutativity.**

The symmetry of the scale Hessian is `d_comm` and nothing else, so it holds in
the quantum sector verbatim.  This is why exactly *one* object in the curvature
computation — the deformation tensor — notices the passage. -/
theorem substrate_hessian_symm (σ : M) (i j : Fin n) : hess σ i j = hess σ j i :=
  hess_symm σ i j

/-- **The commutative sector is a sector, not a second axiom.**

Every `CommRing` satisfying A1 satisfies A1: no transport is required, and there
is nothing to check.  Recorded as a `rfl` so that "A1 has one carrier" is a fact
about the elaborator rather than a claim in a comment. -/
theorem commutative_sector_is_the_substrate {A : Type*} [CommRing A] [ScaleAlgebra n A]
    (i : Fin n) (a : A) : ScaleAlgebra.d i a = ScaleAlgebra.d i a := rfl

/-! ## A7, where the other six are

`Observability` is stated once, in `Pattern.lean`, together with the two sector
counts it compares.  It was previously written out three further times — here as
raw arithmetic, in `Locus.lean` in terms of `Dimension`'s counts, and in
`Slice.lean` as `wedgeDim = dirDim` — with `Iff.rfl` bridges standing in for the
identification.  The theorems below are the same statements, now about the one
definition. -/

/-- Given A7, `k = 3`; and `n = k + 1 = 4` follows because naming the algebra
already fixed `n` as its defining representation's dimension. -/
theorem three_from_A7 {m : ℕ} (h : Observability m) : m = 2 :=
  three_from_observability h

/-- A7 is a genuine restriction: it holds at exactly one dimension. -/
theorem A7_holds_only_at_three (m : ℕ) : Observability m ↔ m = 2 :=
  observability_iff_two m

end SCD.Postulates
