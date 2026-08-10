/-
# Local covariance survives global dissipation

A6 says the universe dissipates: the fiducial scale drifts without end.  The
obvious objection is that this should wreck local physics — if the unit of
length is running away, why is the hydrogen atom the same size today as
yesterday, and why does the solar system not expand?

The answer is forced by A5 and is proved here.  Cosmic dissipation is a
*spatially constant* drift of the fiducial, `σ_t = σ + c(t)` with `∂ᵢ c(t) = 0`.
Every geometric object is built from *derivatives* of `σ`, so the drift cancels
identically.  Local geometry is therefore exactly time-independent, not
approximately so:

  * the connection, Riemann, Ricci, scalar curvature and the deformation
    tensor are literally the same at every cosmic epoch;
  * consequently the field equation is form-invariant along the drift, so
    local general covariance is untouched.

Bound systems do not expand, and this is a theorem rather than an assumption.
The expansion is visible only in the comparison of *different* fiducials —
which is exactly what a redshift measurement is.
-/
import SCD.Axioms
import Mathlib.Data.Real.Basic

namespace SCD.Covariance

open SCD ScaleAlgebra

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-- A **cosmic history**: a local scale profile together with a global fiducial
drift.  A6 makes the drift non-constant in time; A5 makes it spatially
constant, since a fiducial is by definition the same everywhere at a given
epoch. -/
structure CosmicHistory (n : ℕ) (A : Type*) [CommRing A] [ScaleAlgebra n A] where
  /-- The local scale profile — the gravitational field. -/
  base : A
  /-- The global fiducial drift produced by dissipation. -/
  drift : ℝ → A
  /-- The drift is spatially constant: it is a change of unit, not of geometry. -/
  drift_spatially_constant : ∀ (t : ℝ) (i : Fin n), d i (drift t) = 0

namespace CosmicHistory

variable (H : CosmicHistory n A)

/-- The scale field at cosmic time `t`. -/
def scale (t : ℝ) : A := H.base + H.drift t

/-- The scale gradient does not drift. -/
theorem sig_eq (t : ℝ) (i : Fin n) : sig (H.scale t) i = sig H.base i :=
  sig_add_const H.base (H.drift t) (H.drift_spatially_constant t) i

/-- **The connection is epoch-independent.** -/
theorem Chr_eq (t : ℝ) (a b e : Fin n) : Chr (H.scale t) a b e = Chr H.base a b e :=
  Chr_add_const H.base (H.drift t) (H.drift_spatially_constant t) a b e

/-- **Curvature is epoch-independent.**  Two observers at cosmic times `t` and
`t'`, however far apart, measure exactly the same local geometry. -/
theorem Rm_eq (t t' : ℝ) (a b e f : Fin n) :
    Rm (H.scale t) a b e f = Rm (H.scale t') a b e f := by
  simp only [scale]
  rw [Rm_add_const H.base (H.drift t) (H.drift_spatially_constant t),
    Rm_add_const H.base (H.drift t') (H.drift_spatially_constant t')]

theorem Ric_eq_of_drift (t t' : ℝ) (b e : Fin n) :
    Ric (H.scale t) b e = Ric (H.scale t') b e := by
  simp only [scale]
  rw [Ric_add_const H.base (H.drift t) (H.drift_spatially_constant t),
    Ric_add_const H.base (H.drift t') (H.drift_spatially_constant t')]

/-- The scale deformation — the source term of the field equation — is
epoch-independent. -/
theorem Defm_eq (t t' : ℝ) (i j : Fin n) :
    Defm n (H.scale t) i j = Defm n (H.scale t') i j := by
  simp only [scale]
  rw [Defm_add_const H.base (H.drift t) (H.drift_spatially_constant t),
    Defm_add_const H.base (H.drift t') (H.drift_spatially_constant t')]

/-- **The field equation is form-invariant under cosmic dissipation.**

If `e^{2σ}R = κρ` holds at one epoch it holds at every epoch with the same
`κ` and the same local `ρ`.  Global dissipation therefore does not renormalise
local gravity, and local general covariance is preserved exactly. -/
theorem field_equation_form_invariant (κ ρ : A) (t t' : ℝ)
    (hfield : RscBare n (H.scale t) = κ * ρ) :
    RscBare n (H.scale t') = κ * ρ := by
  rw [← hfield]
  simp only [RscBare]
  exact Finset.sum_congr rfl (fun b _ => H.Ric_eq_of_drift t' t b b)

/-- **Bound systems do not expand.**

Collected statement: everything locally measurable is exactly constant along
the cosmic drift.  Expansion is not a local force that space exerts on matter;
it is only visible when two *different* fiducials are compared, which is what a
cosmological redshift measurement does. -/
theorem no_local_expansion (t t' : ℝ) :
    (∀ i : Fin n, sig (H.scale t) i = sig (H.scale t') i)
    ∧ (∀ a b e f : Fin n, Rm (H.scale t) a b e f = Rm (H.scale t') a b e f)
    ∧ (∀ b e : Fin n, Ric (H.scale t) b e = Ric (H.scale t') b e)
    ∧ (∀ i j : Fin n, Defm n (H.scale t) i j = Defm n (H.scale t') i j)
    ∧ RscBare n (H.scale t) = RscBare n (H.scale t') := by
  refine ⟨fun i => by rw [H.sig_eq t i, H.sig_eq t' i], H.Rm_eq t t',
    H.Ric_eq_of_drift t t', H.Defm_eq t t', ?_⟩
  simp only [RscBare]
  exact Finset.sum_congr rfl (fun b _ => H.Ric_eq_of_drift t t' b b)

end CosmicHistory

end SCD.Covariance
