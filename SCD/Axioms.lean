/-
# A2, A3, A5 — the scale field and exact dimensionlessness

**The axiom system is stated in `Postulates.lean`**, all seven in one place with
the formal carrier and status of each.  This file carries three of them and
derives their immediate consequences; it is not the place to read the axioms
from.

* **A2 — Scale.**  A dimensionless log-scale `σ` with multiplicative
  representative `s = e^σ`, postulated as a *unit* of the ring.  Carrier:
  `ScaleField`.
* **A3 — Scale–energy duality.**  `ε · s = 1`.  Carrier: `ScaleField.en`.
* **A5 — Fiducial covariance.**  Only differences of `σ` are observable.
  Carrier: `geometry_fiducial_invariant`.

Working with `s` as a unit rather than an analytic exponential keeps the
development algebraic while capturing the one property that matters: `s` is
nowhere zero, and `d log s = dσ`.  That `s` is a unit is what later removes the
singularity (`Singularity.lean`), the horizon (`Horizon.lean`) and the minimum
length in one stroke.

A5 is load-bearing far beyond its appearance here.  It makes the geometry
exactly dimensionless, and it forces the dissipation rate to be constant
(`Cosmos.rate_constant_of_fiducial_invariance`), hence `w = −1` with no
evolution — which is the framework's most exposed prediction.
-/
import SCD.Conformal

namespace SCD

open Finset ScaleAlgebra

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-! ## A2 — the scale field

`σ` is the log-scale.  Its exponential `s = e^σ` is postulated as a *unit* of
the ring satisfying the defining differential equation of the exponential.
Working with `s` as a unit rather than with an analytic `exp` keeps the whole
development algebraic while capturing exactly the property that matters:
`s` is nowhere zero and `d log s = dσ`. -/

/-- A **scale field**: a dimensionless log-scale `σ` together with its
multiplicative representative `s = e^σ`. -/
structure ScaleField (n : ℕ) (A : Type*) [CommRing A] [ScaleAlgebra n A] where
  /-- The log-scale.  Dimensionless, observable only through its differences. -/
  σ : A
  /-- The scale itself, `s = e^σ`; a unit, hence nowhere vanishing. -/
  s : Aˣ
  /-- `s` is the exponential of `σ`: `∂_i s = s ∂_i σ`. -/
  d_s : ∀ i : Fin n, d i (s : A) = (s : A) * sig σ i

namespace ScaleField

variable (F : ScaleField n A)

/-- **A3 — scale–energy duality.**  The local energy scale is the reciprocal
of the local length scale.  In natural units `ħ = c = 1` this is not a
modelling choice but the definition of energy: `ε = 1/s`. -/
def en : A := ((F.s⁻¹ : Aˣ) : A)

/-- The duality relation itself: `ε · s = 1`.  High energy *is* small scale. -/
@[simp] theorem en_mul_scale : F.en * (F.s : A) = 1 := by
  simp only [en]
  exact Units.inv_mul F.s

theorem scale_mul_en : (F.s : A) * F.en = 1 := by
  rw [mul_comm]; exact F.en_mul_scale

/-- **Gravitational redshift.**  Differentiating the duality relation forces
`∂_i ε = −ε ∂_i σ`: the energy of a fixed excitation *falls* exactly where the
scale *rises*.  Climbing out of a region of enlarged scale therefore costs
energy — redshift is a theorem, not an extra postulate. -/
theorem d_en (i : Fin n) : d i F.en = -(F.en * sig F.σ i) := by
  have h : d i (F.en * (F.s : A)) = 0 := by rw [F.en_mul_scale, d_one]
  rw [d_mul, F.d_s] at h
  have h' : (d i F.en) * (F.s : A) = -(F.en * ((F.s : A) * sig F.σ i)) := by
    linear_combination h
  calc d i F.en = (d i F.en) * ((F.s : A) * F.en) := by rw [F.scale_mul_en, mul_one]
    _ = ((d i F.en) * (F.s : A)) * F.en := by ring
    _ = (-(F.en * ((F.s : A) * sig F.σ i))) * F.en := by rw [h']
    _ = -((F.s : A) * F.en) * (F.en * sig F.σ i) := by ring
    _ = -(F.en * sig F.σ i) := by rw [F.scale_mul_en]; ring

end ScaleField

/-! ## A5 — fiducial covariance, i.e. exact dimensionlessness

`σ` is defined only up to a global additive constant, because the fiducial
unit against which the scale is measured is arbitrary.  We prove that this is
an exact symmetry of *everything geometric*: the connection, the Riemann
tensor, Ricci, and the scale deformation are all untouched by `σ ↦ σ + c`.

This is what it means for the theory to be dimensionless.  It is also the
origin of the renormalisation group: the *geometry* is invariant under a shift
of the fiducial scale, while the *description of matter* need not be — and the
required compensating change of couplings is precisely RG flow. -/

section Fiducial

variable (σ c : A) (hc : ∀ i : Fin n, d i c = 0)
include hc

@[simp] theorem sig_add_const (i : Fin n) : sig (σ + c) i = sig σ i := by
  simp only [sig, d_add, hc i, add_zero]

@[simp] theorem hess_add_const (i j : Fin n) : hess (σ + c) i j = hess σ i j := by
  simp only [hess, sig_add_const σ c hc]

@[simp] theorem lap_add_const : lap n (σ + c) = lap n σ := by
  simp only [lap, hess_add_const σ c hc]

@[simp] theorem gradsq_add_const : gradsq n (σ + c) = gradsq n σ := by
  simp only [gradsq, sig_add_const σ c hc]

@[simp] theorem Chr_add_const (a b e : Fin n) : Chr (σ + c) a b e = Chr σ a b e := by
  simp only [Chr, sig_add_const σ c hc]

@[simp] theorem Rm_add_const (a b e f : Fin n) : Rm (σ + c) a b e f = Rm σ a b e f := by
  simp only [Rm, Chr_add_const σ c hc]

@[simp] theorem Ric_add_const (b e : Fin n) : Ric (σ + c) b e = Ric σ b e := by
  simp only [Ric, Rm_add_const σ c hc]

@[simp] theorem Defm_add_const (i j : Fin n) : Defm n (σ + c) i j = Defm n σ i j := by
  simp only [Defm, hess_add_const σ c hc, sig_add_const σ c hc, gradsq_add_const σ c hc]

/-- **A5, collected: the geometry is exactly dimensionless.**

A global change of the fiducial unit leaves every geometric object invariant.
No observable depends on where the zero of `σ` is placed; only scale
*differences* are physical. -/
theorem geometry_fiducial_invariant :
    (∀ i : Fin n, sig (σ + c) i = sig σ i)
    ∧ (∀ a b e f : Fin n, Rm (σ + c) a b e f = Rm σ a b e f)
    ∧ (∀ b e : Fin n, Ric (σ + c) b e = Ric σ b e)
    ∧ (∀ i j : Fin n, Defm n (σ + c) i j = Defm n σ i j)
    ∧ RscBare n (σ + c) = RscBare n σ := by
  refine ⟨sig_add_const σ c hc, Rm_add_const σ c hc, Ric_add_const σ c hc,
    Defm_add_const σ c hc, ?_⟩
  simp only [RscBare, Ric_add_const σ c hc]

end Fiducial

/-! ## Linearity of the scale operators

Elementary, but needed to pass between the log-scale `σ` and the Newtonian
potential `Φ = −σ`. -/

@[simp] theorem sig_neg (σ : A) (i : Fin n) : sig (-σ) i = -sig σ i := by
  simp only [sig, d_neg]

@[simp] theorem hess_neg (σ : A) (i j : Fin n) : hess (-σ) i j = -hess σ i j := by
  simp only [hess, sig_neg, d_neg]

@[simp] theorem lap_neg (σ : A) : lap n (-σ) = -lap n σ := by
  simp only [lap, hess_neg, Finset.sum_neg_distrib]

@[simp] theorem gradsq_neg (σ : A) : gradsq n (-σ) = gradsq n σ := by
  simp only [gradsq, sig_neg]
  exact Finset.sum_congr rfl (fun i _ => by ring)

end SCD
