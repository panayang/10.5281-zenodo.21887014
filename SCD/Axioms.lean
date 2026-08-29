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
import Mathlib.Algebra.Group.Subgroup.Basic

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

/-! ### The energy is a scale field, and the scale fields are a group

A3 says `ε · s = 1`, and `en` was carried as a bare ring element with `d_en`
proved by hand — as if the energy were a different *kind* of object from the
scale.  It is not.  `−σ` is a log-scale and `s⁻¹` is its unit representative, so
**the energy is itself a scale field**, and A3 says it is the inverse of the
scale in a group whose elements are scale fields.

That is worth making explicit, because `Foundation.lean` *argues for* the
structure this turns out to be: it asks what a comparison of local units can
possibly be, concludes that comparisons compose invertibly and that scales are
ratios and so commute, and takes the scale of a comparison to be its image in
the abelianization.  Here the abelian group is exhibited rather than argued for,
and the argument's conclusion is a theorem about A1–A3.

`scale_energy_duality_is_inversion` is the statement the programme's name refers
to: scale–energy duality *is* inversion in this group. -/

/-- Two scale fields with the same log-scale and the same unit are equal: the
differential condition is a proposition, so it carries no data. -/
@[ext] theorem ext {F G : ScaleField n A} (hσ : F.σ = G.σ) (hs : F.s = G.s) : F = G := by
  cases F; cases G; simp_all

/-- **The trivial scale**: the fiducial itself, `σ = 0`, `s = 1`.  By A5 its
choice is unobservable, which is exactly why it can serve as a group identity. -/
def one : ScaleField n A where
  σ := 0
  s := 1
  d_s := by intro i; simp [sig]

/-- **Scales multiply**, and their log-scales add.  This is `Foundation.lean`'s
"comparisons compose", realised in the carrier A2 provides. -/
def mul (F G : ScaleField n A) : ScaleField n A where
  σ := F.σ + G.σ
  s := F.s * G.s
  d_s := by
    intro i
    have h : d i ((F.s : A) * (G.s : A))
        = ((F.s : A) * sig F.σ i) * (G.s : A) + (F.s : A) * ((G.s : A) * sig G.σ i) := by
      rw [d_mul, F.d_s, G.d_s]
    simp only [Units.val_mul, sig, d_add] at h ⊢
    rw [h]
    ring

/-- **The reciprocal scale field.**  `σ ↦ −σ`, `s ↦ s⁻¹`; the differential
condition is not assumed but forced, by differentiating `s · s⁻¹ = 1`. -/
def inv (F : ScaleField n A) : ScaleField n A where
  σ := -F.σ
  s := F.s⁻¹
  d_s := by
    intro i
    have hmul : (F.s : A) * ((F.s⁻¹ : Aˣ) : A) = 1 := F.s.mul_inv
    have h : d i ((F.s : A) * ((F.s⁻¹ : Aˣ) : A)) = 0 := by rw [hmul, d_one]
    rw [d_mul, F.d_s] at h
    have hstep : (F.s : A) * d i ((F.s⁻¹ : Aˣ) : A)
        = -((F.s : A) * (sig F.σ i * ((F.s⁻¹ : Aˣ) : A))) := by
      linear_combination h
    have hcancel : ((F.s⁻¹ : Aˣ) : A) * (F.s : A) = 1 := by
      rw [mul_comm]; exact hmul
    calc d i ((F.s⁻¹ : Aˣ) : A)
        = (((F.s⁻¹ : Aˣ) : A) * (F.s : A)) * d i ((F.s⁻¹ : Aˣ) : A) := by
          rw [hcancel, one_mul]
      _ = ((F.s⁻¹ : Aˣ) : A) * ((F.s : A) * d i ((F.s⁻¹ : Aˣ) : A)) := by ring
      _ = ((F.s⁻¹ : Aˣ) : A) * (-((F.s : A) * (sig F.σ i * ((F.s⁻¹ : Aˣ) : A)))) := by
          rw [hstep]
      _ = -((((F.s⁻¹ : Aˣ) : A) * (F.s : A)) * (((F.s⁻¹ : Aˣ) : A) * sig F.σ i)) := by ring
      _ = ((F.s⁻¹ : Aˣ) : A) * sig (-F.σ) i := by
          rw [hcancel, one_mul]
          simp only [sig, d_neg]
          ring

/-- **The scale fields form an abelian group.**

`Foundation.lean` reaches "scales multiply and commute" by asking what a
comparison of local units can possibly be; this group is what A1–A3 actually
supply, and the two agree.  So the abelianization `Foundation.scale` takes is
the identity on this carrier — in the scalar sector everything is scale and
nothing is curvature, which is `Foundation.commutator_eq_one_of_comm` supplied
with a witness rather than assumed. -/
instance : CommGroup (ScaleField n A) where
  mul := mul
  one := one
  inv := inv
  mul_assoc F G H :=
    ext (show F.σ + G.σ + H.σ = F.σ + (G.σ + H.σ) by ring)
      (show F.s * G.s * H.s = F.s * (G.s * H.s) from mul_assoc _ _ _)
  one_mul F :=
    ext (show (0 : A) + F.σ = F.σ by ring) (show (1 : Aˣ) * F.s = F.s from one_mul _)
  mul_one F :=
    ext (show F.σ + (0 : A) = F.σ by ring) (show F.s * (1 : Aˣ) = F.s from mul_one _)
  inv_mul_cancel F :=
    ext (show -F.σ + F.σ = (0 : A) by ring)
      (show F.s⁻¹ * F.s = (1 : Aˣ) from inv_mul_cancel _)
  mul_comm F G :=
    ext (show F.σ + G.σ = G.σ + F.σ by ring)
      (show F.s * G.s = G.s * F.s from mul_comm _ _)

@[simp] theorem mul_σ (F G : ScaleField n A) : (F * G).σ = F.σ + G.σ := rfl
@[simp] theorem mul_s (F G : ScaleField n A) : (F * G).s = F.s * G.s := rfl
@[simp] theorem inv_σ (F : ScaleField n A) : (F⁻¹).σ = -F.σ := rfl
@[simp] theorem inv_s (F : ScaleField n A) : (F⁻¹).s = F.s⁻¹ := rfl
@[simp] theorem one_σ : (1 : ScaleField n A).σ = 0 := rfl
@[simp] theorem one_s : (1 : ScaleField n A).s = 1 := rfl

/-- **A3, restated: the energy field is the inverse scale field.**

`ε = 1/s` is not a derived quantity of a different type — it is the unit of
`F⁻¹`, whose log-scale is `−σ`.  So "the local energy scale is the reciprocal of
the local length scale" is inversion in the group of scale fields, and nothing
else. -/
@[simp] theorem en_eq_inv_s : F.en = (((F⁻¹).s : Aˣ) : A) := rfl

/-- **Scale–energy duality is inversion.**

The whole content of A3 in one line: `F · F⁻¹ = 1`, whose unit component is
`ε · s = 1` and whose log component is `σ + (−σ) = 0`.  Every consequence drawn
from A3 elsewhere — redshift, the mass–threshold identification, the absence of
a minimum length — is a consequence of this. -/
theorem scale_energy_duality_is_inversion :
    F * F⁻¹ = 1 ∧ F.en * (F.s : A) = 1 ∧ F.σ + (F⁻¹).σ = 0 := by
  refine ⟨mul_inv_cancel F, F.en_mul_scale, ?_⟩
  show F.σ + -F.σ = 0
  ring

/-- The energy of the energy is the scale: duality is an involution, so nothing
distinguishes "the scale" from "the energy" except which is being called which.
That is the framework's version of "high energy *is* small scale". -/
theorem inv_inv_eq (F : ScaleField n A) : F⁻¹⁻¹ = F := inv_inv F

/-- **Redshift is the group law.**  The log-scale of a product is the sum, so
composing two scale changes multiplies the energies — `d_en` is the
infinitesimal form of this. -/
theorem en_mul (F G : ScaleField n A) : (F * G).en = F.en * G.en := by
  show (((F * G)⁻¹).s : A) = (((F⁻¹).s : A)) * (((G⁻¹).s : A))
  rw [mul_inv]
  rfl

/-! ### A5 in the same language: the fiducial changes are a subgroup

A5 says a global shift `σ ↦ σ + c` is unobservable.  In the group of scale
fields such a shift is *multiplication by a scale field whose log-scale is
constant*, so A5 is the assertion that a particular **subgroup acts trivially on
the geometry**.  That subgroup is exhibited here, and
`geometry_fiducial_invariant` below is the action being trivial.

Saying it this way costs nothing and buys the same thing the group law bought
for A3: A5 stops being a statement about a stray constant `c` and becomes a
statement about the carrier A2 already provides. -/

/-- A scale field is **fiducial** when its log-scale is constant: it changes the
unit everywhere by the same amount, which by A5 is unobservable. -/
def IsFiducial (F : ScaleField n A) : Prop := ∀ i : Fin n, d i F.σ = 0

/-- The fiducial scale fields form a subgroup — the group of changes of unit. -/
def fiducials : Subgroup (ScaleField n A) where
  carrier := {F | IsFiducial F}
  one_mem' := by intro i; show d i (0 : A) = 0; simp
  mul_mem' := by
    intro F G hF hG i
    show d i (F.σ + G.σ) = 0
    rw [d_add, hF i, hG i, add_zero]
  inv_mem' := by
    intro F hF i
    show d i (-F.σ) = 0
    rw [d_neg, hF i, neg_zero]

@[simp] theorem mem_fiducials {F : ScaleField n A} : F ∈ fiducials ↔ IsFiducial F := Iff.rfl

/-- **Rescaling by a fiducial does not move the scale gradient**, hence moves
nothing geometric: this is the group-theoretic form of A5, and everything in
`geometry_fiducial_invariant` follows from it. -/
theorem sig_mul_fiducial (F C : ScaleField n A) (hC : IsFiducial C) (i : Fin n) :
    sig (F * C).σ i = sig F.σ i := by
  show d i (F.σ + C.σ) = d i F.σ
  rw [d_add, hC i, add_zero]

/-- And the energy is multiplied by the fiducial's own energy — the same
constant everywhere — which is why every *ratio* of energies is
fiducial-independent while no single energy is.  That is A5's content and the
reason the framework predicts only ratios (`Dimension.only_ratios_are_fixed`). -/
theorem en_mul_fiducial (F C : ScaleField n A) : (F * C).en = F.en * C.en :=
  en_mul F C

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
