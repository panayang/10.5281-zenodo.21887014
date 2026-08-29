/-
# A5 and A6 are one statement about one subgroup

A5 says a global shift of the fiducial is unobservable.  A6 says the universe is
open: its total energy scale dissipates.  They are stated as two independent
postulates and have always been discussed as two — indeed as being *in tension*,
which `Observation.lean` was written to resolve.

They are not two.  `Axioms.ScaleField.fiducials` is the subgroup of scale fields
whose log-scale is constant, and:

        **A5** :  that subgroup acts trivially on the geometry.
        **A6** :  the world's scale field is **not in it**.

One subgroup, two things said about it — that it is a kernel, and that the world
is not the identity.  Everything each axiom is used for follows from that
reading, and the reading is what this file proves.

## What being in the subgroup costs

A fiducial scale field is not merely uninteresting; it is *empty*:

* `fiducial_no_drift` — every direction has vanishing scale gradient, so by
  `Signature.lean`'s argument the drift functional is zero and **no direction is
  distinguished: there is no time**;
* `fiducial_hess`, `fiducial_gradsq`, `fiducial_lap` — every second-order
  quantity vanishes;
* `fiducial_Defm_eq_zero` and `fiducial_flat` — hence the deformation tensor
  vanishes and, where `2` is invertible, **the whole Riemann tensor does**.  A
  closed universe is flat.

So the fiducial locus is the one point of the theory at which nothing happens at
all — no time, no curvature, no content.  `closed_universe_is_empty` collects
it.

**A6 is the statement that the world is not that point**, and every structure
the framework describes is a measure of how far from it the world is.  That is
one axiom's worth of content, not two.

## Openness costs a transverse direction

There is a second, sharper thing the merged reading makes visible.
`Waves.total_conserved` derives conservation from a continuity equation whose
non-drift terms are the transverse divergences.  With **one** direction there are
no transverse terms, so the continuity equation degenerates to `∂_t ρ = 0`:

* `no_dissipation_in_one_direction` — on a one-direction substrate a continuity
  equation forbids dissipation outright.

Hence **A6 forces `n ≥ 2`, or else the absence of any continuity equation.**
`Native.no_global_field_equation` says the second horn is the one the framework
actually takes globally — but locally, where continuity does hold
(`Covariance.lean`), the first horn bites: *the universe is open because it has
somewhere to leak.*  Openness is not a separate fact about the universe; given a
local conservation law it is a statement about the dimension.

## What is not claimed

This does not derive A6 from A5.  "The world is not the identity of a group" is
a contingent fact and no theorem produces it.  What is shown is that A6 is a
statement **about the object A5 is about**, so the two should be counted as one
postulate with two clauses, in the way A4 and A4′ were merged in `Unify.lean`.
The register's axiom count should read that way, and `Audit.lean` records it.
-/
import SCD.Axioms
import SCD.Conformal

namespace SCD.Openness

open SCD ScaleAlgebra Finset

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-! ## I. A6 in A5's vocabulary -/

/-- **A6 (Openness), stated about A5's subgroup.**  The world's scale field is
not a fiducial one — it is not in the kernel A5 declares unobservable. -/
def IsOpen (F : ScaleField n A) : Prop := ¬ ScaleField.IsFiducial F

/-- The two clauses are about the same subgroup: being fiducial is membership,
being open is non-membership. -/
theorem open_iff_not_mem (F : ScaleField n A) :
    IsOpen F ↔ F ∉ ScaleField.fiducials := Iff.rfl

/-- Openness is exactly "some direction drifts". -/
theorem open_iff_some_drift (F : ScaleField n A) :
    IsOpen F ↔ ∃ i : Fin n, sig F.σ i ≠ 0 := by
  simp only [IsOpen, ScaleField.IsFiducial, sig]
  push Not
  rfl

/-! ## II. What being in the subgroup costs -/

variable (F : ScaleField n A)

/-- A fiducial scale field has no drift in any direction. -/
theorem fiducial_no_drift (h : ScaleField.IsFiducial F) (i : Fin n) : sig F.σ i = 0 := h i

/-- Hence its Hessian vanishes: nothing varies at second order either. -/
theorem fiducial_hess (h : ScaleField.IsFiducial F) (i j : Fin n) : hess F.σ i j = 0 := by
  show d i (sig F.σ j) = 0
  rw [fiducial_no_drift F h j, d_zero]

theorem fiducial_lap (h : ScaleField.IsFiducial F) : lap n F.σ = 0 := by
  simp only [lap, fiducial_hess F h, Finset.sum_const_zero]

theorem fiducial_gradsq (h : ScaleField.IsFiducial F) : gradsq n F.σ = 0 := by
  simp only [gradsq, fiducial_no_drift F h, mul_zero, Finset.sum_const_zero]

/-- **A fiducial scale field has no deformation.**  The obstruction to the local
unit varying affinely is zero, because the unit does not vary at all. -/
theorem fiducial_Defm_eq_zero (h : ScaleField.IsFiducial F) (i j : Fin n) :
    Defm n F.σ i j = 0 := by
  simp only [Defm, fiducial_hess F h, fiducial_no_drift F h, fiducial_gradsq F h,
    mul_zero, sub_zero, add_zero]

/-- **A closed universe is flat.**

Not merely Ricci-flat: the whole Riemann tensor vanishes, by
`Conformal.Rm_eq_zero_of_Defm_eq_zero`.  So the fiducial locus carries no
gravity, and there is nothing there to describe. -/
theorem fiducial_flat [Invertible (2 : A)] (h : ScaleField.IsFiducial F) (a b c e : Fin n) :
    Rm F.σ a b c e = 0 :=
  Rm_eq_zero_of_Defm_eq_zero F.σ (fiducial_Defm_eq_zero F h) a b c e

/-- **Collected: the closed universe is empty.**

No drift in any direction — hence no distinguished direction, hence by
`Signature.no_time_of_no_drift`'s argument no time; no deformation; and, where
`2` is invertible, no curvature of any kind.

A6 is the statement that the world is not this.  Every structure the framework
describes measures the distance from it. -/
theorem closed_universe_is_empty [Invertible (2 : A)] (h : ScaleField.IsFiducial F) :
    (∀ i : Fin n, sig F.σ i = 0) ∧ (∀ i j : Fin n, Defm n F.σ i j = 0)
      ∧ (∀ a b c e : Fin n, Rm F.σ a b c e = 0) :=
  ⟨fiducial_no_drift F h, fiducial_Defm_eq_zero F h, fiducial_flat F h⟩

/-- And conversely, anything nonzero at all forces openness: a single nonvanishing
deformation component puts the world outside the subgroup.  So "there is
geometry" and "the universe is open" are the same statement. -/
theorem open_of_deformation {i j : Fin n} (hD : Defm n F.σ i j ≠ 0) : IsOpen (n := n) F := by
  intro h
  exact hD (fiducial_Defm_eq_zero F h i j)

/-! ## III. Openness costs a transverse direction

`Waves.total_conserved` reads a continuity equation as "the drift of the density
lies in the subgroup generated by the transverse divergences".  With one
direction there are no transverse divergences, so the equation says the density
does not drift at all. -/

section OneDirection

variable {M : Type*} [Ring M] [ScaleAlgebra 1 M]

/-- **A one-direction substrate cannot dissipate.**

The transverse sum is empty, so a continuity equation degenerates to
`∂_t ρ = 0`.  Nothing can leak, because there is nowhere for it to leak to. -/
theorem no_dissipation_in_one_direction (ρ : M) (J : Fin 1 → M) (t : Fin 1)
    (hcont : d t ρ + ∑ i ∈ Finset.univ.erase t, d i (J i) = 0) : d t ρ = 0 := by
  have hempty : (Finset.univ.erase t) = (∅ : Finset (Fin 1)) := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.notMem_empty, iff_false,
      not_not]
    exact Subsingleton.elim i t
  rw [hempty, Finset.sum_empty, add_zero] at hcont
  exact hcont

/-- **So openness and local continuity together force more than one direction.**

If the density genuinely drifts — which is A6 — then no continuity equation of
the above shape holds on a one-direction substrate.  Given that continuity does
hold locally (`Covariance.lean`), A6 is a statement about the *dimension*: the
universe is open because it has somewhere to leak. -/
theorem openness_forbids_continuity_in_one_direction (ρ : M) (J : Fin 1 → M) (t : Fin 1)
    (hdrift : d t ρ ≠ 0) :
    d t ρ + ∑ i ∈ Finset.univ.erase t, d i (J i) ≠ 0 := by
  intro hcont
  exact hdrift (no_dissipation_in_one_direction ρ J t hcont)

end OneDirection

/-! ## IV. The accounting

A5 and A6 should be counted as one postulate with two clauses.  The merge is of
the same kind as `Unify.lean`'s: there A4 was demoted to a locus of A4′, here A6
is recognised as a statement about A5's kernel.  Nothing is derived that was not
there; what changes is the count, and the count is what the register carries. -/

/-- **The merged statement.**

For any scale field, exactly one of two things holds: it lies in A5's fiducial
subgroup — in which case it has no drift, no deformation and no curvature — or it
does not, which is A6.  Two clauses about one subgroup. -/
theorem A5_A6_dichotomy [Invertible (2 : A)] (F : ScaleField n A) :
    (ScaleField.IsFiducial F ∧ (∀ a b c e : Fin n, Rm F.σ a b c e = 0)) ∨ IsOpen (n := n) F := by
  by_cases h : ScaleField.IsFiducial F
  · exact Or.inl ⟨h, fiducial_flat F h⟩
  · exact Or.inr h

end SCD.Openness
