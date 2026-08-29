/-
# Momentum, and the mass shell

The development had the Lorentz **algebra** (`Algebra.lean`) and no dispersion
relation.  It had "energy" — but only as `ε = 1/s`, a *scalar*, and
`Axioms.scale_energy_duality_is_inversion` shows that what A3 actually says is
that `ε` is the inverse of `s` in the group of scale fields.  Inversion is a map
`G → G`.  Physical energy is the generator of translation along the drift, which
belongs to the **dual**, and calling `s⁻¹` "the energy" conflated the two.

With A3 read directionally (`Frame.DirScale.en`, one energy per direction) the
conflation resolves and the missing structure appears at once:

        ε_t   is the energy,
        ε_i   are the momenta,

and they are one object — the inverse scale pattern — split by the drift
direction that `Signature.lean` singles out.  Nothing new is postulated; the
directional reading of A3 costs no hypothesis, since `(E.s a)⁻¹` exists because
`E.s a` is a unit.

## I.  Lowering and raising are the two scale patterns

`Light.physFormDir` measures a *direction* with `s_a²`.  The corresponding form
on **covectors** measures with `ε_a² = s_a⁻²`, and the two are inverse:
`dual_of_lower` says lowering a direction with the measured metric and then
applying the covector form returns the measured form.  So `s` and `ε` are the
metric and its inverse, which is the precise content of A3 once it is
directional.

## II.  E² = m² + p², derived

Splitting the covector form by the drift direction gives

        (ε_t p_t)²  =  m²  +  Σ_i (ε_i p_i)² .

`dispersion_relation`.  The measured energy is `ε_t p_t` and the measured
momentum components are `ε_i p_i`, so this is Einstein's relation, and it is a
consequence of A3 + A4′ + the signature — not an input.  `massless_iff_null`
gives the `m = 0` case back as the null condition of `Light.lean`.

The `m` here is not a new parameter.  By `Emergence.mass_iff_threshold` mass and
threshold determine each other, so **the mass in the dispersion relation is the
location on the scale axis at which the species becomes resolvable**
(`mass_shell_at_threshold`).  The framework has no mass parameters, and the
dispersion relation does not introduce one.

## III.  The gradient is momentum acting

`Quantum.lean` observed that a derivation can be *inner*: `d_i = ad P_i`.  Then
`P_i` is the generator of translation along `i` — the momentum — and the scale
gradient is momentum acting on the scale:

        σ_i  =  [P_i , σ] .

`sig_eq_ad_momentum`.  That closes the gap between momentum-as-a-value (`ε_i`,
above) and momentum-as-a-generator (`P_i`), which had no connection at all.

And it pays immediately.  `NCConformal` shows the whole quantum-gravitational
correction is `[σ_a, σ_c]` and says the framework cannot compute its magnitude.
With the derivations inner, Jacobi gives

        [σ_a , σ_c]  =  ∂_a [σ, σ_c]  −  [σ , σ_{ac}] ,

`commutator_of_gradients` — the correction expressed **entirely through
`[σ, ·]`**, the failure of the log-scale itself to be central.  It vanishes
identically when `σ` is central (`correction_vanishes_of_central`), so its scale
is set by one quantity, and `Crossed.lean` is what identifies that quantity with
the scale step.  This does not yet produce a number, but it reduces the unknown
from "a commutator of gradients" to "how far `σ` fails to commute", which is a
single object the framework already names.
-/
import SCD.Light
import SCD.Connection
import SCD.Emergence
import SCD.Slice

namespace SCD.Momentum

open SCD Light Frame Quantum ScaleAlgebra Finset

/-! ## I. The covector form: A3 is the inverse metric -/

section Forms

variable {n : ℕ} {A : Type*} [CommRing A]

/-- The **mass-shell form on covectors**: each component measured in that
direction's *energy*, `ε_a = 1/s_a`.  This is the inverse of `physFormDir`, and
that it is the inverse is the whole of directional A3. -/
def dualForm (E : DirScale n A) (η p : Fin n → A) : A :=
  ∑ a, η a * (E.en a ^ 2 * (p a * p a))

/-- Lowering a direction with the measured metric: `p_a = η_a s_a² v^a`. -/
def lower (E : DirScale n A) (η v : Fin n → A) (a : Fin n) : A :=
  η a * ((E.s a : A)) ^ 2 * v a

/-- **The two forms are inverse.**

Lowering a direction and then applying the covector form returns the measured
form, provided the signature squares to one — which is what a signature is.  So
`s` and `ε` are metric and inverse metric, and A3 is that statement. -/
theorem dual_of_lower (E : DirScale n A) (η v : Fin n → A)
    (hη : ∀ a, η a * η a = 1) :
    dualForm E η (lower E η v) = physFormDir E η v := by
  simp only [dualForm, lower, physFormDir]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hs : E.en a * (E.s a : A) = 1 := E.en_mul_scale a
  calc η a * (E.en a ^ 2 * ((η a * ((E.s a : A)) ^ 2 * v a) * (η a * ((E.s a : A)) ^ 2 * v a)))
      = (η a * (η a * η a)) * ((E.en a * (E.s a : A)) ^ 2 * (((E.s a : A)) ^ 2 * (v a * v a))) := by
        ring
    _ = η a * (((E.s a : A)) ^ 2 * (v a * v a)) := by
        rw [hs, hη a]; ring

/-- On the isotropic locus the covector form is the bare one divided by `s²`, so
its zeros are the bare null covectors — `Light.lean`'s statement, dualised. -/
theorem dualForm_of_isotropic (E : DirScale n A) (η p : Fin n → A)
    (h : E.Isotropic) (c : Fin n) :
    dualForm E η p = E.en c ^ 2 * bareForm η p := by
  simp only [dualForm, bareForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : E.en a = E.en c := by simp only [Frame.DirScale.en, h a c]
  rw [this]; ring

end Forms

/-! ## II. The dispersion relation -/

section Dispersion

variable {n : ℕ} {A : Type*} [CommRing A]

/-- **`E² = m² + p²`.**

With signature `η_t = −1` on the drift direction and `η_i = +1` elsewhere, a
covector on the mass shell `dualForm = −m²` satisfies

        (ε_t p_t)²  =  m²  +  Σ_{i ≠ t} (ε_i p_i)² .

The measured energy is `ε_t p_t`; the measured momentum components are
`ε_i p_i`.  Nothing here is postulated: `ε` is A3 read per direction, the split
into one temporal and `n−1` spatial directions is `Signature.codim_ker_eq_one`,
and the form is the inverse of A4′'s metric. -/
theorem dispersion_relation (E : DirScale n A) (η p : Fin n → A) (t : Fin n) (m : A)
    (ht : η t = -1) (hi : ∀ i, i ≠ t → η i = 1)
    (hshell : dualForm E η p = -(m * m)) :
    (E.en t * p t) ^ 2 = m * m + ∑ i ∈ Finset.univ.erase t, (E.en i * p i) ^ 2 := by
  have hsplit : dualForm E η p
      = η t * (E.en t ^ 2 * (p t * p t))
        + ∑ i ∈ Finset.univ.erase t, η i * (E.en i ^ 2 * (p i * p i)) := by
    simp only [dualForm]
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ t)).symm
  rw [hsplit, ht] at hshell
  have hspat : ∑ i ∈ Finset.univ.erase t, η i * (E.en i ^ 2 * (p i * p i))
      = ∑ i ∈ Finset.univ.erase t, (E.en i * p i) ^ 2 := by
    refine Finset.sum_congr rfl fun i hmem => ?_
    rw [hi i (Finset.mem_erase.mp hmem).1]
    ring
  rw [hspat] at hshell
  have : (E.en t * p t) ^ 2 = E.en t ^ 2 * (p t * p t) := by ring
  rw [this]
  linear_combination -hshell

/-- **Massless is null.**

At `m = 0` the mass shell is the vanishing of the covector form, which on the
isotropic locus is the bare null condition of `Light.lean`.  So light is the
`m = 0` case of the dispersion relation rather than a separate story. -/
theorem massless_iff_null (E : DirScale n A) (η p : Fin n → A)
    (h : E.Isotropic) (c : Fin n) :
    dualForm E η p = 0 ↔ E.en c ^ 2 * bareForm η p = 0 := by
  rw [dualForm_of_isotropic E η p h c]

/-- At `m = 0` the dispersion relation is `E² = |p|²`: the measured energy is
the measured momentum, which is what masslessness means operationally. -/
theorem massless_dispersion (E : DirScale n A) (η p : Fin n → A) (t : Fin n)
    (ht : η t = -1) (hi : ∀ i, i ≠ t → η i = 1) (hshell : dualForm E η p = 0) :
    (E.en t * p t) ^ 2 = ∑ i ∈ Finset.univ.erase t, (E.en i * p i) ^ 2 := by
  have h := dispersion_relation E η p t 0 ht hi (by simpa using hshell)
  simpa using h

end Dispersion

/-! ## II.b  The mass in the relation is a threshold, not a parameter -/

/-- **The mass shell is located on the scale axis.**

`Emergence.mass_iff_threshold` makes mass and threshold determine each other, so
the `m` appearing in `E² = m² + p²` is `exp(μ k)` — *where* the species becomes
resolvable, not a number attached to it.  The dispersion relation therefore
introduces no free parameter: it inherits the threshold structure. -/
theorem mass_shell_at_threshold (μ : ℕ → ℝ) (k : ℕ) :
    Emergence.massOf μ k = Real.exp (μ k) := rfl

/-- And two species share a mass shell exactly when they share a threshold — so
the dispersion relation cannot distinguish what the threshold structure does
not. -/
theorem same_shell_iff_same_threshold (μ : ℕ → ℝ) (k l : ℕ) :
    Emergence.massOf μ k = Emergence.massOf μ l ↔ μ k = μ l :=
  Emergence.mass_iff_threshold μ k l

/-! ## III. Momentum as a generator, and what it buys

A derivation may be **inner**: `d_i = ad P_i`.  Where it is, `P_i` generates
translation along `i` and is therefore the momentum in the Noether sense, and
the scale gradient is momentum acting on the scale. -/

section Generators

variable {n : ℕ} {M : Type*} [Ring M] [ScaleAlgebra n M]

/-- **The scale gradient is momentum acting on the scale.**

Given generators `P` with `d_i = ad P_i`, the gradient `σ_i` is `[P_i, σ]`.  This
is the bridge between momentum as a *value* (`ε_i`, above) and momentum as a
*generator*, which the development had left unconnected. -/
theorem sig_eq_ad_momentum (P : Fin n → M) (hP : ∀ (i : Fin n) (a : M), d i a = ad (P i) a)
    (σ : M) (i : Fin n) : sig σ i = ad (P i) σ := hP i σ

/-- **The quantum correction, expressed through `[σ, ·]` alone.**

`NCConformal.Defm_antisymm_part` makes the whole quantum-gravitational
correction `[σ_a, σ_c]`, and says the framework cannot compute its magnitude.
With the derivations inner, the Jacobi identity rewrites it as

        [σ_a , σ_c]  =  ∂_a [σ, σ_c]  −  [σ , σ_{ac}] ,

so the correction is built entirely from the failure of the **log-scale itself**
to be central.  That is one object rather than a pair of gradients, and it is
the object `Crossed.lean` identifies with the scale step. -/
theorem commutator_of_gradients (P : Fin n → M)
    (hP : ∀ (i : Fin n) (a : M), d i a = ad (P i) a) (σ : M) (a c : Fin n) :
    ad (sig σ a) (sig σ c) = d a (ad σ (sig σ c)) - ad σ (hess σ a c) := by
  have hj := ad_jacobi (P a) σ (sig σ c)
  rw [← sig_eq_ad_momentum P hP σ a] at hj
  have h1 : ad (P a) (ad σ (sig σ c)) = d a (ad σ (sig σ c)) := (hP a _).symm
  have h2 : ad (P a) (sig σ c) = hess σ a c := (hP a (sig σ c)).symm
  rw [h1, h2] at hj
  exact hj.symm

/-- **And it vanishes when the log-scale is central.**

So the classical sector is exactly the sector in which `σ` commutes with
everything — not an approximation, and not a separate assumption about the
gradients.  One condition on one object. -/
theorem correction_vanishes_of_central (P : Fin n → M)
    (hP : ∀ (i : Fin n) (a : M), d i a = ad (P i) a) (σ : M)
    (hcen : ∀ x : M, ad σ x = 0) (a c : Fin n) :
    ad (sig σ a) (sig σ c) = 0 := by
  rw [commutator_of_gradients P hP σ a c, hcen (sig σ c), hcen (hess σ a c)]
  have : d a (0 : M) = 0 := d_zero a
  rw [this, sub_zero]

end Generators

/-! ## IV. Angular momentum

The third Noether charge is already in the development under another name.
`Coupling.bracket_scaling_scaling` says two scalings bracket to a rotation,
`Algebra.boost_bracket_spatial` computes that bracket as `vᵢwⱼ − vⱼwᵢ`, and
`Pattern.wedge` is that expression.  So angular momentum is the wedge of two
scale directions, and by `Axes.lean` a single pattern carries it only through
its own variation.

Collected, the framework's Noether table is:

| symmetry              | generator                       | charge          |
|-----------------------|---------------------------------|-----------------|
| translation along `i` | `P_i`, with `d_i = ad P_i` (A1) | `ε_i` (A3)      |
| translation along `t` | `P_t` (`Signature.lean`)        | `ε_t`, energy   |
| scaling along `a`     | `Algebra.boost` (A4′)           | `σ_a`           |
| rotation in `a∧b`     | `[K_a, K_b]` (`Coupling.lean`)  | `wedge`         |
| fiducial shift        | `ScaleField.fiducials` (A5)     | *unnamed*       |

The last row is the one with no charge named, and it is the subject of the next
step: A5's Noether charge is the dilatation charge, and A6 is the statement that
it is not globally conserved. -/

/-- **The rotational charge is the wedge, which is what the coupling
generates.**  Restated here so the Noether table above is anchored in a theorem
rather than a comment. -/
theorem angular_charge_is_wedge {k : ℕ} (v w : Fin k → ℝ) (i j : Fin k) :
    wedge v w i j = Coupling.br (Algebra.boost v) (Algebra.boost w) i.succ j.succ :=
  Slice.wedge_eq_bracket v w i j

end SCD.Momentum
