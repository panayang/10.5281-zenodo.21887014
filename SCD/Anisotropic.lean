/-
# The anisotropic sector, and the anisotropic non-commutative one

`Unify.lean` closed with the outstanding item: *what this file does not do is
compute curvature in the anisotropic sector.*  This is that computation's
starting point, and the first thing it does is refute a guess of mine.

## The carrier: A2 applied in each of A4′'s directions

A4′ gives one unit per direction and A2 gives every unit a log-scale, so the
object is one **scale field per direction** — `DirField` below.  The isotropic
locus is where they all agree, and every isotropic statement is recovered by
the embedding `ofScalar`.

## A guess, refuted

I had suggested that anisotropy produces **torsion** classically, on the grounds
that the scale index `a` and the derivative index `i` are different indices with
no `d_comm` relating them.  That is true of `∂_i σ_a` and false of the
connection: `ChrDir_symm` shows the anisotropic Christoffel symbol is still
symmetric in its lower pair.  A Levi-Civita connection is torsion-free whatever
the metric is, and the metric here is still a metric.  The guess is withdrawn.

## What is actually there, and it is measurable

The anisotropic connection differs from the isotropic one by a **ratio of
directional scales**:

        Γ^u_{ab}  =  δ_ub ∂_a σ_u + δ_ua ∂_b σ_u  −  δ_ab (η_a/η_u)(s_a/s_u)² ∂_u σ_a ,

and only the last term differs — by the factor `(s_a/s_u)²`, which is `1`
exactly on the isotropic locus (`ChrDir_of_isotropic`).  So the whole
anisotropic correction to the geometry is controlled by
`(s_a/s_u)² − 1` (`ChrDir_sub_Chr`).

**Correction, and it withdraws a crisis I announced.**  I read that ratio as an
observable anisotropy of the speed of light and set it against the `10⁻¹⁸`
Michelson–Morley bound, calling it the framework's sharpest constraint.  That was
wrong: `Light.physFormDir_eq_bareForm_rescaled` shows the measured form is the
bare form in rescaled axes, so the **pointwise** ratio is a frame choice, and
`Light.michelson_morley_null` shows the null result is a theorem for every
pattern.  Nothing bounds `(s_a/s_u)²` pointwise, there is no tension with
`PPN.lean`, and `spatial_anisotropy_is_what_is_bounded` — my proposed escape — is
not needed.

What is left is the correct statement, and it is the one the development always
made: the correction is a **ratio**, and ratios of the scale at a single point
are gauge.  The anisotropic sector's physical content is in how that ratio
*varies*, which is curvature, and in the antisymmetric residue that no rescaling
can remove (`Pattern.wedge_rescale_ne_zero`).

## The non-commutative anisotropic sector

Here the sector earns its name.  In `NCConformal.lean` there is one log-scale
and the correction is `[∂_a σ, ∂_b σ]` — **second order in gradients**.  With one
log-scale per direction there is a new object available:

        [σ_a , σ_b] ,

**zeroth order in gradients**, and it has no isotropic analogue at all: on the
isotropic locus all the `σ_a` are one element and it vanishes identically
(`dirCommutator_isotropic`).

So the anisotropic non-commutative sector carries a quantum correction that is
parametrically *larger* than the isotropic one — ahead of it by two derivatives.
`dirCommutator_is_leading` names the comparison.

**Two corrections, from `NCSize.lean`, and they matter.**

* **"Zeroth order in gradients" is withdrawn.**  That describes how the
  expression is *written*.  In the only non-commutative algebra the development
  constructs — `Deformation.lean`'s first-order deformation — the commutator is
  `ħ` times a Poisson bracket, and `NCSize.dir_commutator_star` evaluates it to
  `ħ(∂_qσ_a ∂_pσ_b − ∂_qσ_b ∂_pσ_a)`: **two gradients and an explicit `ħ`.**  The
  *relative* claim survives (the isotropic one carries four), so this sector is
  still the leading one; what is withdrawn is that it is unsuppressed.
* **And `dirCommutator_is_leading` proves none of it.**  It is `⟨rfl, rfl⟩` —
  two definitional unfoldings — with the whole order-counting argument in this
  docstring.  `NCSize.leading_claim_has_no_failing_instance` applies
  `Anchor.Falsifiable` to it.

**And the effect vanishes where it would be measured.**  The bracket is a wedge
of two gradients, so collinear scale gradients kill it
(`NCSize.collinear_gradients_kill_it`) — and staticity plus spherical symmetry is
exactly collinearity.  So it is identically zero in the Schwarzschild
configuration, which is the solar-system laboratory.  It is sourced by the
*departure* from spherical symmetry, and is not identically zero as algebra
(`NCSize.correction_is_not_identically_zero`).

And unlike the symmetric anisotropy it is **not gauge**: a per-direction
rescaling multiplies a wedge by a unit and can never cancel it
(`Pattern.wedge_rescale_ne_zero`), and `dirCommutator_is_wedge` says this
correction *is* a wedge.  So the antisymmetric part is the framework's only
pointwise observable beyond the signature, and it is where any bound must come
from.

**Why no number has been put on it** — `NCSize.lean` §V.  The object has weight
two under `σ ↦ cσ`, so it is a squared log-scale rather than an energy, and
converting it into the energy shift a co-magnetometer measures needs a coupling
of the rotational label to matter.  The framework has no matter sector.  That is
the single missing item, and it is nameable rather than a fog.
-/
import SCD.Light
import SCD.NCConformal

namespace SCD.Anisotropic

open SCD ScaleAlgebra Frame Quantum Finset

/-! ## I. The carrier -/

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-- A **directional scale field**: A2 applied in each of A4′'s directions — one
log-scale, and one unit representing it, per direction. -/
def DirField (n : ℕ) (A : Type*) [CommRing A] [ScaleAlgebra n A] : Type _ :=
  Fin n → ScaleField n A

namespace DirField

variable (E : DirField n A)

/-- The unit in direction `a`. -/
def s (a : Fin n) : Aˣ := (E a).s

/-- The log-scale in direction `a`. -/
def lg (a : Fin n) : A := (E a).σ

/-- The underlying A4′ datum: forgetting the log-scales gives a `DirScale`. -/
def toDirScale : DirScale n A := ⟨E.s⟩

/-- **The anisotropy**: the difference of two directional log-scales.  It
vanishes for every pair exactly on the isotropic locus, so it is the order
parameter of this sector. -/
def anis (a b : Fin n) : A := E.lg a - E.lg b

@[simp] theorem anis_self (a : Fin n) : E.anis a a = 0 := sub_self _

theorem anis_antisymm (a b : Fin n) : E.anis a b = -E.anis b a := by
  simp only [anis]; ring

/-- Every scalar scale field embeds as an isotropic directional one. -/
def ofScalar (F : ScaleField n A) : DirField n A := fun _ => F

@[simp] theorem ofScalar_lg (F : ScaleField n A) (a : Fin n) : (ofScalar F).lg a = F.σ := rfl
@[simp] theorem ofScalar_s (F : ScaleField n A) (a : Fin n) : (ofScalar F).s a = F.s := rfl

@[simp] theorem ofScalar_anis (F : ScaleField n A) (a b : Fin n) :
    (ofScalar F).anis a b = 0 := sub_self _

/-- The embedded field is isotropic in the sense of `Frame.lean`. -/
theorem ofScalar_isotropic (F : ScaleField n A) :
    (ofScalar F).toDirScale.Isotropic := fun _ _ => rfl

/-- The **anisotropic gradient**: `∂_i σ_a`, a matrix with the scale index and
the derivative index in different slots.  Unlike the Hessian it has no symmetry
to lose, because `d_comm` relates derivative indices and `a` is not one. -/
def grad (a i : Fin n) : A := sig (E.lg a) i

theorem grad_ofScalar (F : ScaleField n A) (a i : Fin n) :
    (ofScalar F).grad a i = sig F.σ i := rfl

end DirField

/-! ## II. The connection, and the guess it refutes -/

open DirField

/-- The **anisotropic Christoffel symbol** of `g_ab = η_a s_a² δ_ab`:

        Γ^u_{ab} = δ_ub ∂_a σ_u + δ_ua ∂_b σ_u − δ_ab (η_a η_u)(s_a s_u⁻¹)² ∂_u σ_a .

The signature enters as `η_a η_u` rather than `η_a/η_u` because `η` squares to
one; the scale enters as the **ratio** `s_a/s_u`, which is what makes this
different from the isotropic case and what makes the difference measurable. -/
def ChrDir (E : DirField n A) (η : Fin n → A) (u a b : Fin n) : A :=
  (kron u b : A) * E.grad u a + (kron u a : A) * E.grad u b
    - (kron a b : A) * ((η a * η u) * (((E.s a * (E.s u)⁻¹ : Aˣ) : A)) ^ 2 * E.grad a u)

/-- **The anisotropic connection is still symmetric in its lower pair.**

So there is no classical torsion here, and the suggestion that the two index
types would produce some is withdrawn.  A Levi-Civita connection is torsion-free
whatever the metric is; anisotropy changes the metric, not that. -/
theorem ChrDir_symm (E : DirField n A) (η : Fin n → A) (u a b : Fin n) :
    ChrDir E η u a b = ChrDir E η u b a := by
  by_cases h : a = b
  · subst h; rfl
  · simp only [ChrDir, show (kron a b : A) = 0 from if_neg h,
      show (kron b a : A) = 0 from if_neg (Ne.symm h)]
    ring

/-- **On the isotropic locus with Euclidean signature it is `Conformal.Chr`.**

The scale ratio is `1` and the two log-scales coincide, so every term matches the
conformal computation exactly.  Nothing proved in the isotropic sector is lost;
it is the `s_a = s_u` case. -/
theorem ChrDir_of_isotropic (F : ScaleField n A) (η : Fin n → A)
    (hη : ∀ a, η a = 1) (u a b : Fin n) :
    ChrDir (ofScalar F) η u a b = Chr F.σ u a b := by
  simp only [ChrDir, Chr, grad_ofScalar, ofScalar_s, hη]
  rw [show ((F.s * (F.s)⁻¹ : Aˣ) : A) = 1 by
    rw [mul_inv_cancel]; rfl]
  ring

/-- **The whole anisotropic correction is a ratio of directional scales.**

Subtracting the isotropic connection built from the same gradients leaves one
term, carrying the factor `(s_a/s_u)² − 1`.  That factor is the anisotropy, and
it is `0` exactly on the isotropic locus. -/
theorem ChrDir_sub_Chr (E : DirField n A) (η : Fin n → A) (hη : ∀ a, η a = 1)
    (u a b : Fin n) :
    ChrDir E η u a b
      - ((kron u b : A) * E.grad u a + (kron u a : A) * E.grad u b
          - (kron a b : A) * E.grad a u)
      = -((kron a b : A)
            * ((((E.s a * (E.s u)⁻¹ : Aˣ) : A)) ^ 2 - 1) * E.grad a u) := by
  simp only [ChrDir, hη]
  ring

/-- **And the correction vanishes exactly where the two directional units
agree** — so "isotropic sector" and "the correction is absent" are the same
condition, not two. -/
theorem ChrDir_correction_zero_of_eq (E : DirField n A) (u a : Fin n)
    (h : E.s a = E.s u) : ((((E.s a * (E.s u)⁻¹ : Aˣ) : A)) ^ 2 - 1) = 0 := by
  rw [h, mul_inv_cancel]
  simp

/-! ## III. What bounds it — and what does not

The correction is built from `(s_a/s_u)²`.  At a single point that ratio is a
**frame choice** (`Light.physFormDir_eq_bareForm_rescaled`), so nothing
interferometric bounds it, and the crisis this section originally announced is
withdrawn.  What remains is the identity itself, which is still worth having:
the correction and the optical ratio are one expression, and both are gauge at a
point and physical only through their variation. -/

/-- **The anisotropic correction and the light-speed anisotropy are the same
quantity.**

The connection's correction carries `(s_a s_u⁻¹)²`, and the null condition
carries `s_a²` against `s_u²`.  So a bound on optical anisotropy is a bound on
the anisotropic sector's departure from the isotropic geometry, with no model in
between. -/
theorem correction_is_optical_anisotropy (E : DirField n A) (u a : Fin n) :
    (((E.s a * (E.s u)⁻¹ : Aˣ) : A)) ^ 2 * ((E.s u : A)) ^ 2 = ((E.s a : A)) ^ 2 := by
  have h : ((E.s a * (E.s u)⁻¹ : Aˣ) : A) * ((E.s u : A)) = ((E.s a : A)) := by
    rw [Units.val_mul]
    calc ((E.s a : A)) * (((E.s u)⁻¹ : Aˣ) : A) * ((E.s u : A))
        = ((E.s a : A)) * ((((E.s u)⁻¹ : Aˣ) : A) * ((E.s u : A))) := by ring
      _ = ((E.s a : A)) := by rw [(E.s u).inv_mul, mul_one]
  calc (((E.s a * (E.s u)⁻¹ : Aˣ) : A)) ^ 2 * ((E.s u : A)) ^ 2
      = (((E.s a * (E.s u)⁻¹ : Aˣ) : A) * ((E.s u : A))) ^ 2 := by ring
    _ = ((E.s a : A)) ^ 2 := by rw [h]

/-- **Kept, with its motivation withdrawn.**

This was written as the escape from a tension between `PPN.lean`'s required
`O(1)` temporal–radial anisotropy and a supposed `10⁻¹⁸` bound on spatial
anisotropy.  There is no such bound (`Light.michelson_morley_null`), so no
escape is needed.  The statement is retained because it is true and because the
reasoning that produced it should stay visible: the conclusion was right and the
argument was not. -/
theorem spatial_anisotropy_is_what_is_bounded (E : DirField n A) (i j : Fin n)
    (hbound : E.s i = E.s j) :
    (((E.s i * (E.s j)⁻¹ : Aˣ) : A)) ^ 2 = 1 := by
  rw [hbound, mul_inv_cancel]
  simp

/-! ## IV. The non-commutative anisotropic sector

With one log-scale per direction a commutator is available that the isotropic
sector cannot form. -/

section NonCommutative

variable {M : Type*} [Ring M]

/-- **The directional commutator** `[σ_a, σ_b]`: the failure of two *directional
log-scales* to commute.  It is zeroth order in derivatives. -/
def dirCommutator (σ : Fin n → M) (a b : Fin n) : M := ad (σ a) (σ b)

@[simp] theorem dirCommutator_self (σ : Fin n → M) (a : Fin n) :
    dirCommutator σ a a = 0 := by
  simp only [dirCommutator, ad, sub_self]

theorem dirCommutator_antisymm (σ : Fin n → M) (a b : Fin n) :
    dirCommutator σ a b = -dirCommutator σ b a := by
  simp only [dirCommutator, ad]
  noncomm_ring

/-- **It vanishes identically on the isotropic locus.**

Where all the directional log-scales are one element, the commutator is that
element with itself.  So this correction has *no isotropic analogue whatever* —
it is not a small isotropic term made smaller, it is absent there and present
here. -/
@[simp] theorem dirCommutator_isotropic (σ₀ : M) (a b : Fin n) :
    dirCommutator (fun _ => σ₀) a b = 0 := by
  simp only [dirCommutator, ad, sub_self]

/-- **The directional commutator is the wedge of the log-scale pattern with
itself.**

`Pattern.wedge_self_eq_commutator` again: the object is the framework's own
rotational label evaluated on the directional log-scale.  So the anisotropic
quantum correction is a rotational label, exactly as
`NCConformal.quantum_correction_is_a_wedge` says of the isotropic one — but of
the pattern rather than of its gradient. -/
theorem dirCommutator_is_wedge (σ : Fin n → M) (a b : Fin n) :
    dirCommutator σ a b = wedge σ σ a b := rfl

/-- **And it is the leading correction, ahead of the isotropic one by two
derivatives.**

`NCConformal.Defm_antisymm_part` makes the isotropic correction
`[∂_a σ, ∂_b σ]` — second order in gradients.  This one is `[σ_a, σ_b]`, zeroth
order.  Both are commutators of scale data; they differ in how many derivatives
sit inside them, and that is the whole comparison.

**This theorem is `⟨rfl, rfl⟩` and proves neither claim.**  Both sides of each
component are definitionally equal; the order counting is entirely in this
docstring.  `NCSize.leading_claim_has_no_failing_instance` records that, and
`NCSize.dir_commutator_star` supplies what the counting actually gives: the
directional correction is `ħ` times **two** gradients and the isotropic one `ħ`
times **four**, so the comparison stands and the earlier gloss — "not
derivative-suppressed" — does not. -/
theorem dirCommutator_is_leading [ScaleAlgebra n M] (σ : Fin n → M) (a b : Fin n) :
    dirCommutator σ a b = ad (σ a) (σ b)
    ∧ ad (sig (σ a) a) (sig (σ b) b) = ad (d a (σ a)) (d b (σ b)) :=
  ⟨rfl, rfl⟩

end NonCommutative

end SCD.Anisotropic
