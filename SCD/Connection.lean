/-
# Curvature is a commutator

The obvious way to get curvature for a directional scale would be to write down
Cartan's structure equations and grind.  That imports general relativity's
machinery wholesale — precisely the inertia worth avoiding.  There is a more
primitive route, and it identifies gravity with something already built here.

Ask what transport of the local unit actually *is*.  Moving in direction `i`
re-expresses everything in the neighbouring unit; that is an operator `D_i`.
Doing `i` then `j` need not agree with `j` then `i`.  The discrepancy is the
whole of curvature:

        F_{ij} = [D_i , D_j] .

This is the same construction as `Quantum.ad`.  There the transports were
phase-space translations and their failure to commute was `ħ`; here they are
frame transports and their failure to commute is gravity.  **Curvature and `ħ`
are one construction evaluated on two families of transports** — a stronger
statement than any analogy between the theories.

Proved below:

* `comm_covD` — `[D_i, D_j] m = [F_{ij}, m]`, with the Yang–Mills curvature
  `F_{ij} = ∂_i A_j − ∂_j A_i + [A_i, A_j]` *falling out* rather than posited.
  That the commutator acts algebraically on `m` is exactly the statement that
  curvature is a tensor;
* `bianchi` — the Bianchi identity, from the Jacobi identity of `ad`.
  Conservation of the gravitational field is associativity of transport;
* `curv_gradient_eq_zero` — a gradient connection is flat, recovering
  `scaleCurv_eq_zero` in the non-commutative setting;
* `curv_eq_rotation_part` — **the punchline.**  Split transport into its scale
  part (commuting, and by A5 a gradient) and its frame-rotation part.  The
  scale part contributes *exactly nothing*.  All of gravity lives in the
  non-commuting part of scale transport.

The last theorem is the anisotropic curvature the scalar axiom could not reach,
and it arrives without a single Christoffel symbol.
-/
import SCD.Quantum
import SCD.Basic

namespace SCD.Connection

open SCD Quantum ScaleAlgebra

/-! ## Transport, and its failure to commute

A1 is stated once, in `Basic.lean`, over a ring — it never needed the ring to be
commutative, only the Leibniz rule and equality of mixed partials.  An earlier
state of the development declared it a second time here as `DiffRing`, with an
instance and a `def` in `Postulates.lean` transporting between the two; both are
gone, and `ScaleAlgebra` is the one carrier. -/

variable {n : ℕ} {M : Type*} [Ring M] [ScaleAlgebra n M]

/-- **Covariant transport** in direction `i`: the bare derivation corrected by
the connection, acting on the frame by commutator. -/
def covD (A : Fin n → M) (i : Fin n) (m : M) : M := d i m + ad (A i) m

/-- **Curvature**: the object that will turn out to measure the failure of two
transports to commute.  It is written down here only so that it can be named;
`comm_covD` is what justifies the definition. -/
def F (A : Fin n → M) (i j : Fin n) : M :=
  d i (A j) - d j (A i) + ad (A i) (A j)

theorem F_antisymm (A : Fin n → M) (i j : Fin n) : F A i j = -F A j i := by
  simp only [F, ad]
  noncomm_ring


/-- **Curvature is the commutator of transports.**

`[D_i, D_j] m = [F_{ij}, m]`.

Two facts at once.  First, the Yang–Mills curvature is not postulated: it is
what the left-hand side evaluates to.  Second, the result acts on `m`
*algebraically* — no derivative of `m` survives — which is precisely the
statement that curvature is a tensor rather than a differential operator. -/
theorem comm_covD (A : Fin n → M) (i j : Fin n) (m : M) :
    covD A i (covD A j m) - covD A j (covD A i m) = ad (F A i j) m := by
  simp only [covD, F, ad, d_add, d_sub, d_mul]
  rw [d_comm i j m]
  noncomm_ring

/-- **Bianchi identity.**

The cyclic sum of covariant derivatives of the curvature vanishes.  It follows
from the Jacobi identity for `ad` together with equality of mixed partials:
the conservation law of the gravitational field is the associativity of
transport, and nothing else. -/
theorem bianchi (A : Fin n → M) (i j k : Fin n) :
    covD A i (F A j k) + covD A j (F A k i) + covD A k (F A i j) = 0 := by
  simp only [covD, F, ad, d_add, d_sub, d_mul]
  rw [d_comm j i (A k), d_comm k i (A j), d_comm k j (A i)]
  noncomm_ring

/-! ## Which part of transport actually curves -/

/-- An abelian connection has the familiar curl for its curvature. -/
theorem curv_of_central (A : Fin n → M) (hc : ∀ i (x : M), A i * x = x * A i)
    (i j : Fin n) : F A i j = d i (A j) - d j (A i) := by
  simp only [F, ad]
  rw [hc i (A j)]
  noncomm_ring

/-- **A gradient connection is flat.**

If the connection is the gradient of a scalar and commutes with itself, its
curvature vanishes identically — mixed partials commute.  This is
`scaleCurv_eq_zero` again, now in the non-commutative setting: the *scale* part
of transport is integrable, so there is no second clock effect no matter how
curved the geometry is. -/
theorem curv_gradient_eq_zero (σ : M) (hcomm : ∀ i j : Fin n, ad (d i σ) (d j σ) = 0)
    (i j : Fin n) : F (fun k => d k σ) i j = 0 := by
  simp only [F]
  rw [d_comm i j σ, hcomm i j]
  simp

/-- Splitting transport into a commuting part and a rotation part, the
commuting part contributes only its curl. -/
theorem curv_split (a ω : Fin n → M) (hcen : ∀ i (x : M), a i * x = x * a i)
    (i j : Fin n) :
    F (fun k => a k + ω k) i j = (d i (a j) - d j (a i)) + F ω i j := by
  simp only [F, ad, d_add, add_mul, mul_add]
  rw [hcen i (a j), hcen i (ω j), hcen j (ω i)]
  noncomm_ring

/-- **All curvature lives in the non-commuting part of scale transport.**

Write transport as its scale part — which by A5 is a gradient, hence
commuting and integrable — plus its frame-rotation part.  The scale part drops
out of the curvature *entirely*.

So gravity is not "the scale field bending space".  Gravity is the failure of
*frame rotations* to commute, while the scale itself transports integrably.
That is why an integrable Weyl geometry can carry gravity without producing the
second clock effect that killed Weyl's original theory — and it is the
anisotropic curvature that the scalar axiom A4 could not express. -/
theorem curv_eq_rotation_part (σ : M) (ω : Fin n → M)
    (hcen : ∀ (i : Fin n) (x : M), (d (n := n) i σ) * x = x * (d (n := n) i σ)) (i j : Fin n) :
    F (fun k => d k σ + ω k) i j = F ω i j := by
  rw [curv_split (fun k => d k σ) ω hcen i j, d_comm i j σ]
  simp

/-- Consequently a purely scalar (isotropic) transport is flat: the scalar
axiom could produce no curvature from the scale alone, which is the structural
reason it forbade Schwarzschild. -/
theorem curv_pure_scale_eq_zero (σ : M)
    (hcen : ∀ (i : Fin n) (x : M), (d (n := n) i σ) * x = x * (d (n := n) i σ)) (i j : Fin n) :
    F (fun k => d k σ) i j = 0 := by
  refine curv_gradient_eq_zero σ (fun p q => ?_) i j
  simp only [ad]
  rw [hcen p (d q σ)]
  noncomm_ring

end SCD.Connection
