/-
# Off the commuting locus: Ricci is not symmetric, and the scalar curvature does
# not move

§V.ba found that everything the framework has computed sits on the isotropic,
commuting locus, and that both unfinished sectors are off it.  This file leaves
it, and contracts the non-commutative Riemann tensor to Ricci and to the scalar
— the step `NCConformal.lean` set up and did not take.

## The results

`sum_RmCorr_contract` — **the Riemann correction dies in the Ricci
contraction.**  `RmCorr a b c e` carries `δ_{ab}` and `δ_{bc}` with opposite
signs, and at `c = a` they cancel term by term.  So whatever Ricci inherits, it
does not inherit through `RmCorr`.

`two_Ric_eq_nc` — `2 Ric_{be} = (2−n) D_{be} − δ_{be} tr D`, the classical shape
with no extra term.

`two_Ric_antisymm` — and yet:

        **Ric_{be} − Ric_{eb} = (n−2)·[σ_b, σ_e]** ,

because `D` itself is not symmetric off the locus.

`two_RscBare_eq_nc` — `2 Rsc = (2−2n) tr D`, and `tr D` is built from `hess a a`,
`σ_aσ_a` and `gradsq`, every one of which is a square.

> **The whole quantum correction to the geometry is the antisymmetric part of
> Ricci.  The scalar curvature does not move at all.**

## What that predicts, and it is unusually sharp

**(1) An antisymmetric Ricci with a torsion-free connection.**  `Chr_symm` is
proved in the `[Ring M]` block — the connection is symmetric in its lower pair
whether or not the values commute, so there is **no torsion**.  In ordinary
differential geometry `Ric_{[ab]} = 0` for a torsion-free connection, by the
first Bianchi identity.  That identity's proof uses commutativity of the
**values**, not only torsion-freeness, and here the values do not commute.

So this is not Einstein–Cartan.  Einstein–Cartan buys an antisymmetric Ricci by
giving the connection torsion; here the connection stays torsion-free and the
antisymmetry comes from the ring.

**(2) Nothing classical moves — at any order.**  The scalar curvature is exactly
its commutative expression, so A6′/A6″, the coupling `κ`, the Newtonian limit and
every cosmological statement take **no quantum correction whatever**.  In
particular there is no `ℏG/r³` correction to the Newtonian potential, of the kind
effective-field-theory treatments of gravity produce, and no running of `G`.
That is a flat disagreement with the standard expectation and it is exact rather
than small.

**(3) It vanishes in two dimensions.**  The factor is `(n−2)`, the same one that
governs conformal geometry throughout the development.

**(4) Where it can appear.**  An antisymmetric Ricci in a field equation needs an
antisymmetric source, and the antisymmetric source in physics is **spin**.
`NCConformal.quantum_correction_is_a_wedge` says by `rfl` that the correction
*is* the framework's rotational label, which is the same statement from the other
side.

**(5) And it does not inherit §V.au's problem.**
`Micro.quantum_correction_signature_independent` shows the antisymmetric part is
the same for any signature, and the antisymmetric part is where the whole
correction lives.  So unlike `κ`, this prediction never depended on the pairing
that was never chosen.

## What is *not* claimed

That the correction couples to spin **as a theorem**.  No field equation for the
antisymmetric part is written here; `Dynamics.lean` derives conservation from
Bianchi for the symmetric setting and nothing has been said about the other half.
(4) is a reading of what an antisymmetric tensor can be equated to, and it is
labelled as one.

Nor any magnitude.  Calling `[σ_b, σ_e]` an `ℏ`-order effect goes through
`Crossed.lean`'s identification of `ℏ` with a scale step, which is a separate
input and is registered as one.

Nor existence: nothing here exhibits a scale algebra with non-commuting gradients
and a non-trivial geometry at once.  That is the same debt `ExpPoly.lean` paid
for `ScaleField`, and it is unpaid.
-/
import SCD.NCConformal

namespace SCD.QuantumRicci

open SCD Quantum Finset ScaleAlgebra NCConformal

variable {n : ℕ} {M : Type*} [Ring M] [ScaleAlgebra n M]
variable (σ : M)


/-- A commutator with itself vanishes. -/
theorem ad_self (x : M) : ad x x = 0 := by simp only [ad, sub_self]

/-- The Riemann correction contributes nothing to the Ricci contraction. -/
theorem sum_RmCorr_contract (b e : Fin n) :
    ∑ a, RmCorr n σ a b a e = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  simp only [RmCorr, ad_self, mul_zero, add_zero, kron_symm a b]
  noncomm_ring

/-- **Ricci, contracted without commutativity.**

`2 Ric_{be} = (2−n) D_{be} − δ_{be} tr D` — the classical shape, with no extra term,
because the Riemann correction dies in the contraction. -/
theorem two_Ric_eq_nc (b e : Fin n) :
    2 * Ric σ b e
      = (2 - (n : M)) * Defm n σ b e - (kron b e : M) * ∑ a, Defm n σ a a := by
  have h : ∀ a : Fin n, 2 * Rm σ a b a e
      = (kron a e : M) * Defm n σ b a - (kron a a : M) * Defm n σ b e
        + (kron b a : M) * Defm n σ a e - (kron b e : M) * Defm n σ a a
        + 2 * RmCorr n σ a b a e := fun a => two_Rm_eq_nc σ a b a e
  have hR : 2 * Ric σ b e = ∑ a : Fin n, 2 * Rm σ a b a e := by
    simp only [Ric, Finset.mul_sum]
  rw [hR, Finset.sum_congr rfl (fun a _ => h a)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_kron_left,
    sum_kron_right, kron_self, one_mul, ← Finset.mul_sum,
    sum_const_fin]
  rw [sum_RmCorr_contract σ b e]
  noncomm_ring

/-- **The antisymmetric part of Ricci is the commutator of scale gradients.**

`Ric_{be} − Ric_{eb} = (n−2)[σ_b, σ_e]`, and the connection is torsion-free
(`Chr_symm` holds over a `Ring`).  In ordinary differential geometry a
torsion-free connection has symmetric Ricci; that argument uses commutativity of
the **values**. -/
theorem two_Ric_antisymm (b e : Fin n) :
    2 * Ric σ b e - 2 * Ric σ e b
      = 2 * ((n : M) - 2) * ad (sig σ b) (sig σ e) := by
  have key : 2 * Ric σ b e - 2 * Ric σ e b
      = (2 - (n : M)) * (Defm n σ b e - Defm n σ e b) := by
    rw [two_Ric_eq_nc σ b e, two_Ric_eq_nc σ e b, kron_symm b e]
    noncomm_ring
  rw [key, Defm_antisymm_part σ b e]
  noncomm_ring

/-- **And the scalar curvature carries no correction at all.**

`tr D` is built from `hess a a`, `σ_aσ_a` and `gradsq`, every one a square.  So
the source law, `κ`, the Newtonian limit and every cosmological statement are
exactly classical — at any order. -/
theorem two_RscBare_eq_nc :
    2 * RscBare n σ = (2 - 2 * (n : M)) * ∑ a : Fin n, Defm n σ a a := by
  have h : ∀ b : Fin n, 2 * Ric σ b b
      = (2 - (n : M)) * Defm n σ b b - ∑ a : Fin n, Defm n σ a a := by
    intro b
    rw [two_Ric_eq_nc σ b b, kron_self, one_mul]
  have hR : 2 * RscBare n σ = ∑ b : Fin n, 2 * Ric σ b b := by
    simp only [RscBare, Finset.mul_sum]
  rw [hR, Finset.sum_congr rfl (fun b _ => h b)]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_const_fin]
  noncomm_ring

end SCD.QuantumRicci
