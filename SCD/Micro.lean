/-
# The micro sector, and where it stands after the signature pass

§V.au found the classical coupling computed in the wrong pairing.  The obvious
next question is whether the **quantum** correction inherits the same problem.
It does not, and the reason says something about what the correction is.

## I.  The quantum correction does not see the pairing

`Conformal.Defm` is `2σᵢⱼ − 2σᵢσⱼ + δᵢⱼ|∇σ|²`, and the pairing enters through the
**last term only** — which `DefmE_symm_part` shows is symmetric in `ij` whatever
`η` is, because `δᵢⱼ` already forces the indices equal.

`NCConformal.Defm_antisymm_part` says the whole quantum-gravitational correction
is `Defm i j − Defm j i = −2[σᵢ, σⱼ]`.  So `DefmE_antisymm_part` gives the same
thing with `η` in place of `δ`, and
`quantum_correction_signature_independent` states the equality.

> **The pairing was never chosen (§V.at) and the quantum correction never needed
> it.**

`DefmE_sub_Defm` isolates where the pairing *does* matter: the symmetric part,
carrying `ηᵢ|∇σ|²_η − |∇σ|²`.  That is exactly the term §V.au and §V.av were
about, and it is exactly the part the classical tests read.

## II.  What the correction is, which is sharper than "a correction"

`NCConformal.quantum_correction_is_a_wedge` is proved by `rfl`:

        `ad (sig σ i) (sig σ j) = wedge (sig σ) (sig σ) i j` .

The quantum-gravitational correction **is** the framework's rotational label
applied to the scale gradient pattern.  Not analogous to it — the same term.  And
being antisymmetric it cannot enter anything computed from a symmetric part, so
orbits, deflection, precession and redshift are untouched by construction.

## III.  But every quantitative result is computed where it vanishes

`NCConformal` was written to close the loop, and it closes it **for the Riemann
tensor**: `Conformal.lean` is now over a `Ring`.  The chain is not.
`Diagonal.lean`, `Newton.lean`, `Reciprocity.lean` and `Chain.lean` — the files
`Chain.lean`'s own table runs the gravity chain through — all carry
`[CommRing A]`, and over a commutative ring `ad` vanishes identically
(`Dynamics.commutative_sector_transports_commute`).

> **The correction is identified exactly, and every number the framework
> computes is computed in a sector where it is zero by construction.**

That is not a small correction being neglected.  It is a term that has never been
carried into any quantitative statement, and saying "the quantum correction does
not affect the classical tests" is at present a statement about *where the
computation was done* as much as about the term's symmetry.

## IV.  A warning the register should record about itself

`Expressive.channels_independent` — that the scale and commutator channels
cannot constrain each other — is the obvious thing to quote here, and it is
**superseded**.  `Expressive.lean`'s own header says so: the independence is that
of the *scalar* scale channel, and `Coupling.lean` shows scalings along different
directions bracket into a rotation, so under A4′ the channels are **coupled**.
The correction being the wedge is that coupling, seen again.

This file was one sentence from quoting the superseded conclusion, and the file's
own warning is what stopped it.  That is the second time this session that a
header's self-correction did work no theorem could have done.

## V.  And it meets this session's other gap

The correction vanishes where the gradients commute
(`NCConformal.correction_vanishes_on_commuting`), and `Anisotropic`'s
directional commutator vanishes on the isotropic locus
(`dirCommutator_isotropic`).  §V.aw's bridge and §V.ax's source law also live on,
and only on, the isotropic locus.

> **Everything the framework has computed is on the isotropic, commuting locus;
> both of its unfinished sectors are off it.**

Two open items that looked unrelated — the missing directional source law and the
uncarried quantum correction — are open in the same place, and it is the place no
computation has yet been done.
-/
import SCD.NCConformal
import SCD.EtaTrace

namespace SCD.Micro

open SCD Quantum Finset ScaleAlgebra

variable {n : ℕ} {M : Type*} [Ring M] [ScaleAlgebra n M]


/-- The `η`-weighted squared gradient, over a ring. -/
def gsqE (η : Fin n → M) (σ : M) : M := ∑ i : Fin n, η i * (sig σ i * sig σ i)

/-- The deformation tensor with a signature in place of `δ`. -/
def DefmE (η : Fin n → M) (σ : M) (i j : Fin n) : M :=
  2 * hess σ i j - 2 * (sig σ i * sig σ j)
    + (kron i j : M) * (η i * gsqE η σ)

/-- **The signature enters `Defm` only symmetrically**, because `δᵢⱼ` already
forces the indices equal before `η` is read. -/
theorem DefmE_symm_part (η : Fin n → M) (σ : M) (i j : Fin n) :
    (kron i j : M) * (η i * gsqE η σ)
      = (kron j i : M) * (η j * gsqE η σ) := by
  by_cases h : i = j
  · subst h; rfl
  · simp only [show (kron i j : M) = 0 from if_neg h,
      show (kron j i : M) = 0 from if_neg (Ne.symm h), zero_mul]

/-- **So the quantum-gravitational correction is unchanged by the pairing.** -/
theorem DefmE_antisymm_part (η : Fin n → M) (σ : M) (i j : Fin n) :
    DefmE η σ i j - DefmE η σ j i = -2 * ad (sig σ i) (sig σ j) := by
  simp only [DefmE, ad, hess_symm σ i j, DefmE_symm_part η σ i j]
  noncomm_ring

/-- **And it is literally the same object the `δ` computation produced.** -/
theorem quantum_correction_signature_independent (η : Fin n → M) (σ : M) (i j : Fin n) :
    DefmE η σ i j - DefmE η σ j i = Defm n σ i j - Defm n σ j i := by
  rw [DefmE_antisymm_part η σ i j, NCConformal.Defm_antisymm_part σ i j]

/-- **Where the pairing does matter is the symmetric part** — which is what the
classical tests read, and where §V.au and §V.av live. -/
theorem DefmE_sub_Defm (η : Fin n → M) (σ : M) (i j : Fin n) :
    DefmE η σ i j - Defm n σ i j
      = (kron i j : M) * (η i * gsqE η σ - gradsq n σ) := by
  simp only [DefmE, Defm]
  noncomm_ring

end SCD.Micro
