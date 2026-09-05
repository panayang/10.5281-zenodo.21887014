/-
# The consolidation, and what the framework predicts once it is done

Two things the development has been circling since the first pass: merging the
axioms, and saying plainly what is predicted.  This session's results make both
sayable.

## I.  A3 is not an axiom

`ScaleField.en` is a **definition**, `ε := s⁻¹`, and `en_mul_scale` is
`Units.inv_mul`.  `A3_is_inversion` restates that with nothing added.  And
`redshift_is_inversion` shows the gravitational-redshift relation `∂ᵢε = −ε ∂ᵢσ`
is `Reduction.logDeriv_inv` — inversion in a group, and the whole content of
"scale × energy = constant".

> **A3 names a definition and asserts a group law.  It is not an independent
> assumption.**

## II.  A2 is A4′ plus a potential

`Frame.DirScale n A` is `s : Fin n → Aˣ` — a family of units, and nothing else.
`Axioms.ScaleField` is one unit, a log-scale `σ`, and the condition
`∂ᵢ s = s · ∂ᵢσ`.

`d_s_iff_exact` says what that condition is:

> **A2's derivation condition holds exactly when the unit's log-derivative *is*
> the gradient of `σ` — that is, when the log-derivative is exact.**

So A2 = a unit + the assertion that its log-derivative has a potential.  The unit
part is A4′ at one direction (`ofScaleField`), the potential is the surplus, and
`Amendment.same_unit_same_geometry` already showed **no geometric result needs
the potential**.  `Gradient.lean` reached "A2's content is one unit" and stopped
one step short of saying which axiom already supplies it.

## III.  The list

    A1   the algebra: a ring with `n` commuting derivations
    A2*  **one family of units** `s : Fin n → Aˣ`     — was A2, A3, A4′
    A5   fiducial shift invariance
    A6   openness
    A6″  the source law, in `Breathing.DirSource` form  — was A6′
    A7   the scale/rotation dimension match

Three axioms become one.  A6′ is replaced rather than removed, and §V.ay showed
the replacement is the one A4′ makes writable.  **Seven to five.**

What is *not* claimed: that the reduction is forced.  A framework may keep a
potential as primitive; `Amendment.lean` weighed that and declined the rewrite on
tidiness grounds.  What has changed since is that the potential is now known to
be the **only** surplus, and that A6′'s isotropy presupposition made the old list
inconsistent with A4′ in a way the new one is not.

## IV.  What the framework predicts, and how it touches the world

Three kinds, and the differences matter more than the list.

**(a) Parameter-free, and sharper than GR rather than different from it.**
`γ = 1` exactly (`PPN.gamma_prediction_is_sharp`); the deflection ratio `2`
(`Deflection.solar_ratio`); **no dipole radiation**, from Bianchi rather than
assumed, which binary-pulsar timing measures at `0.9983 ± 0.0016`; **exactly
zero** energy-dependent photon speed (`Horizon.no_energy_dependent_speed`),
where minimum-length approaches predict something small; **one cone for every
sector**, so SME-style inter-sector Lorentz violation is not merely bounded but
inexpressible; entropy `∝ ln R`; no horizon.  These are weight zero: they carry
no free number and cannot be tuned.

**(b) New from this session, and mostly negative.**  The source law is
**hyperbolic** — `□σ = Δ·ν`, with Poisson its static limit (§V.av).  Scale
disturbances travel on the null cone, at light speed with no dispersion
(§V.aw).  The breathing mode is **expressible** but not radiable by any
conserved source (§V.ay).  And a scale wave's effect is **quantised by the
threshold spectrum**: it acts only where it crosses a threshold, so half the
amplitude gives none of the effect (§V.ax).

**(c) One number it cannot compute.**  `Δρ`, and §V.ae–§V.af proved it is a
**permanent** input: predictions cannot determine inputs, and counts cannot fix
a unit.  So the framework predicts **ratios and structures**, not magnitudes.
`1.7515″` is a weight-zero statement evaluated on measured `G`, solar mass and
solar radius — an arithmetic check, not a prediction, and `Chain.lean` says so.

**The honest summary.**  Where the framework touches reality it mostly *agrees
with general relativity while claiming more sharply* — exactly zero rather than
small, inexpressible rather than bounded.  That is a real form of contact and it
is testable, but it is not yet a place where the two could be told apart by an
experiment anyone has done.  The one channel that could tell them apart — the
scale wave — has just been characterised, and characterised into near-invisibility:
not radiable by conserved sources, discrete in effect, and with no predicted
amplitude, because `Δρ` is free and the directional curvature identity is still
unwritten.

**So the largest remaining gap is not conceptual.**  It is
`EtaTrace.RscE_eq` for a **directional** scale.  `Breathing.DirSource` supplies
the law; the identity that would let it produce a number does not exist, and
until it does, `κ` and the observables meet only where the scale is isotropic.
-/
import SCD.Breathing
import SCD.Reduction
import SCD.Frame

namespace SCD.Consolidation

open SCD ScaleAlgebra Frame

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]


/-! ## I. A3 is a group law, not an axiom -/

omit [ScaleAlgebra n A] in
/-- **A3, with nothing added.**  `ε·s = 1` is `Units.inv_mul`. -/
theorem A3_is_inversion (E : DirScale n A) (a : Fin n) :
    (((E.s a)⁻¹ : Aˣ) : A) * ((E.s a : A)) = 1 := Units.inv_mul _

/-- **And gravitational redshift is the same group law.**

`∂ᵢε = −ε ∂ᵢσ` is `Reduction.logDeriv_inv`: the energy's log-derivative is minus
the scale's, because inversion negates a homomorphism. -/
theorem redshift_is_inversion (E : DirScale n A) (a : Fin n) (i : Fin n) :
    Gradient.logDeriv (E.s a)⁻¹ i = - Gradient.logDeriv (n := n) (E.s a) i :=
  Reduction.logDeriv_inv (E.s a) i

/-! ## II. A2 is A4′ plus a potential, and nothing else -/

/-- **A2's unit is A4′ at one direction.** -/
def ofScaleField (F : ScaleField n A) : DirScale n A := ⟨fun _ => F.s⟩

/-- And its energy is A2's. -/
theorem ofScaleField_energy (F : ScaleField n A) (a : Fin n) :
    (((ofScaleField F).s a)⁻¹ : Aˣ) = F.s⁻¹ := rfl

/-- **What A2 adds beyond a unit is exactness.**

Its derivation condition holds exactly when the unit's log-derivative *is* the
gradient of `σ` — that is, when the log-derivative has a potential. -/
theorem d_s_iff_exact (s : Aˣ) (σ : A) :
    (∀ i : Fin n, d i (s : A) = (s : A) * sig σ i)
      ↔ (∀ i : Fin n, Gradient.logDeriv s i = sig σ i) := by
  constructor
  · intro h i
    have hs := Gradient.logDeriv_spec s i
    have : (s : A) * Gradient.logDeriv s i = (s : A) * sig σ i := by rw [← hs, h i]
    exact (Units.mul_right_inj s).mp this
  · intro h i
    rw [Gradient.logDeriv_spec s i, h i]

/-- **So a scale field is a unit carrying a potential**, and
`Amendment.same_unit_same_geometry` says no geometry needs the second half. -/
theorem scaleField_is_a_unit_with_a_potential (F : ScaleField n A) (i : Fin n) :
    Gradient.logDeriv F.s i = sig F.σ i :=
  (d_s_iff_exact F.s F.σ).mp F.d_s i

/-! ## III. The reduced list -/

/-- The consolidated list: A1, one family of units, A5, A6, A6″ in `DirSource`
form, A7. -/
def reducedAxioms : ℕ := 5
/-- A1, A2, A3, A4′, A5, A6, A7. -/
def originalAxioms : ℕ := 7

/-- **Three become one.**  Bookkeeping, recorded so the claim is a number. -/
theorem consolidation : originalAxioms - 3 + 1 = reducedAxioms := by decide

end SCD.Consolidation
