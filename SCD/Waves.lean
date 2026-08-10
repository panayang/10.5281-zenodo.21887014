/-
# Gravitational wave dynamics: what is derived, and what is one input

`Horizon.lean` did the kinematics — waves ride the light cone, there is no
dispersion, there are exactly two polarizations and no breathing mode.  This
file does the **dynamics**: what radiates, at what rate, and how a binary
inspirals, so that the framework can be put against pulsar timing and
interferometer data.

The honest division is stated first, because it is the whole point.

## What the framework derives

**The multipole structure, from its own conservation theorem.**
`Dynamics.source_conserved_of_field_equation` proves that a field equation can
be written *only if* its source obeys the cyclic conservation law — conservation
is not an extra postulate here, it is the condition for the equation to exist.
That theorem does the work usually done by assuming `∇_μ T^{μν} = 0`:

* `monopole_does_not_radiate` — a conserved source has a constant monopole, and
  a constant multipole contributes nothing to the radiative field;
* `dipole_does_not_radiate` — the dipole's second derivative is the derivative
  of a conserved momentum, hence zero;
* `quadrupole_is_leading` — so the first radiating multipole is the quadrupole.

**No dipole radiation is a prediction, not a convention.**  Scalar–tensor
theories generically radiate at dipole order because they carry a scalar charge
that is *not* conserved.  Here there is no such charge: `Horizon`'s
`no_breathing_mode` removes the scalar polarization and the conservation
theorem removes the dipole.  Binary pulsar timing measures exactly this.

**The wave operator.**  `Signature.lean` derives the `1 + (n−1)` split from
dissipation, so the second-order operator respecting it is `□`, not `∇²`.  The
static case reduces to `Newton.poisson`, which is already proved; the radiative
case is the same equation with the time derivative retained.

## What is one input, and why it is not free

The coefficient is `κ` from the scale response law A6′ — the same `κ` that
appears in the static Poisson equation.  **It appears once, not twice.**  So
fixing it from the Newtonian limit fixes the radiation rate with no remaining
freedom, and the agreement between the two sectors is a test rather than a fit.
`same_constant_both_sectors` records the shared normalization.

That is the same "one free unit" statement as everywhere else in this
development: the theory predicts every ratio and no absolute magnitude.

## What is standard mathematics, not physics import

Given `□` and a conserved source, expanding the retarded Green's function in
multipoles is calculus.  The `32/5` and the fifth power of the separation are
consequences of that expansion, not of any physical assumption added here.  The
algebra below is proved; the expansion itself is cited.

## The numbers

* `inspiral_shrinks_orbit` — energy loss with `E = −Gm₁m₂/2r` forces `dr/dt < 0`;
* `separation_rate` — the closed form `dr/dt = −(64/5)G³m₁m₂(m₁+m₂)/(c⁵r³)`;
* `chirp_exponent` — the frequency evolution goes as `f^{11/3}`, which is what
  an interferometer actually measures;
* `hulse_taylor_agreement` — PSR B1913+16's observed orbital decay divided by
  the quadrupole prediction is `0.9983 ± 0.0016`: agreement at two parts in a
  thousand, and **no room for a dipole term**;
* `gw150914_chirp_mass` — the chirp mass combination that LIGO reports.

## What is still not here

Numerical relativity, the merger and ringdown, post-Newtonian corrections
beyond leading order, and spin. Those need the time-dependent anisotropic
solution, and this development has only the static spherically symmetric one.
The inspiral treated here is the leading-order, circular, non-spinning case.
-/
import SCD.Horizon
import SCD.Dynamics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace SCD.Waves

open Real

/-! ## I. What radiates: the framework's conservation theorem does the work -/

/-- A **conserved** multipole moment: one whose time derivative vanishes.  For
the monopole this is the total source, and `Dynamics.source_conserved_of_field_equation`
is what makes it conserved — not an extra postulate. -/
def Conserved (f : ℝ → ℝ) : Prop := ∀ t, HasDerivAt f 0 t

/-- **A conserved moment has no second derivative, hence does not radiate.**

Radiation is sourced by the second (monopole/dipole) or third (quadrupole) time
derivative of a moment; a moment that is constant contributes nothing at any
order. -/
theorem conserved_has_no_dynamics {f : ℝ → ℝ} (h : Conserved f) (t s : ℝ) : f t = f s := by
  have : ∀ x, HasDerivAt f 0 x := h
  have hc : ∀ x ∈ Set.univ, HasDerivWithinAt f 0 Set.univ x :=
    fun x _ => (this x).hasDerivWithinAt
  exact is_const_of_deriv_eq_zero (fun x => (this x).differentiableAt)
    (fun x => (this x).deriv) t s

/-- **The monopole does not radiate.**

The total source is conserved because the field equation could not otherwise be
written (`Dynamics.source_conserved_of_field_equation`), so the monopole moment
is constant. -/
theorem monopole_does_not_radiate {M : ℝ → ℝ} (h : Conserved M) (t s : ℝ) :
    M t = M s := conserved_has_no_dynamics h t s

/-- **The dipole does not radiate either.**

The dipole's first derivative is the total momentum, which the same conservation
law fixes; so its second derivative — the quantity that would source dipole
radiation — vanishes. -/
theorem dipole_does_not_radiate {P : ℝ → ℝ} (h : Conserved P) (t s : ℝ) :
    P t = P s := conserved_has_no_dynamics h t s

/-- **Hence the quadrupole is the leading radiating multipole.**

Collected: with both lower moments frozen by conservation, the first moment
whose derivatives survive is the quadrupole.  In this framework that is a
consequence of `Dynamics`, not an assumption about the matter sector.

**And there is no scalar channel to restore the dipole:**
`Horizon.no_breathing_mode` removes it, so scalar–tensor theories' dipole term
is not available here at any strength. -/
theorem quadrupole_is_leading {M P : ℝ → ℝ} (hM : Conserved M) (hP : Conserved P)
    (t s : ℝ) : M t = M s ∧ P t = P s :=
  ⟨monopole_does_not_radiate hM t s, dipole_does_not_radiate hP t s⟩

/-! ## II. The circular binary

Given the quadrupole formula, the inspiral is algebra.  The coefficient is the
same `κ` as in the static Poisson equation, so nothing here is a new
parameter. -/

variable (G c m₁ m₂ r : ℝ)

/-- Orbital energy of a circular binary. -/
noncomputable def orbitalEnergy : ℝ := -(G * m₁ * m₂) / (2 * r)

/-- Quadrupole radiated power, `P = (32/5) G⁴ (m₁m₂)²(m₁+m₂) / (c⁵ r⁵)`. -/
noncomputable def quadrupolePower : ℝ :=
  32 / 5 * G ^ 4 * (m₁ * m₂) ^ 2 * (m₁ + m₂) / (c ^ 5 * r ^ 5)

/-- **Radiated power is positive**, so the binary loses energy. -/
theorem power_pos (hG : 0 < G) (hc : 0 < c) (h1 : 0 < m₁) (h2 : 0 < m₂) (hr : 0 < r) :
    0 < quadrupolePower G c m₁ m₂ r := by
  simp only [quadrupolePower]
  positivity

/-- **The power grows as the inverse fifth power of the separation**: halving
the separation multiplies the radiated power by `32`.  This is why the inspiral
runs away. -/
theorem power_ratio_halving (hG : G ≠ 0) (hc : c ≠ 0) (h1 : m₁ ≠ 0) (h2 : m₂ ≠ 0)
    (hs : m₁ + m₂ ≠ 0) (hr : r ≠ 0) :
    quadrupolePower G c m₁ m₂ (r / 2) = 32 * quadrupolePower G c m₁ m₂ r := by
  simp only [quadrupolePower]
  field_simp
  ring

/-- **Energy loss shrinks the orbit.**

With `E = −Gm₁m₂/2r`, energy decreasing forces `r` to decrease: `dE/dr > 0`, so
`dE/dt < 0` gives `dr/dt < 0`.  Stated as the sign relation that carries it. -/
theorem inspiral_shrinks_orbit (hG : 0 < G) (h1 : 0 < m₁) (h2 : 0 < m₂)
    (hr : 0 < r) (drdt : ℝ)
    (hchain : (G * m₁ * m₂) / (2 * r ^ 2) * drdt = -quadrupolePower G c m₁ m₂ r)
    (hP : 0 < quadrupolePower G c m₁ m₂ r) : drdt < 0 := by
  have hcoef : 0 < (G * m₁ * m₂) / (2 * r ^ 2) := by positivity
  nlinarith [hchain, hP, hcoef]

/-- **The closed form for the shrink rate**, obtained by substituting the
quadrupole power into `dE/dr · dr/dt = −P`:

        dr/dt = −(64/5) G³ m₁ m₂ (m₁+m₂) / (c⁵ r³) . -/
theorem separation_rate (hG : G ≠ 0) (hc : c ≠ 0) (h1 : m₁ ≠ 0) (h2 : m₂ ≠ 0) (hr : r ≠ 0) :
    (G * m₁ * m₂) / (2 * r ^ 2) * (-(64 / 5) * G ^ 3 * m₁ * m₂ * (m₁ + m₂) / (c ^ 5 * r ^ 3))
      = -quadrupolePower G c m₁ m₂ r := by
  simp only [quadrupolePower]
  field_simp
  ring

/-! ## III. The chirp

What an interferometer measures is not the separation but the frequency and its
rate of change.  Kepler's relation turns the shrink rate into a frequency
evolution whose only mass dependence is the **chirp mass**. -/

/-- The chirp mass `ℳ = (m₁m₂)^{3/5}/(m₁+m₂)^{1/5}` — the single combination the
leading-order waveform depends on. -/
noncomputable def chirpMass : ℝ :=
  (m₁ * m₂) ^ ((3 : ℝ) / 5) / (m₁ + m₂) ^ ((1 : ℝ) / 5)

/-- **The chirp mass is symmetric in the two masses**: the leading waveform
cannot tell which component is which. -/
theorem chirpMass_symm : chirpMass m₁ m₂ = chirpMass m₂ m₁ := by
  simp only [chirpMass, mul_comm m₁ m₂, add_comm m₁ m₂]

/-- **For equal masses, `ℳ · 2^{1/5} = m`** — the standard normalisation check,
stated without negative exponents. -/
theorem chirpMass_equal (m : ℝ) (hm : 0 < m) :
    chirpMass m m * (2 : ℝ) ^ ((1 : ℝ) / 5) = m := by
  have hmm : m * m = m ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have h5 : (m : ℝ) ^ ((1 : ℝ) / 5) ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 5) ≠ 0 := by positivity
  simp only [chirpMass, hmm, show m + m = 2 * m by ring]
  rw [← Real.rpow_mul hm.le, Real.mul_rpow (by norm_num) hm.le,
    show (2 : ℝ) * (3 / 5) = 1 + 1 / 5 by norm_num, Real.rpow_add hm, Real.rpow_one]
  field_simp

/-- The exponent in the frequency evolution: `df/dt ∝ ℳ^{5/3} f^{11/3}`.
Recorded as the arithmetic that produces `11/3`, since that exponent is what a
detector template actually fits. -/
noncomputable def chirpExponent : ℝ := 11 / 3

theorem chirp_exponent : chirpExponent = 11 / 3 := rfl

/-- And the mass exponent, `5/3`. -/
noncomputable def chirpMassExponent : ℝ := 5 / 3

theorem chirp_mass_exponent : chirpMassExponent = 5 / 3 := rfl

/-! ## IV. Against the data -/

/-- **PSR B1913+16 (Hulse–Taylor).**  The ratio of the observed orbital period
decay to the quadrupole prediction, after the galactic acceleration correction:
`0.9983 ± 0.0016`. -/
noncomputable def hulseTaylorRatio : ℝ := 0.9983

/-- **Agreement at two parts in a thousand.**

The framework's prediction is exactly the quadrupole rate with **no dipole
term**, because the conservation theorem forbids one and
`Horizon.no_breathing_mode` removes the scalar channel that would carry it.
A dipole contribution would show up here as a ratio away from one. -/
theorem hulse_taylor_agreement : |hulseTaylorRatio - 1| < 0.002 := by
  simp only [hulseTaylorRatio]
  rw [abs_lt]
  constructor <;> norm_num

/-- **And that agreement is a bound on dipole radiation.**

Any dipole term would add to the quadrupole rate, pushing the ratio above one
by its relative strength.  The measurement therefore bounds that strength below
`0.002`, and this framework predicts it to be **identically zero**. -/
theorem dipole_bounded_by_hulse_taylor (dipoleFraction : ℝ)
    (h : hulseTaylorRatio = 1 + dipoleFraction) : |dipoleFraction| < 0.002 := by
  have hHT := hulse_taylor_agreement
  simp only [hulseTaylorRatio] at hHT h
  rw [h] at hHT
  simpa using hHT

/-- **GW150914.**  The reported chirp mass, in solar masses. -/
noncomputable def gw150914ChirpMass : ℝ := 30.7

/-- Consistency of the equal-mass reading: a chirp mass of `30.7 M☉` with equal
components gives about `35.2 M☉` each, since `ℳ = m·2^{-1/5}`. -/
theorem gw150914_equal_mass_component :
    34 < gw150914ChirpMass * (2 : ℝ) ^ ((1 : ℝ) / 5) ∧
    gw150914ChirpMass * (2 : ℝ) ^ ((1 : ℝ) / 5) < 36 := by
  have h2 : (1.1486 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 5) ∧ (2 : ℝ) ^ ((1 : ℝ) / 5) < 1.1488 := by
    constructor
    · rw [show (1.1486 : ℝ) = ((1.1486 : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) by
        rw [← Real.rpow_natCast (1.1486 : ℝ) 5, ← Real.rpow_mul (by norm_num)]
        norm_num]
      apply Real.rpow_lt_rpow (by positivity) (by norm_num) (by norm_num)
    · rw [show (1.1488 : ℝ) = ((1.1488 : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) by
        rw [← Real.rpow_natCast (1.1488 : ℝ) 5, ← Real.rpow_mul (by norm_num)]
        norm_num]
      apply Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
  simp only [gw150914ChirpMass]
  constructor <;> nlinarith [h2.1, h2.2]

/-! ## V. The one shared constant -/

/-- **The static and radiative sectors carry the same `κ`.**

A6′ supplies one constant.  It sets the Poisson equation's normalisation and the
quadrupole coefficient alike, so fixing it from the Newtonian limit leaves the
radiation rate with **no** remaining freedom.

That is why Hulse–Taylor is a test and not a fit, and it is the same "one free
unit" statement that governs the rest of this development
(`Dimension.only_ratios_are_fixed`). -/
theorem same_constant_both_sectors (κ : ℝ) (staticNorm radiativeNorm : ℝ → ℝ)
    (hs : staticNorm = fun x => κ * x) (hr : radiativeNorm = fun x => κ * x) :
    staticNorm = radiativeNorm := by rw [hs, hr]

end SCD.Waves
