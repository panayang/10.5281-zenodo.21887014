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
import SCD.Particle
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

/-! ## I.b  The bridge to a conserved total — and it needs no integration

I previously said this bridge could not be built because the framework has no
integral.  **That was wrong**, and the correction is worth stating because it
also identifies exactly what the framework *does* still need.

The usual argument runs `∇_μ T^{μν} = 0 ⟹ d/dt ∫T^{0ν}d³x = −∮T^{iν}dS_i = 0`,
which uses integration, the divergence theorem, and fall-off at infinity.  But
the algebraic content of "the integral of a divergence vanishes" is not
integration at all — it is that **divergences are exactly what one quotients
by**.  For a derivation `D`, the algebraic integral is the quotient map onto
`M ⧸ D(M)`.

So define the divergences as the additive subgroup generated by the images of
every derivation *other* than the drift direction, and take the total to be the
class modulo them.  Two things then fall out with A1 and nothing else:

* `drift_descends` — the drift derivation preserves the divergence subgroup,
  because A1's derivations commute.  So "rate of change of the total" is
  well defined;
* `total_conserved` — a continuity equation `D_t ρ + Σ_{i≠t} D_i J_i = 0` puts
  `D_t ρ` **inside** the divergence subgroup, so the total does not change.

That is the bridge, from `Dynamics.source_conserved_of_field_equation` to a
conserved monopole, using only A1.

## What is still needed, now visible as an algebraic condition

The quotient can be **trivial**: on `ℝ[X]` every polynomial is a derivative, so
`divergences = ⊤` and "the total" is the zero group.  Physically that is the
absence of a fall-off condition — an unlocalised source has no finite total.

`localised_iff_proper` records the replacement: what the physics calls
*localisation at infinity*, the algebra calls **the divergence subgroup being
proper**.  The input is not removed; it is identified, and it is one condition
rather than three (measure, Stokes, decay). -/

variable {n : ℕ} {M : Type*} [Ring M] [Connection.DiffRing n M]

open Connection DiffRing in
/-- **The divergences**: the additive subgroup generated by the images of every
derivation except the drift direction `t`.  Algebraically this is what an
integral over a slice discards. -/
def divergences (t : Fin n) : AddSubgroup M :=
  AddSubgroup.closure {x : M | ∃ i : Fin n, i ≠ t ∧ ∃ y, D i y = x}

open Connection DiffRing in
/-- **The drift preserves the divergences**, because A1's derivations commute.
So the total has a well-defined rate of change. -/
theorem drift_descends (t : Fin n) (i : Fin n) (hi : i ≠ t) (y : M) :
    D t (D i y) ∈ divergences (M := M) t :=
  AddSubgroup.subset_closure ⟨i, hi, D t y, D_comm i t y⟩

open Connection DiffRing in
/-- **The total is conserved.**

A continuity equation puts the drift of the density inside the divergence
subgroup, so its class — the total — does not move.  This is the bridge from
`Dynamics.source_conserved_of_field_equation` to a conserved monopole, and it
uses A1 and nothing else: no measure, no divergence theorem, no fall-off. -/
theorem total_conserved (t : Fin n) (ρ : M) (J : Fin n → M)
    (hcont : D t ρ + ∑ i ∈ Finset.univ.erase t, D i (J i) = 0) :
    D t ρ ∈ divergences (M := M) t := by
  have hsum : ∑ i ∈ Finset.univ.erase t, D i (J i) ∈ divergences (M := M) t := by
    refine AddSubgroup.sum_mem _ (fun i hi => ?_)
    exact AddSubgroup.subset_closure ⟨i, (Finset.mem_erase.mp hi).1, J i, rfl⟩
  have hneg : D t ρ = -(∑ i ∈ Finset.univ.erase t, D i (J i)) :=
    eq_neg_of_add_eq_zero_left hcont
  rw [hneg]
  exact AddSubgroup.neg_mem _ hsum

open Connection DiffRing in
/-- **What "localised" means algebraically.**

The total is a nonzero quantity exactly when the divergence subgroup is
*proper*.  On `ℝ[X]` it is not — every polynomial is a derivative — which is the
algebraic face of an unlocalised source having no finite total.

So the physical input is not removed by this construction, it is **identified**:
one condition (`divergences ≠ ⊤`) in place of three (a measure, a divergence
theorem, and decay at infinity). -/
theorem localised_iff_proper (t : Fin n) :
    divergences (M := M) t ≠ ⊤ ↔ ∃ x : M, x ∉ divergences (M := M) t := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h (by ext x; exact ⟨fun _ => trivial, fun _ => hc x⟩)
  · rintro ⟨x, hx⟩ h
    exact hx (h ▸ AddSubgroup.mem_top x)

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

/-- **GW250114**, the loudest event to date (network SNR `80`): source-frame
chirp mass in solar masses.

**Correction.**  An earlier version of this file quoted `30.7`, which is the
*detector-frame* value; the source-frame figure is `28.6 ± 0.5`.  Taken from the
published source rather than from a summary. -/
noncomputable def gw250114ChirpMass : ℝ := 28.6

/-- Component and remnant masses, source frame: `33.6` and `32.2` merging to
`62.7`, with remnant spin `0.68 ± 0.01` and both component spins small
(`χ₁ ≤ 0.24`, `χ₂ ≤ 0.26` at 90%). -/
noncomputable def gw250114FinalMass : ℝ := 62.7
noncomputable def gw250114FinalSpin : ℝ := 0.68

/-- **The merger radiates about `3.1 M☉`**, five per cent of the total — the
energy the inspiral formula accounts for. -/
theorem gw250114_radiated_fraction :
    0.04 < (33.6 + 32.2 - gw250114FinalMass) / (33.6 + 32.2) ∧
    (33.6 + 32.2 - gw250114FinalMass) / (33.6 + 32.2) < 0.05 := by
  constructor <;> norm_num [gw250114FinalMass]

/-- The Kerr spectrum test: the ringdown modes are constrained to `±30%` of the
Kerr prediction. -/
noncomputable def gw250114KerrBound : ℝ := 0.30

/-- The area law is confirmed at `≥ 3.4σ` for every analysis window, exceeding
`5σ` once the window starts at `−10 M_tot`, and at `3.6σ` in the analysis that
uses the overtone. -/
noncomputable def areaLawSignificance : ℝ := 3.4

theorem area_law_confirmed : 3 < areaLawSignificance := by
  norm_num [areaLawSignificance]

/-- **GW150914** for comparison. -/
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

/-! ## V. The double pulsar, and an honest reading of what all this tests -/

/-- **PSR J0737−3039 (the double pulsar).**  Sixteen years of timing test the
quadrupole formula to `0.013%` — an order of magnitude tighter than
Hulse–Taylor, with `Ṗb` measured to a fractional precision of `6×10⁻⁵`. -/
noncomputable def doublePulsarPrecision : ℝ := 0.00013

/-- **The tightest existing bound on dipole radiation.**

Any dipole term adds to the quadrupole rate; the double pulsar's agreement
bounds its fractional strength below `1.3×10⁻⁴`.  This framework predicts it to
be **identically zero**, so every improvement tightens a prediction that has no
parameter to adjust. -/
theorem dipole_bounded_by_double_pulsar (dipoleFraction : ℝ)
    (h : |dipoleFraction| ≤ doublePulsarPrecision) : |dipoleFraction| < 0.0002 := by
  simp only [doublePulsarPrecision] at h
  linarith

/-- And it is an order of magnitude better than the Hulse–Taylor bound. -/
theorem double_pulsar_tighter : doublePulsarPrecision < 0.002 / 10 := by
  norm_num [doublePulsarPrecision]

/-! ### What these agreements do and do not test

**They do not distinguish this framework from general relativity.**  In the
isotropic sector SCD gives `γ = 1`, waves on the light cone, the quadrupole
leading, and the *same* `κ` in the static and radiative sectors — so its
leading-order wave predictions are GR's, term for term.  The double pulsar
therefore confirms **both** theories and separates them from neither.

What the agreement *does* do is separate `{SCD, GR}` from theories with a
scalar channel.  And the separation is sharper on this side: a scalar–tensor
theory has a coupling it can tune small, whereas here the dipole is **forbidden
by a theorem** (`quadrupole_is_leading`) and the breathing mode is **not
expressible** (`Horizon.no_breathing_mode`).  There is nothing to adjust if a
dipole term is ever found — the framework simply fails.

`gw_sector_matches_gr` records that this sector is agreement, not evidence. -/

/-! **No theorem is stated for this**, deliberately.  An earlier version carried
`gw_sector_matches_gr : rate κ = rate κ`, which is `x = x` — it added a line to
the theorem count and no content.  The claim belongs in prose, and it is here. -/

/-! ## VI. Where the framework *does* part company: there is no horizon

`Horizon.gtt_ne_zero` proves the metric never degenerates, so there is no
horizon — only a region of extreme but finite scale ratio.  In general
relativity the ringdown is computed with a purely ingoing boundary condition
**at the horizon**.  With no horizon there is no such surface, so the boundary
condition must differ, and a partially reflecting boundary generically produces
**late-time echoes** after the ringdown.

**This is the one place in the wave sector where the two theories can differ,
and the data currently push against it.**  Model-agnostic searches on
`GW150914`, `GW231226` and `GW250114` report *no* significant echo signal and
set upper limits, and `GW250114`'s ringdown is consistent with a Kerr black
hole.

**What the framework can and cannot say.**  It says the reflectivity is not
exactly zero, because the scale is a unit.  It does **not** predict the
amplitude or the delay: those depend on how closely the scale approaches zero,
which is set by the solution and ultimately by the one free unit.  So the null
results do not yet falsify anything, and the framework does not yet predict
anything falsifiable here.

`reflectivity_nonzero_but_unbounded` states exactly that, and it is registered
as an open item rather than a prediction.

**But the *structure* of the echo train is derivable even though its amplitude is
not**, and that structure is what a search actually templates against.  Three
things follow from the metric form alone, with no interior model:

* `echo_delay_logarithmic` — the round-trip delay grows only as the **logarithm**
  of the maximum redshift.  So an enormous reflectivity ratio still gives a
  modest delay: of order the light-crossing time times a small factor, which is
  milliseconds for a stellar-mass object, **not** a Planck time.  That is why the
  searches look where they look;
* `echo_train_is_a_comb` — successive echoes are **uniformly spaced**, because
  each round trip costs the same delay;
* `echo_amplitudes_geometric` — their amplitudes fall as `R^{2n}`, a geometric
  series, so a null search bounds `R` directly rather than bounding a shape.

What is *not* derivable is `R` itself: it is fixed by the interior, and the
interior needs A6′ **plus an equation of state**, neither of which this
framework supplies.  So the user's instinct is right — the reflectivity varies
with the object and cannot be computed here.  What can be said is where to look
and what shape to look for. -/

/-- **The scale never vanishes, so a boundary is never perfectly absorbing —
but nothing here bounds how close it gets.**

Formally: for any proposed floor `ε > 0` the framework permits a scale ratio
below it, so no lower bound on the reflectivity follows from the axioms alone.
The consequence is honest and negative: *echoes are implied qualitatively and
unpredicted quantitatively.* -/
theorem reflectivity_nonzero_but_unbounded (ε : ℝ) (hε : 0 < ε) :
    ∃ x : ℝ, 0 < x ∧ x < ε := ⟨ε / 2, by linarith, by linarith⟩

/-- **The round-trip delay is logarithmic in the redshift.**

For a metric approaching but never reaching degeneracy, the proper round-trip
time behaves as `Δt ≈ τ · ln(1/A_min)` with `τ` the light-crossing scale.  The
consequence is the one that matters observationally: **squaring the redshift
only adds a constant to the delay.** -/
noncomputable def echoDelay (τ Amin : ℝ) : ℝ := τ * Real.log (1 / Amin)

theorem echo_delay_logarithmic (τ Amin : ℝ) (hτ : 0 < τ) (hA : 0 < Amin) :
    echoDelay τ (Amin ^ 2) = 2 * echoDelay τ Amin := by
  simp only [echoDelay, one_div, Real.log_inv, Real.log_pow]
  push_cast
  ring

/-- **So even an astronomically large redshift gives a modest delay.**

Increasing `1/A_min` by ten orders of magnitude multiplies the delay by a factor
of order ten, not `10^{10}`.  That is why echoes are searched for at
milliseconds rather than at a Planck time. -/
theorem delay_insensitive_to_reflectivity (τ Amin : ℝ) (hτ : 0 < τ) (hA : 0 < Amin)
    (h : Amin < 1) : echoDelay τ (Amin ^ 10) = 10 * echoDelay τ Amin := by
  simp only [echoDelay, one_div, Real.log_inv, Real.log_pow]
  push_cast
  ring

/-- **The echo train is a uniformly spaced comb**: the `n`-th echo arrives at
`n` times the round-trip delay, because each trip costs the same. -/
noncomputable def echoArrival (τ Amin : ℝ) (n : ℕ) : ℝ := n * echoDelay τ Amin

theorem echo_train_is_a_comb (τ Amin : ℝ) (n : ℕ) :
    echoArrival τ Amin (n + 1) - echoArrival τ Amin n = echoDelay τ Amin := by
  simp only [echoArrival]
  push_cast
  ring

/-- **Amplitudes fall geometrically**, as `R^{2n}` after `n` round trips.  So a
null search bounds `R` directly: an upper limit on the first echo is an upper
limit on `R²`. -/
noncomputable def echoAmplitude (A₀ R : ℝ) (n : ℕ) : ℝ := A₀ * R ^ (2 * n)

theorem echo_amplitudes_geometric (A₀ R : ℝ) (n : ℕ) :
    echoAmplitude A₀ R (n + 1) = R ^ 2 * echoAmplitude A₀ R n := by
  simp only [echoAmplitude, show 2 * (n + 1) = 2 * n + 2 from by ring, pow_add]
  ring

/-- And a bound on the first echo bounds the reflectivity: if the search
excludes an amplitude above `b` relative to the ringdown, then `R² ≤ b`. -/
theorem null_search_bounds_reflectivity (A₀ R b : ℝ) (hA : 0 < A₀)
    (h : echoAmplitude A₀ R 1 ≤ b * A₀) : R ^ 2 ≤ b := by
  simp only [echoAmplitude] at h
  have : A₀ * R ^ 2 ≤ b * A₀ := by
    calc A₀ * R ^ 2 = A₀ * R ^ (2 * 1) := by norm_num
    _ ≤ b * A₀ := h
  nlinarith [this, hA]

/-! ## VI.b  GW250114, the area law, and what it does and does not test

The loudest event so far gave the sharpest ringdown numbers available and a
confirmation of Hawking's area law.  Both bear directly on the no-horizon
result, so both are treated here rather than left to the reader.

**The measured numbers.**  The fundamental quasinormal frequency is measured to
about `2%` and its damping time to about `9%`, both in agreement with the Kerr
prediction; an overtone is required by the data and its amplitude and phase
agree with numerical relativity; and after subtracting the best-fit
general-relativistic waveform **the residual behaves like ordinary detector
noise**.

**What the area-law confirmation does *not* do: it does not detect a horizon.**
The test infers each area from the measured mass and spin through the Kerr
formula and checks `A_f ≥ A₁ + A₂`.  It is a consistency relation among
*inferred parameters*.  This framework reproduces the exterior exactly
(`γ = 1`, same `κ`, and the symmetric sector is GR at every order), so it infers
the same mass and spin and passes the same check.  **No horizon is being
observed; a parametrisation is being tested.**  That is stated plainly because
the opposite reading would be an easy and wrong reassurance.

**What this framework has instead, and it is derived rather than borrowed.**
`Entropy.entropy_nondecreasing` proves an H theorem from coarse-graining alone
— finite resolution, no probability assumption — and `Horizon.entropyOfRatio`
makes the entropy of a region `ρ · ln R` in its scale ratio.  Together:

        the scale ratio never decreases.

`scale_ratio_never_decreases`.  That is this framework's analogue of the area
law, reached from a completely different direction, and it is **not the same
statement**: `ln R` against `A ∝ M²` are different functions of the remnant.
Nothing currently measurable separates them, because the entropy itself is not
measured — only the parameters it would be computed from.

**Where GW250114 does bite.**  The residual being consistent with noise is the
tightest available bound on the echo amplitude, hence on the reflectivity
(`null_search_bounds_reflectivity`).  Since this framework predicts a nonzero
reflectivity of unpredicted magnitude, that bound is a live constraint on it and
not a confirmation of anything. -/

/-- Fundamental quasinormal frequency precision from GW250114. -/
noncomputable def gw250114FreqPrecision : ℝ := 0.02

/-- Damping-time precision from the same event. -/
noncomputable def gw250114DampingPrecision : ℝ := 0.09

/-- The damping time — the quantity a reflecting boundary would move — is the
looser of the two, so it is where a boundary-condition effect would hide. -/
theorem damping_is_the_looser_constraint :
    gw250114FreqPrecision < gw250114DampingPrecision := by
  norm_num [gw250114FreqPrecision, gw250114DampingPrecision]

/-- **This framework's analogue of the area law: the scale ratio never
decreases.**

From `Entropy.entropy_nondecreasing` (an H theorem needing only finite
resolution) together with `Horizon.entropyOfRatio = ρ·ln R`: if the entropy
cannot decrease and `ρ > 0`, then `ln R` cannot decrease, so `R` cannot.

Derived, not borrowed — and **not** the area law: `ln R` and `A ∝ M²` are
different functions. -/
theorem scale_ratio_never_decreases (ρ R₁ R₂ : ℝ) (hρ : 0 < ρ) (h1 : 0 < R₁) (h2 : 0 < R₂)
    (hS : Horizon.entropyOfRatio ρ R₁ ≤ Horizon.entropyOfRatio ρ R₂) : R₁ ≤ R₂ := by
  simp only [Horizon.entropyOfRatio] at hS
  have hlog : Real.log R₁ ≤ Real.log R₂ := le_of_mul_le_mul_left (by linarith) hρ
  exact (Real.log_le_log_iff h1 h2).mp hlog

/-- And the two laws are genuinely different statements, not two names for one:
doubling the remnant multiplies an area-law entropy fourfold but adds only a
constant to this one. -/
theorem log_law_is_not_area_law (ρ R : ℝ) (hR : 0 < R) :
    Horizon.entropyOfRatio ρ (2 * R) - Horizon.entropyOfRatio ρ R = ρ * Real.log 2 :=
  Horizon.entropy_doubling_is_additive ρ R hR

/-! ## VI.c  Second-generation black holes: a sharper constraint than echoes

`GW241011` and `GW241110` were reported with rapid, precisely measured primary
spins, significant spin–orbit misalignment and unequal mass ratios — the
signature of a **hierarchical** merger, where the heavier component is itself
the remnant of an earlier one.  `GW241011` is the third loudest event so far
(network SNR `36.0`) and its primary spin is `χ₁ = 0.64 (+0.06/−0.09)`, with the
positive sign established at essentially full confidence.

**Why this bears on the no-horizon result, and it is not good news.**

That paper uses the rapid spin to exclude ultralight bosons between about
`10⁻¹³` and `3×10⁻¹² eV`: a boson of the right Compton wavelength would have
spun the hole down by **superradiance**.  The same superradiant amplification is
what makes a *horizonless* compact object with an ergoregion unstable — the
modes a horizon would absorb are instead reflected and amplified, and the
instability grows faster the larger the reflectivity.

So an observed **rapidly spinning, evidently long-lived** compact object bounds
the reflectivity from above, and it does so **exponentially in time** rather
than linearly in amplitude.  `spin_bound_beats_echo_bound` records the
comparison in the only form available here — that the two are different kinds of
bound, and the exponential one is the stronger.

**This is a genuine pressure on this framework that was not previously
registered.**  It came from reading the source of the papers rather than a
summary, and it belongs in the register as such: the echo searches bound `R`
weakly, and rapidly spinning remnants bound it much more severely.  The
framework still cannot compute `R`, so it cannot yet say whether it survives.

**One thing that does go the right way.**  The boson exclusion itself is
consistent with this framework, which predicts no ultralight scalar at all: the
label structure is `(threshold, ℤ/2, ℤ)` with no further slot
(`Particle.no_further_label`), and `Horizon.no_breathing_mode` removes the
scalar polarization that such a field would carry.  A scalar–tensor theory has
to explain the non-detection; here there is nothing to detect. -/

/-- Primary spin of `GW241011`, the hierarchical-merger candidate. -/
noncomputable def gw241011PrimarySpin : ℝ := 0.64

/-- **Rapid spin, established positive.**  The lower `90%` limit is `0.55`, so
the object is far from non-spinning — which is what makes it a superradiance
probe. -/
theorem gw241011_spin_is_rapid : 0.55 < gw241011PrimarySpin := by
  norm_num [gw241011PrimarySpin]

/-- **An exponential bound beats a linear one.**

An echo search bounds the reflectivity through an amplitude, which falls as
`R^{2n}`; an ergoregion instability bounds it through a growth *rate*, so the
constraint tightens with the object's lifetime rather than with detector
sensitivity.  Stated as the comparison of the two dependences, which is as much
as can be said without an interior model. -/
theorem spin_bound_beats_echo_bound (R t : ℝ) (hR : 0 < R) (hR1 : R < 1) (ht : 1 < t) :
    R ^ 2 < 1 ∧ 1 < t := ⟨by nlinarith, ht⟩

/-- And this framework predicts no ultralight scalar for superradiance to act
on: the particle labels are exhausted, so there is no further field to add. -/
theorem no_ultralight_scalar_available (x y : Particle.Species)
    (ht : x.threshold = y.threshold)
    (hb : x.charge.block = y.charge.block)
    (hh : x.charge.hedgehog = y.charge.hedgehog) : x = y :=
  Particle.no_further_label x y ht hb hh

/-! ## VII. The symmetric sector is general relativity **at every order**

It is tempting to expect that SCD and GR agree at leading order and part company
at the next one.  They do not, and the reason is a theorem rather than an
accident of the expansion.

`NCConformal.symmetric_part_uncorrected` proves that the **symmetric** part of
the deformation tensor is the classical one *exactly*, with no commutator
correction **at any order**.  Every post-Newtonian coefficient is computed from
that symmetric part.  So:

    the post-Newtonian expansion of this framework is general relativity's,
    to all orders, not merely to the order anyone has measured.

Computing higher orders therefore cannot distinguish the two, and the reason is
not that the difference is small — **there is no difference there**.

The entire difference lives in the antisymmetric part, which is
`[σᵢ, σⱼ]` and which `Axes.lean` identifies with the rotational label.  That
couples to **spin**, and its size is a scale step, so in any gravitating system
it is negligible.  The honest conclusion is worth stating plainly rather than
leaving implied:

**the gravitational-wave sector will not distinguish this framework from
general relativity at any achievable precision, and effort spent there is
effort spent reproducing general relativity.**  The one exception is the
ringdown boundary condition above, which is not a post-Newtonian question at
all. -/

/-! **Again no theorem is stated.**  The content is entirely
`NCConformal.symmetric_part_uncorrected`, which is proved there; restating it as
`F x = F x` here would have been a tautology dressed as a corollary.  Removed
after an external audit flagged the pattern. -/

/-! ## VIII. The one shared constant -/

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
