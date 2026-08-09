/-
# Dark matter: interaction without observation

The framework forbids the usual question "what particle is it?" and replaces
it with a question about *scales*.

A detector is itself a physical system sitting at some energy scale `ε_D`.  By
A3 that is the reciprocal of its spatial resolution: a detector built to
resolve small distances is a high-energy object.  What it can register is not
"an interaction" but "an interaction that moves its own state by at least its
threshold `θ`".

An excitation whose own energy scale `ε` is far below `ε_D` therefore deposits
a *strictly positive* but arbitrarily small fraction of the detector's scale.
The interaction happens.  The observation fails.

Meanwhile gravity couples to the total energy `N·ε`, which is blind to how
that energy is partitioned.  A large multiplicity of very-low-scale
excitations is therefore gravitationally loud and non-gravitationally silent —
which is the entire observational profile of dark matter.

The two theorems below make this exact.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

namespace ScaleUniverse.Dark

/-! ## Response functions -/

/-- The fraction of a detector's own energy scale that a single excitation of
energy scale `ε` can move.  This is what a detector actually measures. -/
noncomputable def detResp (ε εD : ℝ) : ℝ := ε / εD

/-- The gravitational response: total energy, blind to how it is partitioned
among excitations.  `N` is the multiplicity. -/
noncomputable def gravResp (N ε : ℝ) : ℝ := N * ε

theorem detResp_pos {ε εD : ℝ} (hε : 0 < ε) (hD : 0 < εD) : 0 < detResp ε εD := by
  simp only [detResp]
  positivity

/-! ## Observational decoupling -/

/-- **Interaction without observation.**

For any detector scale `εD` and any threshold `θ`, every sufficiently
low-scale excitation interacts (`detResp > 0`) yet falls below threshold
(`detResp < θ`).

The failure is in the *measurement*, not in the coupling.  Nothing has been
switched off; the probe and the apparatus simply live at incommensurable
scales. -/
theorem detection_failure (εD θ : ℝ) (hD : 0 < εD) (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      0 < detResp ε εD ∧ detResp ε εD < θ := by
  refine ⟨εD * θ, by positivity, fun ε hε hlt => ⟨detResp_pos hε hD, ?_⟩⟩
  simp only [detResp, div_lt_iff₀ hD]
  linarith [hlt]

/-- **Dark matter.**

Fix any gravitational signal `M > 0`, any detector scale `εD > 0`, and any
detection threshold `θ > 0`.  Then there is a scale `ε` and a multiplicity `N`
producing *exactly* the gravitational signal `M` while remaining strictly
below the detection threshold.

Gravitational visibility and non-gravitational invisibility are therefore not
in tension: they are two different functionals of the same configuration, and
the scale hierarchy separates them by an arbitrary factor. -/
theorem dark_matter_exists (M εD θ : ℝ) (hM : 0 < M) (hD : 0 < εD) (hθ : 0 < θ) :
    ∃ ε N : ℝ, 0 < ε ∧ 0 < N ∧ gravResp N ε = M
      ∧ 0 < detResp ε εD ∧ detResp ε εD < θ := by
  obtain ⟨ε₀, hε₀, hmain⟩ := detection_failure εD θ hD hθ
  have hc : 0 < min (ε₀ / 2) M := lt_min (by linarith) hM
  have hclt : min (ε₀ / 2) M < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨min (ε₀ / 2) M, M / min (ε₀ / 2) M, hc, div_pos hM hc, ?_,
    (hmain _ hc hclt).1, (hmain _ hc hclt).2⟩
  simp only [gravResp]
  field_simp

/-- The same statement in the limit form usually quoted: the detectable
response of a fixed gravitational mass tends to zero as the constituent scale
is lowered. -/
theorem response_vanishes (εD θ : ℝ) (hD : 0 < εD) (hθ : 0 < θ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → detResp ε εD < θ :=
  let ⟨ε₀, h₀, h⟩ := detection_failure εD θ hD hθ
  ⟨ε₀, h₀, fun ε hε hlt => (h ε hε hlt).2⟩

end ScaleUniverse.Dark
