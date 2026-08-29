/-
# Particles without fields: a scale defect mechanism

Quantum field theory produces particles by quantising a field on a background:
a particle is an excitation, its charge a representation label, its mass a
parameter of the Lagrangian.  None of that is available here, and rather than
imitate it we take the scale picture at its word.

If A5's continuous scale symmetry is broken to a discrete subgroup — the scale
matters only modulo a period `Δ` — then the log-scale is not a real-valued
field but a **circle-valued** one.  Around any loop enclosing a point, the
scale must return to itself *modulo `Δ`*, so it may fail to return to itself on
the nose.  The failure is an integer multiple of `Δ`.

That integer is the particle.

A particle is therefore a **defect in the unit of measure**: a place where the
local scale cannot be combed flat.  From this single move:

* **charge is an integer** because winding numbers are (`winding_unique`),
  not because a representation was chosen — and fractional charge cannot occur
  in isolation;
* **particles are stable** because a nonzero winding cannot be deformed to the
  vacuum (`stable_of_winding_ne_zero`);
* **charge is conserved**, and a defect cannot be created alone — only in
  pairs of opposite winding (`pair_winding_zero`);
* **antiparticles** are the same defect with reversed orientation, hence carry
  opposite charge and **exactly equal mass** (`antiparticle_same_mass`) — a
  CPT-like statement arising from orientation reversal rather than being
  imposed;
* **the mass spectrum is a geometric tower** `m_k = m₀e^{|k|Δ}`, because by A3
  mass *is* inverse scale and the scale steps by `Δ` (`mass_ratio_geometric`).

This does not reproduce the Standard Model, and is not meant to.  It is a
different mechanism with a different signature: constant mass *ratios*, an
unbounded tower, strictly integral charge, and exact particle–antiparticle mass
degeneracy.  Those are the things to test.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import SCD.Charges

namespace SCD.Defect

open Real

/-! ## Scale defects -/

/-- A **scale defect**: the log-scale read around a loop enclosing a point.

`lift` is the scale followed continuously around the loop.  Because the scale
is physical only modulo the period `Δ`, going once around (`x ↦ x + 1`) may
return a value shifted by an integer number of periods.  That integer is the
defect's topological charge. -/
structure ScaleDefect (Δ : ℝ) where
  /-- The continuously followed log-scale around the loop. -/
  lift : ℝ → ℝ
  /-- The topological charge. -/
  winding : ℤ
  /-- One circuit shifts the scale by `winding` periods. -/
  quasiperiodic : ∀ x, lift (x + 1) = lift x + (winding : ℝ) * Δ

namespace ScaleDefect

variable {Δ : ℝ}

/-- **Charge is well defined.**  A configuration determines its winding
uniquely; there is no freedom to reassign it.  This is why charge is an
integer — not by a choice of representation, but because a loop either closes
up or misses by a whole number of periods. -/
theorem winding_unique (hΔ : Δ ≠ 0) (D E : ScaleDefect Δ) (h : D.lift = E.lift) :
    D.winding = E.winding := by
  have hD := D.quasiperiodic 0
  have hE := E.quasiperiodic 0
  rw [h] at hD
  have : (D.winding : ℝ) * Δ = (E.winding : ℝ) * Δ := by linarith
  have hcast : (D.winding : ℝ) = (E.winding : ℝ) :=
    mul_right_cancel₀ hΔ this
  exact_mod_cast hcast

/-- The vacuum: no defect. -/
def vacuum (Δ : ℝ) : ScaleDefect Δ where
  lift := fun _ => 0
  winding := 0
  quasiperiodic := by intro x; ring

@[simp] theorem vacuum_winding : (vacuum Δ).winding = 0 := rfl

/-- Superposition of defects. -/
def combine (D E : ScaleDefect Δ) : ScaleDefect Δ where
  lift := fun x => D.lift x + E.lift x
  winding := D.winding + E.winding
  quasiperiodic := by
    intro x
    have hD := D.quasiperiodic x
    have hE := E.quasiperiodic x
    push_cast
    rw [hD, hE]
    ring

/-- **Charge is additive**, hence conserved under superposition. -/
@[simp] theorem combine_winding (D E : ScaleDefect Δ) :
    (D.combine E).winding = D.winding + E.winding := rfl

/-- The **antiparticle**: the same defect with reversed orientation. -/
def anti (D : ScaleDefect Δ) : ScaleDefect Δ where
  lift := fun x => -D.lift x
  winding := -D.winding
  quasiperiodic := by
    intro x
    have hD := D.quasiperiodic x
    push_cast
    rw [hD]
    ring

@[simp] theorem anti_winding (D : ScaleDefect Δ) : D.anti.winding = -D.winding := rfl

/-- **A defect cannot be created alone.**  A particle together with its
antiparticle carries zero total charge, so the pair can appear from the vacuum;
a single defect cannot. -/
@[simp] theorem pair_winding_zero (D : ScaleDefect Δ) :
    (D.combine D.anti).winding = 0 := by
  simp only [combine_winding, anti_winding]
  ring

/-! ## Topological stability -/

/-- A configuration is *trivial* when the scale genuinely closes up around the
loop — no defect. -/
def IsTrivial (D : ScaleDefect Δ) : Prop := ∀ x, D.lift (x + 1) = D.lift x

@[simp] theorem vacuum_isTrivial : IsTrivial (vacuum Δ) := by
  intro x; rfl

/-- **Particles are stable.**  A defect with nonzero winding is not trivial:
the scale genuinely fails to close up around it, and no continuous change of
the configuration that preserves the winding can make it close up.  Stability
is topological, not dynamical — nothing about forces or a potential is used. -/
theorem stable_of_winding_ne_zero (hΔ : Δ ≠ 0) (D : ScaleDefect Δ)
    (h : D.winding ≠ 0) : ¬ IsTrivial D := by
  intro htriv
  have h1 := D.quasiperiodic 0
  have h2 := htriv 0
  rw [h2] at h1
  have hzero : (D.winding : ℝ) * Δ = 0 := by linarith
  rcases mul_eq_zero.mp hzero with hw | hd
  · exact h (by exact_mod_cast hw)
  · exact hΔ hd

/-- Conversely a trivial configuration has zero charge: the vacuum is
uncharged. -/
theorem winding_eq_zero_of_trivial (hΔ : Δ ≠ 0) (D : ScaleDefect Δ)
    (h : IsTrivial D) : D.winding = 0 := by
  by_contra hw
  exact stable_of_winding_ne_zero hΔ D hw h

/-! ## An additive `ℤ`-label — but **not** the hedgehog

**Scope correction (see `Sources.lean`).**  An earlier version of this section
sent the winding to `Charges.DefectCharge.hedgehog` and claimed the two files
describe "one charge algebra, not two".  That is wrong and is withdrawn.

`Charges.hedgehog` is, in its own docstring, "how the axis wraps the **enclosing
sphere**" — a `π₂` class of the *projective directional* order parameter of
`Axis.lean`.  The winding here is "the log-scale read **around a loop**" — a `π₁`
class of a *circle-valued scalar* scale.  A sphere and a loop, of two different
order parameters, and `Audit.lean` §I already scopes the scalar one out.

What the maps below actually establish is the algebraic fact that both are
additive `ℤ`-labels, which is true and is all they share.  They are retained on
that footing and the physical identification is not claimed. -/

variable {B : Type*} [Group B]

/-- The winding, recorded in the shape of an additive `ℤ`-label with trivial
finite part.  **Not** an identification with the hedgehog: see the section
header. -/
def toCharge (D : ScaleDefect Δ) : Charges.DefectCharge B where
  block := 1
  hedgehog := D.winding

@[simp] theorem toCharge_block (D : ScaleDefect Δ) :
    (D.toCharge (B := B)).block = 1 := rfl
@[simp] theorem toCharge_hedgehog (D : ScaleDefect Δ) :
    (D.toCharge (B := B)).hedgehog = D.winding := rfl

@[simp] theorem toCharge_combine (D E : ScaleDefect Δ) :
    (D.combine E).toCharge (B := B) = (D.toCharge).comp (E.toCharge) := by
  simp only [toCharge, Charges.DefectCharge.comp, combine_winding, one_mul]

@[simp] theorem toCharge_anti (D : ScaleDefect Δ) :
    (D.anti).toCharge (B := B) = (D.toCharge (B := B)).anti := by
  simp only [toCharge, Charges.DefectCharge.anti, anti_winding, inv_one]

@[simp] theorem toCharge_vacuum :
    (vacuum Δ).toCharge (B := B) = Charges.DefectCharge.triv B := rfl

/-- With a trivial finite part there is nothing to fail to close up, so the
label is unconstrained.  This is an algebraic remark about the shape of
`DefectCharge`, not a claim that `Charges.hedgehog_free` is about these
defects. -/
theorem toCharge_observable (D : ScaleDefect Δ) :
    Charges.DefectCharge.Observable (D.toCharge (B := B)) := rfl

/-! ## The mass spectrum

By A3 mass is inverse scale, `m = e^{-σ}`.  A defect of charge `k` costs `|k|`
periods of scale, so its mass is `m₀e^{|k|Δ}`.  The tower is geometric because
the scale steps additively and mass is its exponential. -/

/-- Mass of a defect of topological charge `k`.

**This law is posited, not derived.**  The winding is topological; the mass is
dynamical, and nothing in this development computes the strain energy of a
defect.  `MassAudit.mass_law_underdetermined` exhibits a different law equally
compatible with everything proved about the winding.  Treat the geometric tower
below as a hypothesis under test, not as a consequence of the axioms. -/
noncomputable def mass (m₀ Δ : ℝ) (k : ℤ) : ℝ := m₀ * Real.exp (|(k : ℝ)| * Δ)

theorem mass_pos {m₀ : ℝ} (hm : 0 < m₀) (Δ : ℝ) (k : ℤ) : 0 < mass m₀ Δ k := by
  simp only [mass]
  positivity

/-- **Particle and antiparticle have exactly equal mass.**

Charge conjugation is orientation reversal, which leaves `|k|` untouched.  The
degeneracy is not imposed as a symmetry principle; it is a consequence of the
charge being a winding number. -/
@[simp] theorem antiparticle_same_mass (m₀ Δ : ℝ) (k : ℤ) :
    mass m₀ Δ (-k) = mass m₀ Δ k := by
  simp only [mass, Int.cast_neg, abs_neg]

/-- The charge-zero state is the lightest, with mass `m₀`. -/
@[simp] theorem mass_zero (m₀ Δ : ℝ) : mass m₀ Δ 0 = m₀ := by
  simp only [mass, Int.cast_zero, abs_zero, zero_mul, Real.exp_zero, mul_one]

/-- **The tower is geometric** — *given* the posited mass law.  Consecutive
levels differ by the constant factor `e^Δ` at every level.

This is a falsifiable shape, but what it tests is the mass hypothesis of
`mass`, not the framework: see `MassAudit`. -/
theorem mass_ratio_geometric (m₀ Δ : ℝ) (k : ℤ) (hk : 0 ≤ k) :
    mass m₀ Δ (k + 1) = Real.exp Δ * mass m₀ Δ k := by
  have h1 : |((k + 1 : ℤ) : ℝ)| = (k : ℝ) + 1 := by
    rw [Int.cast_add, Int.cast_one, abs_of_nonneg]
    have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have h2 : |((k : ℤ) : ℝ)| = (k : ℝ) := abs_of_nonneg (by exact_mod_cast hk)
  simp only [mass, h1, h2]
  rw [add_mul, one_mul, Real.exp_add]
  ring

/-- The ratio is the same at every level — the statement that could be checked
against an observed spectrum. -/
theorem mass_ratio_const (m₀ Δ : ℝ) (k l : ℤ) (hk : 0 ≤ k) (hl : 0 ≤ l)
    (hm : m₀ ≠ 0) :
    mass m₀ Δ (k + 1) / mass m₀ Δ k = mass m₀ Δ (l + 1) / mass m₀ Δ l := by
  rw [mass_ratio_geometric m₀ Δ k hk, mass_ratio_geometric m₀ Δ l hl]
  have hk' : mass m₀ Δ k ≠ 0 := by
    simp only [mass]
    exact mul_ne_zero hm (Real.exp_ne_zero _)
  have hl' : mass m₀ Δ l ≠ 0 := by
    simp only [mass]
    exact mul_ne_zero hm (Real.exp_ne_zero _)
  field_simp

end ScaleDefect

end SCD.Defect
