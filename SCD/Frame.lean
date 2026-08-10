/-
# A4 was too strong: the scale must be directional

The original A4 read `g = e^{2σ}δ`: one scalar scale, the same in every
direction.  That axiom is *provably* unable to carry Schwarzschild, and this
file proves it.

The diagnosis is physical, not technical.  The programme says that the local
energy-momentum sets the local scale.  But energy-momentum is a **tensor**: a
flowing fluid carries different energy density along its flow than across it.
A tensor source cannot set a scalar scale.  The scale must be **directional**.

So A4 is weakened to

  **A4′ (directional scale).**  The local unit of measure is one scale `sₐ` per
  direction, each a unit of the ring.  The measured line element is
  `g_{ab} = η_a s_a² δ_{ab}` in that frame.

Isotropy — all `sₐ` equal — is the old A4, recovered as a special case, so
nothing proved earlier is lost.  What is gained is exactly what was missing:

* `isotropic_reciprocal_forces_flat` — under the *old* axiom, the defining
  relation of Schwarzschild `g_tt·g_rr = −1` forces the metric to be flat.
  The old axiom did not merely fail to produce Schwarzschild; it forbade it.
* `exists_reciprocal_nonisotropic` — under A4′ the same relation has genuine
  non-flat solutions.

The physical content of the Schwarzschild relation, read in scale language, is
striking on its own: `s_t · s_r = 1`.  **The temporal and radial scales are
exact reciprocals** — clocks are compressed by precisely the factor by which
radial rulers are stretched.  That is a statement about scale, not about a
metric function, and the scalar theory could not even express it.
-/
import SCD.Axioms

namespace SCD.Frame

open SCD ScaleAlgebra

variable {n : ℕ} {A : Type*} [CommRing A]

/-- **A4′ — the directional scale.**  One local unit per direction, each
invertible (a unit of measure is something one can divide by). -/
structure DirScale (n : ℕ) (A : Type*) [CommRing A] where
  /-- The local scale in direction `a`. -/
  s : Fin n → Aˣ

namespace DirScale

variable (E : DirScale n A) (η : Fin n → A)

/-- The measured metric component in direction `a`, with signature `η`. -/
def metric (a : Fin n) : A := η a * ((E.s a : A)) ^ 2

/-- **Isotropy is the old axiom A4.**  All directions carry the same scale. -/
def Isotropic : Prop := ∀ a b : Fin n, E.s a = E.s b

/-- Under isotropy the metric is the bare one times a single conformal factor —
exactly `g = e^{2σ}δ`.  Everything proved in the conformal sector therefore
survives as the isotropic special case of A4′. -/
theorem isotropic_metric (h : E.Isotropic) (a b : Fin n) :
    E.metric η a * η b = E.metric η b * η a := by
  simp only [metric, h a b]
  ring

/-! ## The Schwarzschild relation -/

/-- **The reciprocal-scale relation** `s_t · s_r = 1`.

Equivalent to `g_tt·g_rr = −1` for signature `(−,+)`, this is the defining
feature of the Schwarzschild and Reissner–Nordström families.  In scale
language: the temporal and radial units are exact reciprocals. -/
def Reciprocal (t r : Fin n) : Prop := E.s t * E.s r = 1

/-- The relation written on the metric components, for signature `η_t = −1`,
`η_r = 1`: `g_tt · g_rr = −1`. -/
theorem reciprocal_metric (t r : Fin n) (h : E.Reciprocal t r)
    (ht : η t = -1) (hr : η r = 1) :
    E.metric η t * E.metric η r = -1 := by
  simp only [metric, ht, hr]
  have hs : ((E.s t : A)) * ((E.s r : A)) = 1 := by
    have := congrArg (Units.val (α := A)) h
    simpa using this
  calc (-1 : A) * (E.s t : A) ^ 2 * (1 * (E.s r : A) ^ 2)
      = -(((E.s t : A) * (E.s r : A)) ^ 2) := by ring
    _ = -1 := by rw [hs]; ring

/-! ## The old axiom forbade Schwarzschild

This is the sharp statement of the diagnosis. -/

/-- **Under the old, isotropic axiom the Schwarzschild relation collapses to
flat space.**

If all directions share one scale *and* the temporal and radial scales are
reciprocal, then that scale squares to `1`: the conformal factor is trivial and
the geometry is the bare Euclidean bookkeeping.

So `g = e^{2σ}δ` did not merely fail to reproduce Schwarzschild — it *excluded*
it.  The axiom was too strong, precisely as diagnosed. -/
theorem isotropic_reciprocal_forces_flat (t r : Fin n)
    (hiso : E.Isotropic) (hrec : E.Reciprocal t r) :
    ((E.s t : A)) ^ 2 = 1 := by
  have hsame : E.s r = E.s t := hiso r t
  simp only [DirScale.Reciprocal, hsame] at hrec
  have hval := congrArg (Units.val (α := A)) hrec
  simpa [pow_two] using hval

/-- Consequently every metric component is the bare one: the geometry is flat. -/
theorem isotropic_reciprocal_metric_bare (t r : Fin n)
    (hiso : E.Isotropic) (hrec : E.Reciprocal t r) (a : Fin n) :
    E.metric η a = η a := by
  have h1 : ((E.s t : A)) ^ 2 = 1 := E.isotropic_reciprocal_forces_flat t r hiso hrec
  have h2 : E.s a = E.s t := hiso a t
  simp only [metric, h2, h1, mul_one]

end DirScale

/-! ## Directional scale admits it

The same relation, freed of isotropy, has genuine solutions. -/

/-- **Under A4′ the Schwarzschild relation is satisfiable non-trivially.**

For any unit `u` there is a directional scale field with `s_t = u`,
`s_r = u⁻¹`, reciprocal by construction, and isotropic only in the degenerate
case `u² = 1`.  The temporal and radial scales genuinely differ, which is what
Schwarzschild requires and what the scalar axiom could not provide. -/
theorem exists_reciprocal_nonisotropic (t r : Fin n) (hne : t ≠ r)
    (u : Aˣ) (hu : (u : A) * (u : A) ≠ 1) :
    ∃ E : DirScale n A, E.Reciprocal t r ∧ ¬ E.Isotropic := by
  classical
  refine ⟨⟨fun a => if a = t then u else if a = r then u⁻¹ else 1⟩, ?_, ?_⟩
  · show (if t = t then u else if t = r then u⁻¹ else 1)
        * (if r = t then u else if r = r then u⁻¹ else 1) = 1
    rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl, mul_inv_cancel]
  · intro hiso
    have h1 : (if t = t then u else if t = r then u⁻¹ else 1)
        = (if r = t then u else if r = r then u⁻¹ else 1) := hiso t r
    rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl] at h1
    have h2 : u * u = 1 := by nth_rewrite 1 [h1]; exact inv_mul_cancel u
    exact hu (by simpa using congrArg (Units.val (α := A)) h2)

end SCD.Frame
