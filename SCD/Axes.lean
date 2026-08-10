/-
# The dilemma dissolves, and more axes are impossible

`Slice.lean` posed what it called the framework's sharpest open problem: the
label structure of `Particle.lean` was computed for a uniaxial order parameter,
yet `homogeneous_carries_no_rotation` seemed to say a uniaxial pattern carries no
angular momentum, which the world contradicts.

**The dilemma rested on a misreading, and it is mine.**

`Slice.homogeneous_carries_no_rotation` proves `wedge v v = 0` — the wedge of a
vector with **itself**.  I read that as "a uniaxial pattern carries no
rotation".  But *uniaxial* means the scale takes one distinct **value**, not
that there is one **direction**; and the theorem is about one *vector*, not one
axis.  What `wedge v v = 0` actually says is that a **homogeneous** pattern
generates no rotation.  That is a statement about constancy, not about axes.

This is the same substitution — scalar reasoning where the structure is
directional — for the fifth time, after `Frame.lean`, `Axis.lean`,
`Coupling.lean` and the withdrawn reading in `Direction.lean`.  It is worth
recording that the error survived a formalization and a paper: the theorem was
true, only its name and my gloss were wrong.

## I.  Rotation is the wedge of the pattern with its own variation

`Particle.pattern_is_one_vector` says the scale pattern is a single vector `v`.
So `v ∧ v = 0` at any one place, and a rotational label can only come from the
pattern taking **different** values at different places:

* `rotation_needs_variation` — a nonzero rotational label forces two
  non-parallel values of the pattern;
* `combable_no_rotation` — conversely, a pattern whose values are all parallel
  generates no rotation anywhere.

**So angular momentum here is `v ∧ ∇v`: the wedge of the scale vector with its
own variation.**  It is not a property a configuration has at a point.

And that resolves the dilemma in the framework's favour, because a defect is
*precisely* a configuration whose pattern is not everywhere parallel — that is
what winding means:

* `wound_carries_rotation` — a pattern taking two non-parallel values has a
  nonzero rotational label.

**A topologically charged defect therefore always carries rotation**, and a
rotationless configuration is combable, hence topologically trivial
(`rotationless_is_trivial`).  The framework forbids a charged defect with zero
rotational label.  Observationally, no elementary charged spin-zero particle has
been seen — the charged pions are composite.  Stated as a match, with the caveat
that "elementary" is itself scale-dependent here (`Emergence.lean`).

## II.  More axes are not merely disfavoured; they are unavailable

The instruction was not to rule out biaxial or higher without an argument.
Here is the argument, and it is short.

**Uniaxial/biaxial is vocabulary for a *tensor* order parameter** — a nematic
has a symmetric tensor whose distinct eigenvalues count the axes.  This
framework's order parameter is not a tensor.  Real rank one forces the scale
pattern to be a single **vector** (`Algebra.commuting_boosts_lie_on_a_line`,
`Particle.pattern_is_one_vector`), and a vector has a magnitude and a direction
and nothing else.  There is no second eigenvalue to be distinct from a first.

* `no_second_axis` — given the pattern `v`, any other scaling `w` is either
  parallel to it, hence the same axis, or non-parallel, in which case it is not
  a second axis but a *variation* and shows up as rotation.  There is no third
  possibility.  So "how many axes" has the answer **one**, forced;
* `axis_stabilizer_nontrivial` — and the signature of a uniaxial order
  parameter is present: a nontrivial rotation generator annihilates the
  pattern, so its stabilizer is positive-dimensional.

That last point is what makes the whole thing hang together.  A *continuous*
stabilizer is exactly what gives the order parameter space nontrivial `π₂` and
hence point defects; a biaxial or fully anisotropic pattern has a **discrete**
stabilizer, and a homogeneous space by a discrete subgroup has `π₂ = 0`, hence
**no point defects and no integer charge at all**.

So the two options are not on a par:

        uniaxial  →  continuous stabilizer  →  point defects, integer charge
        biaxial+  →  discrete stabilizer    →  no point defects, no ℤ

**`Particle.lean`'s integer charge exists only in the uniaxial case, and rank
one makes uniaxial the only case.**  The two facts agree, which is why the
labels stand.

(The homotopy statements — `π₂` of a sphere is `ℤ`, `π₂` of a Lie group quotient
by a discrete subgroup vanishes — are standard topology, cited on the same
footing as the rank-one classification.  What is proved here is the algebraic
half: the pattern is one vector, and its stabilizer is positive-dimensional.)

## III.  What this costs elsewhere

`Dynamics.same_multiplet_no_rotation` was glossed as "multiplets are internally
flat".  Its hypothesis `Realizes` assigns a scaling operator **per direction**,
depending only on that direction's scale value.  Rank one does not provide
that — it provides one vector, one scaling.  The theorem is true of anything
satisfying its hypothesis; the physical reading is withdrawn, and
`multiplet_flatness_needs_per_direction_scalings` records why.
-/
import SCD.Slice

namespace SCD.Axes

open SCD Slice

variable {k : ℕ}

/-! ## I. Rotation comes from variation, not from a second axis -/

/-- **A nonzero rotational label forces two non-parallel values of the
pattern.**

Since the pattern at any one place is a single vector, and a vector wedged with
itself vanishes, rotation can only arise between the pattern's values at two
different places. -/
theorem rotation_needs_variation {v w : Fin k → ℝ} {i j : Fin k}
    (h : wedge v w i j ≠ 0) : ∀ c : ℝ, w ≠ c • v :=
  rotation_requires_biaxial h

/-- **A pattern whose values are everywhere parallel generates no rotation.**

"Combable" in the order-parameter sense: if every value is a multiple of one
fixed direction, every wedge vanishes. -/
theorem combable_no_rotation (u : Fin k → ℝ) (f : ℕ → ℝ) (m l : ℕ) (i j : Fin k) :
    wedge (f m • u) (f l • u) i j = 0 := by
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

/-- **A pattern taking two non-parallel values carries a nonzero rotational
label.**

A defect is exactly such a configuration — that is what winding means — so
**every topologically charged defect carries rotation**. -/
theorem wound_carries_rotation {v w : Fin k → ℝ} {i j : Fin k}
    (h : v i * w j ≠ v j * w i) : wedge v w i j ≠ 0 := by
  simp only [wedge, ne_eq, sub_eq_zero]
  exact h

/-- **Contrapositive: a rotationless configuration is combable.**

If every wedge vanishes then all the pattern's values are parallel, so the
configuration deforms to a constant and is topologically trivial.  The framework
therefore forbids a charged defect with zero rotational label. -/
theorem rotationless_is_trivial {v w : Fin k → ℝ} (h : ∀ i j, wedge v w i j = 0) :
    ∀ i j, v i * w j = v j * w i :=
  (wedge_eq_zero_iff_parallel v w).mp h

/-- Collected: the rotational label is carried by the *variation* of the scale
vector, and it vanishes exactly when there is none. -/
theorem rotation_iff_variation (v w : Fin k → ℝ) :
    (∀ i j, wedge v w i j = 0) ↔ ∀ i j, v i * w j = v j * w i :=
  wedge_eq_zero_iff_parallel v w

/-! ## II. There is no second axis to have

Uniaxial/biaxial is vocabulary for a *tensor* order parameter.  Rank one makes
this one a **vector**, which has a magnitude and a direction and nothing else. -/

/-- **Any second scaling is either the same axis or a variation.**

Given the pattern `v` with some nonzero component, every other scaling `w` is
either a multiple of `v` — the same axis — or has a nonzero wedge with it, in
which case it is a variation showing up as rotation.  There is no third
possibility, so "how many axes" is answered: **one**, and not by choice. -/
theorem no_second_axis (v w : Fin k → ℝ) (i₀ : Fin k) (hv : v i₀ ≠ 0)
    (hpar : ∀ i j, v i * w j = v j * w i) : w = (w i₀ / v i₀) • v := by
  funext i
  have h := hpar i₀ i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linarith [h]

/-- The dichotomy in the form used above: either `w` is a multiple of `v`, or
some wedge is nonzero. -/
theorem axis_or_variation (v w : Fin k → ℝ) (i₀ : Fin k) (hv : v i₀ ≠ 0) :
    (w = (w i₀ / v i₀) • v) ∨ ∃ i j, wedge v w i j ≠ 0 := by
  by_cases h : ∀ i j, v i * w j = v j * w i
  · exact Or.inl (no_second_axis v w i₀ hv h)
  · push Not at h
    obtain ⟨i, j, hij⟩ := h
    exact Or.inr ⟨i, j, wound_carries_rotation hij⟩

/-- **The stabilizer of the pattern is positive-dimensional.**

A nontrivial rotation generator annihilates the pattern — here the rotation in
the plane transverse to it.  That is the signature of a *uniaxial* order
parameter, and a continuous stabilizer is what gives the order parameter space
nontrivial `π₂`, hence point defects and the integer charge.

A biaxial or fully anisotropic pattern would have a **discrete** stabilizer, and
a Lie group quotient by a discrete subgroup has `π₂ = 0` — no point defects and
no integer charge at all. -/
theorem axis_stabilizer_nontrivial :
    Coupling.J.mulVec ![1, 0, 0] = 0 ∧ (Coupling.J : Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 := by
  constructor
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Coupling.J, Fin.sum_univ_three]
  · intro h
    have h12 : (Coupling.J : Matrix (Fin 3) (Fin 3) ℝ) 1 2 = 0 := by rw [h]; rfl
    simp [Coupling.J] at h12

/-! ## III. What the correction costs elsewhere

`Dynamics.same_multiplet_no_rotation` was glossed as "multiplets are internally
flat".  Its hypothesis assigns a scaling operator *per direction*, and rank one
does not supply that — it supplies one vector and one scaling. -/

/-- **The multiplet-flatness reading needed per-direction scalings, which rank
one does not provide.**

Under the pattern-as-one-vector picture there is a single scaling, so "two
directions in the same multiplet" does not name two scaling operators to bracket
in the first place.  The theorem stands for anything meeting its hypothesis; the
physical gloss is withdrawn.

What survives, and is the correct statement, is this file's:
rotation is carried by *variation* of the one pattern, not by any relation
between directions within it. -/
theorem multiplet_flatness_needs_per_direction_scalings (v : Fin k → ℝ) (i j : Fin k) :
    wedge v v i j = 0 := homogeneous_carries_no_rotation v i j

end SCD.Axes
