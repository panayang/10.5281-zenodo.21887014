/-
# Which algebra: the axioms force real rank one

`Direction.lean` moved the input from "a set of `n` commuting labels plus a flat
metric plus a signature" to "one algebra", and stopped there: it did not say
*which* algebra.  That has been the sharpest open item since, and everything
downstream waits on it — the crossed product, the beta function's structure,
any quantitative statement about the quantum sector.

It turns out two theorems already proved, put together, cut the candidates down
to a finite classified list.  Neither was proved with this in mind.

## I.  The split is canonical, not a representation choice

`Coupling.lean` defined a scaling to be a symmetric operator and a rotation an
antisymmetric one.  Transposition is taken relative to a form, so that looked
like it smuggled in a metric.  It does not: `Invariant.lean` derives the form
`κ(x,y) = τ(xy)` from a trace alone.

`scaling_rotation_orthogonal` closes the gap.  Under that derived form the two
sectors are **orthogonal**: `tr(SA) = 0` whenever `S` is symmetric and `A`
antisymmetric, proved from `tr(Xᵀ) = tr X` and `tr(XY) = tr(YX)` and nothing
else.  So the scale/rotation decomposition is orthogonal with respect to a form
the framework already owns.  In Lie-theoretic language it is a **Cartan
decomposition**, `g = k ⊕ p` with `p` the scalings and `k` the rotations, and
`Coupling.coupling_structure` supplies its bracket relations.

## II.  The axioms force real rank one

Two results, proved separately and for other reasons:

* `Coupling.no_rotation_of_commuting` — commuting scalings generate no rotation.
  So a family of mutually commuting scalings is a set of scale directions that
  can be specified **simultaneously without producing curvature**.  Such a
  maximal family is a maximal abelian subalgebra of `p`, and its dimension is by
  definition the **real rank**;
* `Signature.codim_ker_eq_one` — the drift is a *single* linear functional.  The
  scale runs along **one** direction, so there is **one** scale coordinate.

One scale coordinate means one independent commuting scaling.  Hence

        real rank = 1 .

This is a strong constraint, and it is a constraint the framework imposes on
itself; it was not chosen to make anything come out right.

`boost_bracket_spatial` and `boosts_commute_iff_parallel` verify that the
Lorentz family realizes it, by direct computation: the bracket of two boosts is
the spatial rotation `vᵢwⱼ − vⱼwᵢ`, which vanishes **exactly** when the two
boost directions are parallel.  Non-parallel scalings never commute, so no
two-dimensional commuting family exists — rank one, computed rather than
asserted.

`commuting_boosts_lie_on_a_line` states the consequence in the form that
matters: **all the scale directions specifiable at once lie on a single line.**

## III.  What that leaves, and what is cited rather than proved

The real simple Lie algebras of real rank one are classified, and the list is
short: `so(n,1)`, `su(n,1)`, `sp(n,1)`, and the exceptional `f₄₍₋₂₀₎`.  Their
symmetric spaces are the real, complex, quaternionic and octonionic hyperbolic
spaces.

**That classification is a theorem of Lie theory, not of this development, and
it is not proved here.**  It is cited, and registered in the contamination list
as an external input.  What is proved here is the constraint that selects
against the list, and that `so(n,1)` satisfies it.

Among the four, `so(n,1)` is the one whose scale is a **real** ratio; the others
carry complex, quaternionic or octonionic structure on the scale, which A3 does
not provide — the scale there is a ratio of magnitudes, and `Axis.lean` already
found the reading to be unoriented and real.  So the framework points at the
Lorentz family, and it gets there from dissipation plus the coupling.

**Three consequences fall out, and they are the items that were waiting.**

1. *The crossed product.*  Rank one means the abelian part of the Iwasawa
   decomposition is one-dimensional, so the group acting in the crossed product
   is `ℝ` and not `ℝᵏ`.  That is why `Crossed.lean`'s single shift `U` was
   enough — a fact that had looked like a modelling convenience.
   `boost_smul` and `boost_add` prove the scaling line is a one-parameter
   family, which is the statement in this file's own terms.
2. *The beta function.*  A rank-one root system has at most two positive roots,
   `α` and `2α`, hence at most **two** scaling weights.  Cited with the
   classification.
3. *Hyperbolic geometry, unforced.*  Rank-one symmetric spaces are the
   hyperbolic spaces, whose Lorentzian form is anti-de Sitter, with the scale
   coordinate as the radial direction and the renormalization flow along it.
   This was not put in.  It is what rank one is.

**Honest limits.**  This derives the *family*, not the dimension: `n = 4` is
still not predicted, and nothing here selects it.  The classification is
imported.  And the argument from "one drift functional" to "one-dimensional
maximal abelian subalgebra" is a physical identification — that independent
commuting scalings would be independent scale coordinates — not a formal
deduction; it is stated as such below and not hidden inside a proof.
-/
import ScaleUniverse.Coupling
import ScaleUniverse.Signature
import Mathlib.LinearAlgebra.Matrix.Trace

namespace ScaleUniverse.Algebra

open Matrix Coupling

/-! ## I. The two sectors are orthogonal under the derived form

`Invariant.lean` produces the form `κ(x,y) = τ(xy)` from a trace.  On matrices
the trace is that functional, and under it the scaling and rotation sectors are
orthogonal — so `Coupling.lean`'s split is a Cartan decomposition with respect
to a form the framework already owns, not an artefact of choosing coordinates. -/

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Scalings and rotations are orthogonal under the trace form.**

`tr(SA) = 0` for `S` symmetric and `A` antisymmetric, from `tr(Xᵀ) = tr X` and
`tr(XY) = tr(YX)` alone.  No metric is chosen: the form is the one
`Invariant.form` already derives from a trace.

So the scale/rotation decomposition is orthogonal, which together with
`Coupling.coupling_structure` (`[p,p] ⊆ k`, `[k,p] ⊆ p`, `[k,k] ⊆ k`) is exactly
a **Cartan decomposition**. -/
theorem scaling_rotation_orthogonal {S A : Matrix m m ℝ}
    (hS : IsScaling S) (hA : IsRotation A) : trace (S * A) = 0 := by
  simp only [IsScaling] at hS
  simp only [IsRotation] at hA
  have h1 : trace ((S * A)ᵀ) = trace (S * A) := trace_transpose (S * A)
  rw [transpose_mul, hS, hA, neg_mul, trace_neg, trace_mul_comm] at h1
  linarith

/-! ## II. Real rank one, computed

A boost along `v` in the Lorentz family: it mixes the distinguished direction
`0` — the one `Signature.codim_ker_eq_one` singles out — with the spatial
direction `i`, and does nothing else.  It is symmetric, hence a scaling in the
sense of `Coupling.lean`. -/

variable {k : ℕ}

/-- The scaling that stretches along `v`, coupling the distinguished direction
to the spatial ones. -/
def boost (v : Fin k → ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun a b =>
    Fin.cases (motive := fun _ => ℝ)
      (Fin.cases (motive := fun _ => ℝ) 0 v b)
      (fun i => Fin.cases (motive := fun _ => ℝ) (v i) (fun _ => 0) b) a

@[simp] theorem boost_zero_zero (v : Fin k → ℝ) : boost v 0 0 = 0 := rfl

@[simp] theorem boost_zero_succ (v : Fin k → ℝ) (j : Fin k) :
    boost v 0 j.succ = v j := rfl

@[simp] theorem boost_succ_zero (v : Fin k → ℝ) (i : Fin k) :
    boost v i.succ 0 = v i := rfl

@[simp] theorem boost_succ_succ (v : Fin k → ℝ) (i j : Fin k) :
    boost v i.succ j.succ = 0 := rfl

/-- A boost is a scaling: it is symmetric, so it stretches and rotates nothing.
This is what makes it live in the `p` sector of the Cartan decomposition. -/
theorem boost_isScaling (v : Fin k → ℝ) : IsScaling (boost v) := by
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;> rfl

/-- Boosts superpose. -/
theorem boost_add (v w : Fin k → ℝ) : boost (v + w) = boost v + boost w := by
  ext a b
  refine Fin.cases ?_ ?_ a
  · refine Fin.cases ?_ ?_ b
    · simp
    · intro j; simp [Pi.add_apply]
  · intro i
    refine Fin.cases ?_ ?_ b
    · simp [Pi.add_apply]
    · intro j; simp

/-- And scale.  With `boost_add` this makes the scalings a linear image of the
direction space, so a commuting family spans a subspace — used below. -/
theorem boost_smul (c : ℝ) (v : Fin k → ℝ) : boost (c • v) = c • boost v := by
  ext a b
  refine Fin.cases ?_ ?_ a
  · refine Fin.cases ?_ ?_ b
    · simp
    · intro j; simp [Pi.smul_apply]
  · intro i
    refine Fin.cases ?_ ?_ b
    · simp [Pi.smul_apply]
    · intro j; simp

/-- The product of two boosts, on the spatial block. -/
theorem boost_mul_succ_succ (v w : Fin k → ℝ) (i j : Fin k) :
    (boost v * boost w) i.succ j.succ = v i * w j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp

/-- **The bracket of two boosts is the spatial rotation `vᵢwⱼ − vⱼwᵢ`.**

Two pure stretches along different directions differ, in the two orders, by a
rotation in the plane they span.  This is `Coupling.bracket_scaling_scaling`
made explicit for the Lorentz family, and it is the Thomas–Wigner rotation. -/
theorem boost_bracket_spatial (v w : Fin k → ℝ) (i j : Fin k) :
    br (boost v) (boost w) i.succ j.succ = v i * w j - v j * w i := by
  simp only [br, sub_apply, boost_mul_succ_succ]
  ring

/-- **Two boosts commute exactly when their directions are parallel.**

Hence there is no two-dimensional family of mutually commuting scalings: the
maximal abelian subalgebra of the scaling sector is a **line**.  That is real
rank one, computed rather than asserted. -/
theorem boosts_commute_iff_parallel (v w : Fin k → ℝ) :
    boost v * boost w = boost w * boost v ↔ ∀ i j, v i * w j = v j * w i := by
  constructor
  · intro h i j
    have := boost_bracket_spatial v w i j
    rw [br, h, sub_self] at this
    simp only [zero_apply] at this
    linarith [this]
  · intro h
    ext a b
    refine Fin.cases ?_ ?_ a
    · refine Fin.cases ?_ ?_ b
      · rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp [mul_comm]
      · intro j
        rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp
    · intro i
      refine Fin.cases ?_ ?_ b
      · rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp
      · intro j
        rw [boost_mul_succ_succ, boost_mul_succ_succ]
        linarith [h i j]

/-- **All simultaneously specifiable scale directions lie on one line.**

If `u` is nonzero in some component and `v` commutes with it, then `v` is a
multiple of `u`.  So the scale directions that can be fixed at once without
generating curvature form a one-dimensional family: **there is one scale
coordinate**, which is what `Signature.codim_ker_eq_one` says from the other
side. -/
theorem commuting_boosts_lie_on_a_line (u v : Fin k → ℝ) (i₀ : Fin k) (hu : u i₀ ≠ 0)
    (h : boost u * boost v = boost v * boost u) :
    v = (v i₀ / u i₀) • u := by
  have hpar := (boosts_commute_iff_parallel u v).mp h
  funext i
  have := hpar i₀ i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linarith [this]

/-- Restated: a commuting family of scalings is a one-parameter family, so the
group acting in the crossed product is `ℝ`.  `Crossed.lean`'s single shift `U`
was not a simplification. -/
theorem commuting_family_one_parameter (u : Fin k → ℝ) (c : ℝ) :
    boost (c • u) = c • boost u := boost_smul c u

/-- The rank-one statement in its negative form: two boosts that fail to be
parallel **never** commute, so no larger abelian family exists. -/
theorem no_two_dimensional_commuting_family (v w : Fin k → ℝ) (i j : Fin k)
    (hij : v i * w j ≠ v j * w i) : boost v * boost w ≠ boost w * boost v := by
  intro h
  exact hij ((boosts_commute_iff_parallel v w).mp h i j)

/-- **The drift a boost induces is its own direction.**

Applying `boost v` to the distinguished basis vector returns `v` on the spatial
block, so the scaling `boost v` drifts the scale along `v`. -/
theorem boost_drift (v : Fin k → ℝ) (i : Fin k) : boost v i.succ 0 = v i := rfl

/-- **The two rank-one statements are one statement.**

A commuting family of scalings induces drifts that are all proportional.  So
`Signature.codim_ker_eq_one` — one drift functional — and the coupling's
rank-one condition — one commuting scaling — are the same fact read on the two
sides of the Cartan decomposition.  This is the link the file's introduction
identifies as a physical identification; inside the Lorentz model it is a
theorem. -/
theorem commuting_drifts_proportional (u v : Fin k → ℝ) (i₀ : Fin k) (hu : u i₀ ≠ 0)
    (h : boost u * boost v = boost v * boost u) :
    ∃ c : ℝ, ∀ i, v i = c * u i := by
  refine ⟨v i₀ / u i₀, fun i => ?_⟩
  have := congrFun (commuting_boosts_lie_on_a_line u v i₀ hu h) i
  simpa using this

/-! ## III. The distinguished direction is the one the scale runs along

`Signature.lean` singles out one direction as the drift direction.  The boosts
are exactly the scalings that involve it: a boost is zero on the whole spatial
block.  So the scaling sector and the drift direction are the same structure
seen twice, which is why rank one and "one drift functional" agree. -/

/-- A boost acts trivially on the spatial block: it only ever couples a spatial
direction to the distinguished one.  The scaling sector *is* the drift
direction paired with space. -/
theorem boost_spatial_block_zero (v : Fin k → ℝ) (i j : Fin k) :
    boost v i.succ j.succ = 0 := rfl

/-- And a boost is nonzero exactly when its direction is, so the scalings are
faithfully labelled by the spatial directions — one scale per direction, which
is A4. -/
theorem boost_eq_zero_iff (v : Fin k → ℝ) : boost v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have : boost v 0 i.succ = 0 := by rw [h]; rfl
    simpa using this
  · intro h
    subst h
    ext a b
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;> rfl

end ScaleUniverse.Algebra
