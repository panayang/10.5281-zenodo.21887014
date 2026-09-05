/-
# The codimension mismatch: one of the two ways out is closed

§V.k found that `Δσ = Δ·ν` is a **codimension-two equation applied to a
codimension-three source**, and offered two ways out:

* *(a)* the source is codimension two after all — strings — which reopens
  `Codimension.lean`'s retraction;
* *(b)* the law is rewritten with a **degree** density, which the grading permits
  but which does not preserve the specific form of A6″.

**(a) is dead**, and the framework's own charge structure kills it.

## The argument

`Axis.lean` says the projective order parameter carries *both* kinds of defect:
line defects with `π₁ = ℤ/2` and point defects with `π₂ = ℤ`.  So codimension two
is available — but at a **two-valued** charge.

The source law needs `ν` **additive**: that is what makes it an index rather than
a response, and `Flux.flux_combine` is the framework proving it for the flux.
And `two_valued_source_is_trivial`: an additive map from a two-element group to
the reals is **identically zero**, because `a·a = 1` forces `2f(a) = 0` and `ℝ`
has no two-torsion.  `odd_pairs_cancel` is the group step, which is
`Particle.two_odd_make_even` — the framework's own selection rule.

> **No source can be built from the block label, whatever the map.**

So the codimension-two defects that the framework actually has cannot source the
geometry, and (a) is closed.

## What that does to the other three integers

§V.g tabulated three integers used interchangeably as "the charge that sources
the geometry".  All three are now eliminated, by three different arguments:

* `Defect.ScaleDefect.winding` — `π₁` of the **scalar circle**, scoped out by §I
  since A4 is directional.  `Flux.lean`'s Gauss law is proved for exactly this
  object, so **the Gauss law lives entirely inside the scoped-out picture**;
* `Charges.block` — `π₁` of the projective axis, eliminated here;
* `Charges.hedgehog` — `π₂`, signed, and `Attraction.signed_source_would_antigravitate`
  says a signed source makes antimatter fall up.

What is left is `Particle.Species.threshold`, which is **not a topological label
at all** — and that is exactly what `Attraction.lean` concluded on empirical
grounds.  It is now reached by exhaustion as well.

## What this costs, stated and not minimised

`Index.A6'_from_index` derives `κ = −2(n−1)Δ` from `IndexResponse : lap σ = Δ·ν`.
That derivation is **algebraic in `ν`** and survives unchanged, whatever `ν` turns
out to count — the factor is not in danger.

What is in danger is `IndexResponse` itself.  Its standing came from `ν` being a
**topological index**: a winding is additive and integral for reasons outside the
dynamics, which is what let A6″ be read as a law rather than a posit.  With all
three topological integers eliminated and a threshold count left, `ν` is a
cardinality of the framework's own making.

> **A6″ keeps its consequences and loses its index reading.**

It is now a postulate about how counting sources scale, of the same standing as
the rest of A1–A7 — which is not nothing, but is less than the register has been
treating it as.

**What is not claimed.**  That the law with a degree density is false, or that it
cannot be written.  Only that (a) is closed, that the label left standing is not
topological, and that A6″ should be read henceforth as a posit rather than as an
index theorem.
-/
import SCD.OneParameter
import SCD.Particle
import SCD.Flux

namespace SCD.Codimension2

open SCD


/-- **A real-valued additive source built on a two-valued charge vanishes.**

The source law `Δσ = Δ·ν` needs `ν` **additive** — that is what makes it an index
rather than a response, and `Flux.flux_combine` is the framework proving exactly
that for the flux.  But an additive map from a two-element group to the reals is
zero: `a·a = 1` forces `2 f a = f 1 = 0`, and `ℝ` has no two-torsion.

So no source can be built from the block label, whatever the map. -/
theorem two_valued_source_is_trivial (f : Multiplicative (ZMod 2) → ℝ)
    (hf : ∀ a b, f (a * b) = f a + f b) (a : Multiplicative (ZMod 2)) : f a = 0 := by
  have h1 : f 1 = 0 := by
    have := hf 1 1
    rw [one_mul] at this
    linarith
  have haa : a * a = 1 := by
    revert a
    decide
  have := hf a a
  rw [haa, h1] at this
  linarith

/-- **The line defects of the framework's own order parameter carry exactly that
charge.**

`Particle.Block` is `Multiplicative (ZMod 2)`, and `Particle.block_two_valued`
says it has two elements.  So the codimension-two defects of the projective axis
cannot source the geometry. -/
theorem block_cannot_source (f : Particle.Block → ℝ)
    (hf : ∀ a b, f (a * b) = f a + f b) (a : Particle.Block) : f a = 0 :=
  two_valued_source_is_trivial f hf a

/-- **And the framework's composition law is what makes it two-valued.**

Two non-trivial block charges compose to the trivial one — which is
`Particle.two_odd_make_even` at the level of the group, and the step the theorem
above turns on.  So the obstruction is the framework's own selection rule and not
an artefact of the encoding. -/
theorem odd_pairs_cancel (a b : Particle.Block) (ha : a ≠ 1) (hb : b ≠ 1) :
    a * b = 1 := by
  revert a b
  decide


end SCD.Codimension2
