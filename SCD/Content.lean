/-
# The framework was writing presheaves without the vocabulary

`Disconnect.lean` found that 59 of the development's 107 files never mention
`ScaleAlgebra`, and that the escape to real numbers has been re-invented **eight
times** — `Defect.ScaleDefect`'s lift, `Emergence.resolved`'s thresholds,
`Observer.Resolution`, `Particle.Species.threshold`, `Running.resolvedCount`,
`Scanning.scanRate`, `Spectrum.gaps`, and my own `Bridge.DriftEval` — with no
theorem relating any two.

That is not a backlog.  It says the development has **one stated primitive and one
unstated one**, and the obvious repair — bolt a real-valued evaluation onto the
ring — is the symptom rather than the cure: eight places each invented it because
it is intuitive, and eight incompatible versions is what "intuitive but not the
right primitive" looks like.

So the question is whether a different primitive fits better, and the framework's
own theorems can be asked before anything is rebuilt.

## The test

`ContentSystem` is a presheaf on a preorder, written plainly so the framework's
statements can be **checked against it** rather than translated into it.  The
functor laws on a preorder are monotonicity and nothing else.

Three of the development's own results are exactly those laws:

* `emergenceSystem` — content on the scale axis, monotone by
  `Emergence.resolved_mono`;
* `filtrationSystem` — content on the resolutions, monotone by
  `Resolution.Filtration.resolved_mono`;
* `observerSystem` — content on the parts, monotone on the **opposite** order by
  `Internal.record_antitone`.

Two variances, one vocabulary, and every monotonicity proof was already in the
repository.  Nothing was adapted to fit.

## And the one that decides it

`pullback_eq_emergence` typechecks with `:=` and no proof: **`Layers.resolved_is_emergence_resolved`
already *is* the statement that the algebraic system and the real-valued one are
the same system**, index by index.

> The algebra and the thresholds were never two structures.  They are one
> presheaf, described twice, and the description was the only thing missing.

## What this does not establish, and the list is honest

* **no topos, no site, no sheaf.**  `ContentSystem` is a presheaf on a preorder.
  There is no covering family here and no gluing condition, so nothing in this
  file earns the word *sheaf*.  What would be needed is a notion of when a family
  of resolutions covers a scale, and the framework has none;
* **the cosmological sector is untouched.**  `Scanning` and `DarkEnergy` are still
  bare reals with no system structure at all, so §V.al's disconnection stands for
  them.  Three of the eight escapes are unified here; five are not;
* **and nothing is refactored.**  This file is additive.  If the direction fails,
  deleting it changes nothing else — which is the property a foundational
  experiment should have before it is a foundational commitment.
-/
import SCD.Disconnect
import SCD.Layers
import SCD.Emergence
import SCD.Internal

namespace SCD.Content

open SCD


/-- **A content system**: an assignment of content to indices, monotone.

This is a presheaf on a preorder, written without the vocabulary so that the
framework's own statements can be checked against it rather than translated into
it.  The functor laws are `mono` and nothing else, because a preorder has no
non-identity parallel arrows. -/
structure ContentSystem (I : Type*) [Preorder I] (X : Type*) where
  /-- What is present at index `i`. -/
  content : I → Set X
  /-- And a larger index contains more. -/
  mono : ∀ {i j : I}, i ≤ j → content i ⊆ content j

namespace ContentSystem

variable {I X : Type*} [Preorder I] (S : ContentSystem I X)

/-- Functoriality at the identity, which a preorder makes trivial and which is
stated so the check is complete rather than assumed. -/
theorem mono_refl (i : I) : S.content i ⊆ S.content i := S.mono le_rfl

/-- And under composition. -/
theorem mono_trans {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    S.content i ⊆ S.content k := S.mono (le_trans hij hjk)

end ContentSystem

/-! ## The framework's two systems -/

/-- **`Emergence.resolved` is a content system on the scale axis.**

Its monotonicity is `Emergence.resolved_mono`, already proved — the framework
wrote the functor law and did not name it. -/
def emergenceSystem (μ : ℕ → ℝ) : ContentSystem ℝ ℕ where
  content t := Emergence.resolved μ t
  mono h := Emergence.resolved_mono μ h

/-- **And a filtration is a content system on the resolutions.**

Its monotonicity is `Resolution.Filtration.resolved_mono`, likewise already
proved. -/
def filtrationSystem {A : Type*} [Ring A] (F : Resolution.Filtration A) :
    ContentSystem ℕ A where
  content k := {a | F.Resolved k a}
  mono h _ ha := F.resolved_mono h ha

/-- The filtration system pulled back along a family of ring elements, so that
the two systems have the same carrier and can be compared. -/
def pullbackSystem {A ι : Type*} [Ring A] (F : Resolution.Filtration A) (e : ι → A) :
    ContentSystem ℕ ι where
  content k := {i | F.Resolved k (e i)}
  mono h _ hi := F.resolved_mono h hi

/-! ## And they are one system, seen twice -/

/-- **The algebraic system *is* the real-valued one, along the cast.**

`Layers.resolved_is_emergence_resolved` said this without the vocabulary: what a
filtration resolves in a family of ring elements is exactly what the
`Emergence.resolved` of the induced thresholds resolves.  Read as systems, it is
an equality of content at every index — the two sectors were never two
structures, they were one presheaf described twice. -/
theorem pullback_eq_emergence {A : Type*} [Ring A] (F : Resolution.Filtration A)
    {thr : A → ℕ} (h : Layers.HasThreshold F thr) (e : ℕ → A) (k : ℕ) :
    (pullbackSystem F e).content k
      = (emergenceSystem (fun i => ((thr (e i) : ℝ) + 1))).content (k : ℝ) :=
  Layers.resolved_is_emergence_resolved h e k

/-! ## And the observer is one too, with the other variance -/

/-- **The internal observer is a content system on the *opposite* order.**

`Internal.record_antitone` says a larger observer records less, so the record is
monotone in the reversed order of parts.  Two variances, one vocabulary: the
scale axis is covariant, the observer contravariant, and both are the same kind
of object. -/
def observerSystem {n : ℕ} {ι : Type*} (μ : ι → Observer.Threshold n)
    (σ : Observer.Resolution n) : ContentSystem (Finset (Fin n))ᵒᵈ ι where
  content S := Internal.record (OrderDual.ofDual S) μ σ
  mono h := Internal.record_antitone μ σ (by exact h)


end SCD.Content
