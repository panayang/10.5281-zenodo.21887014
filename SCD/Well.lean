/-
# Scale wells: what a "wormhole" can be when there is no manifold

## The reading that is withdrawn

An earlier suggestion of mine read `Transport.transport_coset` as ER=EPR: two
transports of a degenerate scale pattern differ by a stabilizer element, so
"entangled regions are connected by a costless identification".

**That is wrong, and the error is the register's own.**  `Gauge.stabilizer` acts
on `Equiv.Perm (Fin n)`, and `Fin n` indexes the **directions at a point**, not
positions in space.  `transport_coset` contains no two distant places and no
non-locality whatsoever; it says a degeneracy makes a *relabelling of directions*
undetermined.  The mistake is the one `Audit.lean` §III's diagnostic is for —
*a count of what?* — applied to a new pair: direction indices versus locations.
It is logged there.

Nothing below uses it.

## What a wormhole can be here

There is no manifold, so "non-trivial topology of space" cannot even be stated.
What the framework does have is A4:

        measured length  =  s × bare length .

So a region can be *near* in the measured sense while being *far* in the bare
count, with no change of topology at all.  That is a **scale well**, and it is
the framework's own version of the object.

Three things follow immediately, and none of them is imported:

* `stretch_ne_zero` — A2 makes `s` a **unit**, so the measured length of a
  nonzero bare separation is never zero.  **There are no zero-length
  identifications here.**  GR permits a degenerate throat; this framework
  forbids one.  (This is the direct contradiction of my earlier claim.)
* `no_positive_floor` — but nothing bounds `s` away from zero either, so the
  length can be made as small as one likes.  "How long is the throat" has no
  absolute answer, only a ratio — which is the one-free-number principle again.
* `light_measured_speed_one` — light crosses the well at measured speed `1`.  So
  there is no disagreement between rulers and light about the *measured*
  geometry; the well is not a causal shortcut in the local sense.

## Where the shortcut actually is, and its sign is not fixed

The observable question is not local.  It is what a *distant* observer, using
their own units, measures for the crossing.  In the `t`–`r` plane the null
condition gives the bare crossing time per unit bare separation as `s_r/s_t`,
while a local ruler gives `s_r`.  Those are independent — until reciprocity
`s_t·s_r = 1` is imposed, and then

        crossing  =  length² .

`reciprocal_crossing_eq_length_sq`.  The two effects **compound rather than
cancel**, and the sign of the effect is the sign of `log s_r`:

        s_r > 1  →  crossing > 1  :  a Shapiro **delay**  (the Schwarzschild branch)
        s_r < 1  →  crossing < 1  :  a Shapiro **advance** (the wormhole branch)

`shapiro_delay_of_stretched` and `shapiro_advance_of_compressed`.  **These are
two branches of one family**, differing only in whether the radial unit is
stretched or compressed, and `Positivity.no_null_energy_condition` says the
axioms select neither.  In GR the advance branch requires an energy-condition
violation; here there is no energy condition to violate.

That is the sharpest honest statement available at this stage:

> The framework's wormhole is the `s_r < 1` branch of the very family that gives
> Schwarzschild, it has a strictly positive measured length, and it would show
> as a **wrong-sign Shapiro effect**.

Cassini measures the Shapiro delay to a few parts in `10⁵`, so the advance
branch is not hiding in the solar system; whether it occurs anywhere is a
question about the source law.

## What is deliberately not decided

Whether such a configuration is *produced* by a source.  That needs the scale
response law A6′, which is the framework's registered external input, and which
is being replaced.  Until then this file states the kinematics and commits to
neither branch — in particular it does **not** assume non-traversability, which
is an untested consequence of an energy condition this framework does not have.
-/
import SCD.Light
import SCD.Positivity

namespace SCD.Well

open SCD Light Frame

variable {n : ℕ}

/-! ## The measured length of a bare separation -/

section Ring

variable {A : Type*} [CommRing A]

/-- The **stretch** in direction `r`: the measured length of one unit of bare
separation.  This is the whole of A4, named so that the wormhole question can be
asked about it. -/
def stretch (E : DirScale n A) (r : Fin n) : A := (E.s r : A)

/-- **The throat never has zero length.**

`s` is a unit of the ring, so it is not a zero divisor and in particular is not
`0`.  A degenerate identification — two places at zero measured separation — is
not available in this framework, whereas it is in GR.  This is a consequence of
A2 alone.

(It is also the direct refutation of the "costless identification" reading of
`Transport.transport_coset` that this file's header withdraws.) -/
theorem stretch_ne_zero (E : DirScale n A) (r : Fin n) (h : (0 : A) ≠ 1) :
    stretch E r ≠ 0 := by
  intro hz
  apply h
  have := (E.s r).mul_inv
  rw [stretch] at hz
  rw [hz, zero_mul] at this
  exact this

end Ring

/-! ## But there is no floor, because there is no absolute scale -/

/-- **The measured length can be made arbitrarily small.**

Nothing in A1–A7 bounds the scale away from zero; A2 only forbids reaching it.
So "the throat is short" is always available and "how short" is not an absolute
question — only the ratio to some other length is, which is the framework's one
free number showing up again. -/
theorem no_positive_floor (r : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∃ E : DirScale n ℝ, 0 < stretch E r ∧ stretch E r < ε := by
  obtain ⟨u, hu0, huε⟩ := Positivity.scale_small_but_nonzero ε hε
  exact ⟨⟨fun _ => u⟩, hu0, huε⟩

/-- And arbitrarily large, so both branches below are populated. -/
theorem no_ceiling (r : Fin n) (M : ℝ) (hM : 0 < M) :
    ∃ E : DirScale n ℝ, M < stretch E r := by
  obtain ⟨u, hu⟩ := Positivity.scale_large M hM
  exact ⟨⟨fun _ => u⟩, hu⟩

/-! ## Light crosses at measured speed one

The null condition of A4′ in the `t`–`r` plane says the measured time equals the
measured length.  So locally there is no disagreement between a ruler and a
light ray — the well is not a *local* shortcut, and any shortcut it provides is
a statement about a distant observer's units. -/

section Ordered

variable {A : Type*} [CommRing A]

/-- **Measured time equals measured length across the well.**

For a null ray confined to the `t`–`r` plane, `(s_t v_t)² = (s_r v_r)²`.  Light
moves at measured speed one, which is what it means for the measured form to be
the geometry — stated here because the wormhole question is often posed as if
light and rulers could disagree locally.  They cannot. -/
theorem light_measured_speed_one (E : DirScale n A) (η : Fin n → A) (t r : Fin n)
    (hne : t ≠ r) (ht : η t = -1) (hr : η r = 1) (v : Fin n → A)
    (hsupp : ∀ a, a ≠ t → a ≠ r → v a = 0) (hnull : IsNullDir E η v) :
    ((E.s t : A) * v t) ^ 2 = ((E.s r : A) * v r) ^ 2 := by
  have h := (null_plane_condition E η t r hne ht hr v hsupp).mp hnull
  calc ((E.s t : A) * v t) ^ 2 = ((E.s t : A)) ^ 2 * (v t * v t) := by ring
    _ = ((E.s r : A)) ^ 2 * (v r * v r) := h
    _ = ((E.s r : A) * v r) ^ 2 := by ring

/-! ## The crossing seen from outside, and the sign that is not fixed -/

/-- **The bare crossing time, squared.**

Setting the bare separation `v_r = 1`, the null condition reads
`s_t² v_t² = s_r²`, so the bare time `v_t` satisfies `(s_t v_t)² = s_r²`.  This
is the quantity a distant observer's clock counts, before their own unit is
applied. -/
theorem bare_crossing_sq (E : DirScale n A) (η : Fin n → A) (t r : Fin n)
    (hne : t ≠ r) (ht : η t = -1) (hr : η r = 1) (v : Fin n → A)
    (hsupp : ∀ a, a ≠ t → a ≠ r → v a = 0) (hv : v r = 1)
    (hnull : IsNullDir E η v) :
    ((E.s t : A)) ^ 2 * (v t) ^ 2 = ((E.s r : A)) ^ 2 := by
  have h := (null_plane_condition E η t r hne ht hr v hsupp).mp hnull
  rw [hv, mul_one, mul_one] at h
  calc ((E.s t : A)) ^ 2 * (v t) ^ 2 = ((E.s t : A)) ^ 2 * (v t * v t) := by ring
    _ = ((E.s r : A)) ^ 2 := h

/-- **Under reciprocity, crossing time is length squared.**

With `s_t · s_r = 1` the bare crossing time obeys `v_t² = s_r⁴ = (s_r²)²`.  So
the ruler effect and the clock effect **compound**: a compressed radial unit is
crossed in less bare time, not the same time.

This is the framework's version of the Shapiro effect, and it has no free
parameter once reciprocity holds. -/
theorem reciprocal_crossing_eq_length_sq (E : DirScale n A) (η : Fin n → A)
    (t r : Fin n) (hne : t ≠ r) (ht : η t = -1) (hr : η r = 1)
    (hrec : E.Reciprocal t r) (v : Fin n → A)
    (hsupp : ∀ a, a ≠ t → a ≠ r → v a = 0) (hv : v r = 1)
    (hnull : IsNullDir E η v) :
    (v t) ^ 2 = (((E.s r : A)) ^ 2) ^ 2 := by
  have hval : (E.s t : A) * (E.s r : A) = 1 := by
    simpa using congrArg (Units.val (α := A)) hrec
  have h := bare_crossing_sq E η t r hne ht hr v hsupp hv hnull
  calc (v t) ^ 2 = ((E.s t : A) * (E.s r : A)) ^ 2 * (v t) ^ 2 := by
        rw [hval, one_pow, one_mul]
    _ = ((E.s r : A)) ^ 2 * (((E.s t : A)) ^ 2 * (v t) ^ 2) := by ring
    _ = ((E.s r : A)) ^ 2 * ((E.s r : A)) ^ 2 := by rw [h]
    _ = (((E.s r : A)) ^ 2) ^ 2 := by ring

end Ordered

/-! ## The two branches

Over the reals the compounding above has a sign, and the sign is the whole
observational content: a stretched radial unit delays light and a compressed one
advances it.  Nothing in A1–A7 chooses between them
(`Positivity.no_null_energy_condition`). -/

/-- **The Schwarzschild branch: a stretched radial unit delays light.**

`s_r > 1` gives crossing time `s_r⁴ > 1`: light takes longer than the bare count.
That is the Shapiro delay, measured by Cassini to a few parts in `10⁵`. -/
theorem shapiro_delay_of_stretched (x : ℝ) (h : 1 < x) : 1 < (x ^ 2) ^ 2 := by
  have h1 : (1 : ℝ) < x ^ 2 := by nlinarith
  nlinarith

/-- **The wormhole branch: a compressed radial unit advances light.**

`s_r < 1` gives crossing time `s_r⁴ < 1`: light arrives *earlier* than the bare
count.  In GR this branch requires violating the null energy condition; here
there is no such condition to violate (`Positivity.no_null_energy_condition`),
so it is not excluded by anything the axioms say.

**This is a prediction only if a source produces it**, which is a question about
the scale response law and is open.  What is settled is that the framework does
not forbid it, and that if it occurs it shows as a **wrong-sign Shapiro
effect** — a signature with no free parameter. -/
theorem shapiro_advance_of_compressed (x : ℝ) (h0 : 0 < x) (h : x < 1) :
    (x ^ 2) ^ 2 < 1 := by
  have h1 : x ^ 2 < 1 := by nlinarith
  have h2 : (0 : ℝ) < x ^ 2 := by positivity
  nlinarith

/-- **The dichotomy, and that it is exactly a dichotomy.**

The crossing time is greater than, equal to, or less than the bare count exactly
as the radial unit is stretched, trivial, or compressed.  There is no third
behaviour, and the axioms do not select among the three. -/
theorem branch_trichotomy (x : ℝ) (h0 : 0 < x) :
    (1 < x → 1 < (x ^ 2) ^ 2) ∧ (x = 1 → (x ^ 2) ^ 2 = 1)
      ∧ (x < 1 → (x ^ 2) ^ 2 < 1) :=
  ⟨shapiro_delay_of_stretched x, fun h => by rw [h]; norm_num,
   shapiro_advance_of_compressed x h0⟩

/-! ## What is measurable

The well's depth is not an absolute length — it is the ratio of two
measurements of the same crossing.  A distant clock gives the crossing time; a
local ruler gives the length.  Under reciprocity the first is the square of the
second, so the depth is recoverable from the pair, with nothing left free. -/

/-- **The depth is the ratio of the crossing to the length.**

`crossing = length²`, so `crossing / length = length`.  Stated without division:
the crossing equals the length times the length.  Two independent measurements
therefore over-determine one number, which is what makes this testable rather
than a fit. -/
theorem depth_from_crossing_and_length (len cross : ℝ) (h : cross = len ^ 2) :
    cross = len * len := by rw [h]; ring

/-- And the over-determination stated as such: if the crossing and the length
are measured independently, their relation is fixed with no adjustable
parameter.  A mismatch falsifies reciprocity, which by `Vacuum.lean` is the
asymptotic-flatness step — the step this development is trying to remove. -/
theorem crossing_length_relation_has_no_parameter (len cross : ℝ)
    (h : cross = len ^ 2) (c : ℝ) (hc : cross = c * len ^ 2) (hlen : len ≠ 0) :
    c = 1 := by
  rw [h] at hc
  have hne : (len : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hlen
  have : (1 : ℝ) * len ^ 2 = c * len ^ 2 := by rw [one_mul]; exact hc
  exact (mul_right_cancel₀ hne this).symm

end SCD.Well
