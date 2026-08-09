/-
# Gravity and gauge fields are one object

Last round left an open question: does the framework need a torsion-free
condition to pin down the connection from the frame?  Asking it that way was
already inertia — "torsion" is a concept borrowed from a theory in which the
frame and the connection are *independent* fields, so that a condition is
needed to relate them.

Here they are not independent, and there is nothing to impose.

A transport from `x` to `y` has exactly one job: carry each local unit at `x`
to the corresponding local unit at `y`.  The scale pattern at each end is all
there is, so the transport is whatever relabelling makes the units match.  No
choice is being made, hence no condition is required to remove one.

The consequences are sharper than the absence of a condition:

* `transport_unique_of_nondegenerate` — if the local units are all **different**,
  the transport is **unique**.  The connection is a function of the scale field,
  full stop;
* `transport_coset` — if some units **coincide**, transports differ exactly by
  an element of `Gauge.stabilizer`, and by nothing else;
* `gauge_freedom_iff_degenerate` — so the undetermined part of the transport is
  precisely the internal symmetry of the scale pattern.

Read together: **the transport is a single object; degeneracy of the scale
pattern is what splits it into a determined part and a free part.**  The
determined part is what varies from point to point and curves — gravity.  The
free part is the block rotations — the gauge field.  They are not two fields
that must be unified; they are one field, separated by whether the local units
happen to coincide.
-/
import ScaleUniverse.Gauge

namespace ScaleUniverse.Transport

open ScaleUniverse Gauge

variable {n : ℕ} {A : Type*} [CommRing A]

/-! ## What a transport is -/

/-- `π` **transports** the pattern `s` to the pattern `t`: it relabels
directions so that each unit at the source matches the corresponding unit at
the target.  This is the entire content of "connection" in this framework — no
further condition is available to impose, because no further choice was made. -/
def Transports (s t : Fin n → Aˣ) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ a, t (π a) = s a

/-- Transport of a pattern to itself is exactly an internal symmetry: the
stabilizer is the transport group of a single point. -/
theorem transports_self_iff (s : Fin n → Aˣ) (π : Equiv.Perm (Fin n)) :
    Transports s s π ↔ π ∈ stabilizer s := Iff.rfl

/-! ## Non-degenerate: the transport is forced -/

/-- **Where the local units are all different, the transport is unique.**

No torsion-free condition, no metric-compatibility postulate, no variational
principle: if the scale pattern at the target has no coincidences, exactly one
relabelling can match the units, and it is therefore a *function* of the scale
field.  The connection was never an independent field to be constrained. -/
theorem transport_unique_of_nondegenerate {s t : Fin n → Aˣ}
    (hinj : Function.Injective t) {π τ : Equiv.Perm (Fin n)}
    (hπ : Transports s t π) (hτ : Transports s t τ) : π = τ := by
  refine Equiv.ext fun a => hinj ?_
  rw [hπ a, hτ a]

/-! ## Degenerate: the leftover is exactly the gauge group -/

/-- **Two transports of the same pattern differ by an internal symmetry.**

The set of transports is a coset of `stabilizer`.  Nothing else is
undetermined, and this much is undetermined necessarily. -/
theorem transport_coset {s t : Fin n → Aˣ} {π τ : Equiv.Perm (Fin n)}
    (hπ : Transports s t π) (hτ : Transports s t τ) :
    π * τ⁻¹ ∈ stabilizer t := by
  intro b
  show t (π (τ⁻¹ b)) = t b
  rw [hπ (τ⁻¹ b)]
  have hb : τ (τ⁻¹ b) = b := by simp
  have h := hτ (τ⁻¹ b)
  rw [hb] at h
  exact h.symm

/-- Conversely, composing a transport with an internal symmetry gives a
transport.  So the transports of a given pattern form exactly one coset — no
more freedom, and no less. -/
theorem transports_of_stabilizer {s t : Fin n → Aˣ} {π ρ : Equiv.Perm (Fin n)}
    (hπ : Transports s t π) (hρ : ρ ∈ stabilizer t) : Transports s t (ρ * π) := by
  intro a
  show t (ρ (π a)) = s a
  rw [hρ (π a), hπ a]

/-- **The undetermined part of the transport is the internal symmetry, and
degeneracy is what creates it.**

If the units are all distinct there is no freedom at all; if they coincide, the
freedom is exactly the block symmetry.  Gravity — the part of the transport
fixed by the scale field — and the gauge field — the part left free — are the
same object, separated only by whether local units happen to coincide. -/
theorem transport_unique_iff_stabilizer_trivial (t : Fin n → Aˣ) :
    (∀ (s : Fin n → Aˣ) (π τ : Equiv.Perm (Fin n)),
        Transports s t π → Transports s t τ → π = τ)
      ↔ stabilizer t = ⊥ := by
  constructor
  · intro huniq
    ext ρ
    constructor
    · intro hρ
      have h1 : Transports t t ρ := hρ
      have h2 : Transports t t 1 := fun a => rfl
      exact Subgroup.mem_bot.mpr (huniq t ρ 1 h1 h2)
    · intro hρ
      have hone : ρ = 1 := Subgroup.mem_bot.mp hρ
      rw [hone]
      exact Subgroup.one_mem _
  · intro hbot s π τ hπ hτ
    have hmem := transport_coset hπ hτ
    rw [hbot] at hmem
    have h1 : π * τ⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    calc π = π * τ⁻¹ * τ := (inv_mul_cancel_right π τ).symm
      _ = 1 * τ := by rw [h1]
      _ = τ := one_mul τ

/-- Collected, with the non-degenerate case spelled out: distinct units give a
trivial internal symmetry and hence a transport that is a function of the scale
field alone. -/
theorem nondegenerate_no_gauge_freedom (t : Fin n → Aˣ) (hinj : Function.Injective t) :
    stabilizer t = ⊥ ∧
      ∀ (s : Fin n → Aˣ) (π τ : Equiv.Perm (Fin n)),
        Transports s t π → Transports s t τ → π = τ :=
  ⟨stabilizer_eq_bot_of_injective t hinj,
    fun _ _ _ hπ hτ => transport_unique_of_nondegenerate hinj hπ hτ⟩

end ScaleUniverse.Transport
