/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Data.Set.Image
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Principal compression for powers of ideals

Powers commute with nonempty inclusion-directed suprema of ideals in a commutative semiring.
When each pair of elements of an ideal has a common divisor in that ideal, membership in its
`n`th power is equivalent to divisibility by the `n`th power of one element of the ideal.

In a commutative Bézout semiring, a generator of the finite pair-generated subideal supplies
this common divisor. The resulting characterization applies to arbitrary ideals, including
exponent zero, without a ring, domain, or finite-generation assumption on the ideal.
-/

@[expose] public section

universe u v

namespace Ideal

variable {R : Type u} [CommSemiring R]

/-- Taking the `n`th power commutes with the supremum of a nonempty inclusion-directed family
of ideals. -/
theorem iSup_pow_of_directed {ι : Sort v} [Nonempty ι] (f : ι → Ideal R)
    (hf : Directed (· ≤ ·) f) (n : ℕ) :
    (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  induction n with
  | zero => simp only [pow_zero, iSup_const]
  | succ n ih =>
    apply le_antisymm
    · rw [pow_succ, ih, Ideal.iSup_mul]
      refine iSup_le fun i => ?_
      rw [Ideal.mul_iSup]
      refine iSup_le fun j => ?_
      obtain ⟨k, hik, hjk⟩ := hf i j
      calc
        f i ^ n * f j ≤ f k ^ n * f k :=
          mul_le_mul' ((pow_left_mono n) hik) hjk
        _ = f k ^ (n + 1) := (pow_succ _ _).symm
        _ ≤ ⨆ l, f l ^ (n + 1) := le_iSup (fun l => f l ^ (n + 1)) k
    · exact iSup_le fun i => (pow_left_mono (n + 1)) (le_iSup f i)

/-- If any two elements of an ideal have a common divisor in the ideal, membership
in its `n`th power is equivalent to divisibility by the `n`th power of one of its elements. -/
theorem mem_pow_iff_exists_pow_dvd_of_directed (I : Ideal R)
    (hI : DirectedOn (fun a b : R => b ∣ a) (I : Set R)) (n : ℕ) (x : R) :
    x ∈ I ^ n ↔ ∃ t ∈ I, t ^ n ∣ x := by
  let _ : Nonempty I := ⟨⟨0, I.zero_mem⟩⟩
  have hrange : Set.range (fun t : I => (t : R)) = (I : Set R) :=
    Subtype.range_val
  have hspan : I = ⨆ t : I, span {(t : R)} := by
    simpa only [hrange, span_eq] using
      (span_range_eq_iSup (fun t : I => (t : R)))
  have hf : Directed (· ≤ ·) (fun t : I => span {(t : R)}) := by
    intro a b
    obtain ⟨t, ht, ha, hb⟩ := hI a a.property b b.property
    refine ⟨⟨t, ht⟩, ?_, ?_⟩
    · exact span_singleton_le_span_singleton.mpr ha
    · exact span_singleton_le_span_singleton.mpr hb
  have hfpow : Directed (· ≤ ·) (fun t : I => span {(t : R)} ^ n) := by
    intro a b
    obtain ⟨t, ha, hb⟩ := hf a b
    exact ⟨t, pow_left_mono n ha, pow_left_mono n hb⟩
  have hpow : I ^ n = ⨆ t : I, span {(t : R)} ^ n := by
    calc
      I ^ n = (⨆ t : I, span {(t : R)}) ^ n :=
        congrArg (fun J : Ideal R => J ^ n) hspan
      _ = ⨆ t : I, span {(t : R)} ^ n := iSup_pow_of_directed _ hf n
  rw [hpow, Submodule.mem_iSup_of_directed _ hfpow]
  simp only [span_singleton_pow, mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨(t : R), t.property, ht⟩
  · rintro ⟨t, ht, htx⟩
    exact ⟨⟨t, ht⟩, htx⟩

variable [IsBezout R]

private theorem directedOn_dvd_of_isBezout (I : Ideal R) :
    DirectedOn (fun a b : R => b ∣ a) (I : Set R) := by
  intro a ha b hb
  let J : Ideal R := Ideal.span ({a, b} : Set R)
  have hfg : J.FG := by
    classical
    exact ⟨{a, b}, by simp [J]⟩
  let _ : J.IsPrincipal := IsBezout.isPrincipal_of_FG J hfg
  have hJI : J ≤ I := by
    refine Ideal.span_le.mpr ?_
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact ha
    · exact hb
  refine ⟨Submodule.IsPrincipal.generator J,
    hJI (Submodule.IsPrincipal.generator_mem J), ?_, ?_⟩
  · exact (Submodule.IsPrincipal.mem_iff_generator_dvd J).mp
      (Ideal.subset_span (by simp))
  · exact (Submodule.IsPrincipal.mem_iff_generator_dvd J).mp
      (Ideal.subset_span (by simp))

/-- An element belongs to an ideal power in a commutative Bézout semiring if and
only if it is divisible by the corresponding power of some element of the ideal. -/
theorem mem_pow_iff_exists_pow_dvd (I : Ideal R) (n : ℕ) (x : R) :
    x ∈ I ^ n ↔ ∃ t ∈ I, t ^ n ∣ x :=
  mem_pow_iff_exists_pow_dvd_of_directed I (directedOn_dvd_of_isBezout I) n x

end Ideal
