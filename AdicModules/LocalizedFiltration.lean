/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import AdicModules.ValuationTopology

/-!
# Principal-adic filtrations after localizing a valuation ring

This file compares the powers of a principal ideal in a localization with the literal images of
the corresponding powers from the base valuation ring.  The image is deliberately a submodule
over the base ring, not the extended ideal in the localization.
-/

@[expose] public section

noncomputable section

universe u v

namespace ValuationRing

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  (S : Submonoid V) (Vₛ : Type v) [CommRing Vₛ] [Algebra V Vₛ] [IsLocalization S Vₛ]

/-- The literal image of `(a ^ n)` from the base ring in a localization.  Unlike `Ideal.map`,
this remembers only base-ring multiples. -/
def localizedPowerImage (a : V) (n : ℕ) : Submodule V Vₛ :=
  Submodule.map (Algebra.linearMap V Vₛ) ((Ideal.span {a}) ^ n)

/-- A denominator disjoint from the radical of `(a)` divides `a` in a valuation ring. -/
lemma denominator_dvd_of_not_mem_radical {a : V}
    (hS : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    (s : S) : (s : V) ∣ a := by
  rcases dvd_total a (s : V) with has | hsa
  · exact (Set.disjoint_left.1 hS s.2
      (Ideal.le_radical ((Ideal.mem_span_singleton).2 has))).elim
  · exact hsa

/-- Multiplying an arbitrary localized element by `a ^ (n + 1)` lands in the literal image of
`a ^ n V`.  This is the substantive inclusion in the localized-filtration comparison. -/
lemma pow_succ_mul_mem_localizedPowerImage {a : V}
    (hS : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    (n : ℕ) (x : Vₛ) :
    algebraMap V Vₛ a ^ (n + 1) * x ∈
      localizedPowerImage (V := V) (Vₛ := Vₛ) a n := by
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
  obtain ⟨c, hc⟩ := denominator_dvd_of_not_mem_radical (V := V) S hS s
  refine ⟨a ^ n * c * r, ?_, ?_⟩
  · rw [Ideal.span_singleton_pow]
    change a ^ n * c * r ∈ (Ideal.span {a ^ n} : Ideal V)
    exact (Ideal.mem_span_singleton).2 ⟨c * r, by ring⟩
  · change algebraMap V Vₛ (a ^ n * c * r) =
      algebraMap V Vₛ a ^ (n + 1) * IsLocalization.mk' Vₛ r s
    calc
      algebraMap V Vₛ (a ^ n * c * r) =
          IsLocalization.mk' Vₛ (a ^ (n + 1) * r) s := by
        apply IsLocalization.eq_mk'_of_mul_eq
        rw [hc]
        ring
      _ = algebraMap V Vₛ (a ^ (n + 1)) * IsLocalization.mk' Vₛ r s :=
        (IsLocalization.mul_mk'_eq_mk'_of_mul (a ^ (n + 1)) r s).symm
      _ = algebraMap V Vₛ a ^ (n + 1) * IsLocalization.mk' Vₛ r s := by
        rw [map_pow]

/-- The powers of the extended principal ideal sandwich the literal images of the base powers. -/
theorem localizedPowerImage_sandwich {a : V}
    (hS : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V)) (n : ℕ) :
    ((Ideal.span {algebraMap V Vₛ a}) ^ (n + 1)).restrictScalars V ≤
        localizedPowerImage (V := V) (Vₛ := Vₛ) a n ∧
      localizedPowerImage (V := V) (Vₛ := Vₛ) a n ≤
        ((Ideal.span {algebraMap V Vₛ a}) ^ n).restrictScalars V := by
  constructor
  · intro x hx
    change x ∈ (Ideal.span {algebraMap V Vₛ a}) ^ (n + 1) at hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    exact pow_succ_mul_mem_localizedPowerImage S Vₛ hS n y
  · rintro x ⟨y, hy, rfl⟩
    change algebraMap V Vₛ y ∈ (Ideal.span {algebraMap V Vₛ a}) ^ n
    rw [Ideal.span_singleton_pow] at hy ⊢
    change y ∈ (Ideal.span {a ^ n} : Ideal V) at hy
    obtain ⟨z, hz⟩ := (Ideal.mem_span_singleton).1 hy
    apply (Ideal.mem_span_singleton).2
    refine ⟨algebraMap V Vₛ z, ?_⟩
    rw [← map_pow, ← map_mul, hz]

/-- In the adic topology of the localized principal ideal, the literal images of `a ^ n V`
form a neighborhood basis at zero. -/
theorem hasBasis_nhds_zero_adic_localizedPowerImage {a : V}
    (hS : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V)) :
    Filter.HasBasis
      (@nhds Vₛ (Ideal.span {algebraMap V Vₛ a}).adicTopology (0 : Vₛ))
      (fun _n : ℕ ↦ True)
      (fun n ↦ (localizedPowerImage (V := V) (Vₛ := Vₛ) a n : Set Vₛ)) := by
  apply (Ideal.hasBasis_nhds_zero_adic
    (Ideal.span {algebraMap V Vₛ a})).to_hasBasis
  · intro n _
    refine ⟨n, trivial, ?_⟩
    intro x hx
    exact (localizedPowerImage_sandwich S Vₛ hS n).2 hx
  · intro n _
    refine ⟨n + 1, trivial, ?_⟩
    intro x hx
    exact (localizedPowerImage_sandwich S Vₛ hS n).1 hx

/-- Separatedness for a principal-adic filtration passes to any localization whose denominators
are disjoint from the radical of the principal ideal. -/
theorem isHausdorff_localization_span_singleton {a : V}
    (hS : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    [IsHausdorff (Ideal.span {a}) V] :
    IsHausdorff (Ideal.span {algebraMap V Vₛ a}) Vₛ := by
  have hS0 : (0 : V) ∉ S := by
    intro h0
    exact Set.disjoint_left.1 hS h0 (Ideal.zero_mem _)
  have hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
  have hinj : Function.Injective (algebraMap V Vₛ) := IsLocalization.injective Vₛ hSnzd
  refine ⟨fun x hx ↦ ?_⟩
  have hxpow (n : ℕ) : x ∈ (Ideal.span {algebraMap V Vₛ a}) ^ n := by
    simpa only [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hx n
  have hximage (n : ℕ) :
      x ∈ localizedPowerImage (V := V) (Vₛ := Vₛ) a n :=
    (localizedPowerImage_sandwich S Vₛ hS n).1 (hxpow (n + 1))
  obtain ⟨y, hy, hyx⟩ := hximage 0
  have hyall (n : ℕ) : y ∈ (Ideal.span {a}) ^ n := by
    obtain ⟨z, hz, hzx⟩ := hximage n
    have hzy : z = y := hinj (hzx.trans hyx.symm)
    exact hzy ▸ hz
  have hy0 : y = 0 := IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) V) y
    (fun n ↦ by
      rw [SModEq.zero]
      simpa only [smul_eq_mul, Ideal.mul_top] using hyall n)
  rw [← hyx, hy0, map_zero]

/-- The separatedness consequence specialized to an arbitrary model of localization at a prime
containing the radical of `(a)`. -/
theorem isHausdorff_localizationAtPrime_span_singleton
    (p : Ideal V) [p.IsPrime] (Vₚ : Type v) [CommRing Vₚ] [Algebra V Vₚ]
    [IsLocalization p.primeCompl Vₚ] {a : V} (ha : (Ideal.span {a}).radical ≤ p)
    [IsHausdorff (Ideal.span {a}) V] :
    IsHausdorff (Ideal.span {algebraMap V Vₚ a}) Vₚ := by
  apply isHausdorff_localization_span_singleton p.primeCompl Vₚ
  rw [Set.disjoint_left]
  intro x hxp hxa
  exact (Ideal.mem_primeCompl_iff.mp hxp) (ha hxa)

/-- Principal-adic separatedness passes to localization at every nonzero prime of a
valuation domain. The required containment of the principal radical follows automatically
from separatedness. -/
theorem isHausdorff_localizationAtNonzeroPrime_span_singleton
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    (Vₚ : Type v) [CommRing Vₚ] [Algebra V Vₚ] [IsLocalization p.primeCompl Vₚ]
    {a : V} [IsHausdorff (Ideal.span {a}) V] :
    IsHausdorff (Ideal.span {algebraMap V Vₚ a}) Vₚ := by
  apply isHausdorff_localizationAtPrime_span_singleton p Vₚ
  exact radical_span_singleton_le_prime_of_isHausdorff p hp

end ValuationRing
