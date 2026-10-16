/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules
public import Mathlib.Algebra.Field.Rat
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.NormNum

/-!
# Power images and separatedness in localizations

The images of base-ring powers lie between consecutive powers of the extended principal ideal
and form an adic neighborhood basis. Separatedness passes to localizations away from the
principal radical, including localizations at nonzero primes.

For `PowerSeries ℚ`, localization at all units is the identity localization. The public
representative theorem gives a nonzero representative of `X * C 3` in this model.

The proofs reuse Mathlib's power-series domain and prime-ideal results and the localized
filtration API of AdicModules.

## References

The identity-localization model uses Mathlib's power-series domain, prime-ideal
and unit-localization facts, together with the base-power sandwich,
separatedness and denominator-clearing representative method of
`AdicModules.LocalizedFiltration`.
-/

set_option warningAsError true

noncomputable section

universe u v

namespace ValuationRing

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  (S : Submonoid V) (Vₛ : Type v) [CommRing Vₛ] [Algebra V Vₛ] [IsLocalization S Vₛ]
  {a : V} (hS : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))

include hS in
private theorem powerSandwichClient (n : ℕ) :
    ((Ideal.span {algebraMap V Vₛ a}) ^ (n + 1)).restrictScalars V ≤
        localizedPowerImage (Vₛ := Vₛ) a n ∧
      localizedPowerImage (Vₛ := Vₛ) a n ≤
        ((Ideal.span {algebraMap V Vₛ a}) ^ n).restrictScalars V :=
  localizedPowerImage_sandwich S Vₛ hS n

include hS in
private theorem neighborhoodBasisClient :
    Filter.HasBasis
      (@nhds Vₛ (Ideal.span {algebraMap V Vₛ a}).adicTopology (0 : Vₛ))
      (fun _n : ℕ ↦ True)
      (fun n ↦ (localizedPowerImage (Vₛ := Vₛ) a n : Set Vₛ)) :=
  hasBasis_nhds_zero_adic_localizedPowerImage S Vₛ hS

include hS in
private theorem separatedLocalizationClient [IsHausdorff (Ideal.span {a}) V] :
    IsHausdorff (Ideal.span {algebraMap V Vₛ a}) Vₛ :=
  isHausdorff_localization_span_singleton S Vₛ hS

private theorem separatedPrimeLocalizationClient (p : Ideal V) [p.IsPrime]
    (Vₚ : Type v) [CommRing Vₚ] [Algebra V Vₚ]
    [IsLocalization p.primeCompl Vₚ] (ha : (Ideal.span {a}).radical ≤ p)
    [IsHausdorff (Ideal.span {a}) V] :
    IsHausdorff (Ideal.span {algebraMap V Vₚ a}) Vₚ :=
  isHausdorff_localizationAtPrime_span_singleton p Vₚ ha

private theorem separatedNonzeroPrimeLocalizationClient (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    (Vₚ : Type v) [CommRing Vₚ] [Algebra V Vₚ] [IsLocalization p.primeCompl Vₚ]
    [IsHausdorff (Ideal.span {a}) V] :
    IsHausdorff (Ideal.span {algebraMap V Vₚ a}) Vₚ :=
  isHausdorff_localizationAtNonzeroPrime_span_singleton p hp Vₚ

/-- Localization at all units gives the identity-localization model for a generator in the
maximal ideal; the denominator-disjointness premise is satisfied. -/
private theorem unitsLocalizationClient (ha : a ∈ IsLocalRing.maximalIdeal V) (x : V) :
    ∃ y : V, algebraMap V V y = algebraMap V V a * x := by
  have hle : (Ideal.span {a}).radical ≤ IsLocalRing.maximalIdeal V :=
    (Ideal.IsPrime.radical_le_iff
      (inferInstance : (IsLocalRing.maximalIdeal V).IsPrime)).2
      ((Ideal.span_singleton_le_iff_mem _).2 ha)
  have hUnits : Disjoint (IsUnit.submonoid V : Set V)
      ((Ideal.span {a}).radical : Set V) := by
    rw [Set.disjoint_left]
    intro s hs hr
    have hnot : ¬ IsUnit s := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hle hr
    exact hnot hs
  exact exists_algebraMap_eq_mul (IsUnit.submonoid V) V hUnits x

end ValuationRing

namespace ValuationRing

/-- In the units localization of `PowerSeries ℚ`, the localized-filtration representative of
`X * C 3` is nonzero. -/
public theorem powerSeries_unitsLocalization_exists_ne_zero_X_mul_three :
    ∃ y : PowerSeries ℚ, y ≠ 0 ∧
      algebraMap (PowerSeries ℚ) (PowerSeries ℚ) y =
        algebraMap (PowerSeries ℚ) (PowerSeries ℚ) PowerSeries.X *
          algebraMap (PowerSeries ℚ) (PowerSeries ℚ) (PowerSeries.C (3 : ℚ)) := by
  have hUnits : Disjoint (IsUnit.submonoid (PowerSeries ℚ) : Set (PowerSeries ℚ))
      ((Ideal.span {(PowerSeries.X : PowerSeries ℚ)}).radical : Set (PowerSeries ℚ)) := by
    rw [Set.disjoint_left]
    intro s hs hr
    have hnot : ¬ IsUnit s := by
      simpa only [← PowerSeries.maximalIdeal_eq_span_X (k := ℚ),
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using
        (PowerSeries.span_X_isPrime (R := ℚ)).isRadical hr
    exact hnot hs
  obtain ⟨y, hy⟩ := exists_algebraMap_eq_mul (a := PowerSeries.X)
    (IsUnit.submonoid (PowerSeries ℚ)) (PowerSeries ℚ) hUnits
    (algebraMap (PowerSeries ℚ) (PowerSeries ℚ) (PowerSeries.C (3 : ℚ)))
  have hC : PowerSeries.C (3 : ℚ) ≠ (0 : PowerSeries ℚ) := by
    simpa only [map_zero] using
      (PowerSeries.C_injective (R := ℚ)).ne (by norm_num : (3 : ℚ) ≠ 0)
  refine ⟨y, ?_, hy⟩
  intro hy0
  have hprod : (PowerSeries.X : PowerSeries ℚ) * PowerSeries.C (3 : ℚ) = 0 := by
    simpa only [Algebra.algebraMap_self, RingHom.id_apply, hy0] using hy.symm
  exact (mul_ne_zero (PowerSeries.X_ne_zero (R := ℚ)) hC) hprod

end ValuationRing
