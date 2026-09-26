/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules

set_option warningAsError true

noncomputable section

universe u v

#check ValuationRing.localizedPowerImage
#check ValuationRing.denominator_dvd_of_not_mem_radical
#check ValuationRing.pow_succ_mul_mem_localizedPowerImage
#check ValuationRing.localizedPowerImage_sandwich
#check ValuationRing.hasBasis_nhds_zero_adic_localizedPowerImage
#check ValuationRing.isHausdorff_localization_span_singleton
#check ValuationRing.isHausdorff_localizationAtPrime_span_singleton
#check ValuationRing.isHausdorff_localizationAtNonzeroPrime_span_singleton

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

private theorem separatedPrimeLocalizationClient (p : Ideal V) [p.IsPrime] (Vₚ : Type v) [CommRing Vₚ] [Algebra V Vₚ]
    [IsLocalization p.primeCompl Vₚ] (ha : (Ideal.span {a}).radical ≤ p)
    [IsHausdorff (Ideal.span {a}) V] :
    IsHausdorff (Ideal.span {algebraMap V Vₚ a}) Vₚ :=
  isHausdorff_localizationAtPrime_span_singleton p Vₚ ha

private theorem separatedNonzeroPrimeLocalizationClient (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    (Vₚ : Type v) [CommRing Vₚ] [Algebra V Vₚ] [IsLocalization p.primeCompl Vₚ]
    [IsHausdorff (Ideal.span {a}) V] :
    IsHausdorff (Ideal.span {algebraMap V Vₚ a}) Vₚ :=
  isHausdorff_localizationAtNonzeroPrime_span_singleton p hp Vₚ

end ValuationRing
