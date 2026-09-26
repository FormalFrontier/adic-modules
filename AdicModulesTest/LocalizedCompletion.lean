/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules

set_option warningAsError true
set_option linter.style.haveILetI false

open scoped Topology

noncomputable section

universe u v w

#check ValuationRing.isUniformInducing_mapToFractionRing
#check ValuationRing.localizedAdicCompletionToFractionFieldCompletion
#check ValuationRing.localizedAdicCompletionToFractionFieldCompletion_algebraMap
#check ValuationRing.localizedAdicCompletionToFractionFieldCompletion_algebraMap_base
#check ValuationRing.localizedAdicCompletionToFractionFieldCompletion_injective
#check ValuationRing.completionIntegers_mem_range_localizedAdicCompletion
#check ValuationRing.localizedAdicCompletionFractionFieldAlgebra
#check ValuationRing.localizedAdicCompletion_isFractionRing

namespace ValuationRing

variable {V : Type u} {Vₛ : Type v} {K : Type w}
  [CommRing V] [IsDomain V] [ValuationRing V]
  [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K]
  (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K]
  {a : V} (ha0 : a ≠ 0)
  (hS : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
  [IsHausdorff (Ideal.span {a}) V]

include ha0 in
private theorem inducedUniformityClient :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    letI : WithIdeal Vₛ := ⟨Ideal.span {algebraMap V Vₛ a}⟩
    IsUniformInducing (Localization.mapToFractionRing K S Vₛ
      (le_nonZeroDivisors_of_noZeroDivisors (fun h0 ↦
        Set.disjoint_left.1 hS h0 (Ideal.zero_mem _)))) :=
  isUniformInducing_mapToFractionRing (K := K) S ha0 hS

private theorem completionInjectivityClient :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    Function.Injective
      (localizedAdicCompletionToFractionFieldCompletion (Vₛ := Vₛ) (K := K)
        S ha0 hS) :=
  localizedAdicCompletionToFractionFieldCompletion_injective
    (Vₛ := Vₛ) (K := K) S ha0 hS

private theorem baseMapClient (x : V) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    localizedAdicCompletionToFractionFieldCompletion (K := K) S ha0 hS
        (algebraMap Vₛ (AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ)
          (algebraMap V Vₛ x)) =
      algebraMap K (UniformSpace.Completion K) (algebraMap V K x) :=
  localizedAdicCompletionToFractionFieldCompletion_algebraMap_base
    (K := K) S ha0 hS x

private theorem fractionFieldClient :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    letI : Algebra (AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ)
        (UniformSpace.Completion K) :=
      localizedAdicCompletionFractionFieldAlgebra (K := K) S ha0 hS
    IsFractionRing (AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ)
      (UniformSpace.Completion K) :=
  localizedAdicCompletion_isFractionRing (K := K) S ha0 hS

end ValuationRing
