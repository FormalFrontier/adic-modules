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

#check ValuationRing.localizedAdicCompletionResidueFieldEquiv
#check ValuationRing.localizedAdicCompletionResidueFieldEquiv_residue

namespace ValuationRing

variable {V : Type u} {Vₛ : Type v} {K : Type w}
  [CommRing V] [IsDomain V] [ValuationRing V]
  [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K]
  (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K]
  {a : V} (ha0 : a ≠ 0)
  (hSrad : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
  [IsHausdorff (Ideal.span {a}) V]

private noncomputable def residueEquivalenceClient :
    let hS0 : (0 : V) ∉ S := fun h0 ↦
      Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
    let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
    letI : IsDomain Vₛ := IsLocalization.isDomain_of_le_nonZeroDivisors Vₛ hSnzd
    letI : ValuationRing Vₛ := localization_isValuationRing (Vₛ := Vₛ) S hSnzd
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    IsLocalRing.ResidueField Vₛ ≃+*
      IsLocalRing.ResidueField
        (localizedAdicCompletionValuationSubring (Vₛ := Vₛ) (K := K)
          S ha0 hSrad) :=
  localizedAdicCompletionResidueFieldEquiv (Vₛ := Vₛ) (K := K)
    S ha0 hSrad

private theorem residueMapClient (x : Vₛ) :
    let hS0 : (0 : V) ∉ S := fun h0 ↦
      Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
    let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
    letI : IsDomain Vₛ := IsLocalization.isDomain_of_le_nonZeroDivisors Vₛ hSnzd
    letI : ValuationRing Vₛ := localization_isValuationRing (Vₛ := Vₛ) S hSnzd
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    localizedAdicCompletionResidueFieldEquiv (Vₛ := Vₛ) (K := K)
        S ha0 hSrad (IsLocalRing.residue Vₛ x) =
      IsLocalRing.residue
        (localizedAdicCompletionValuationSubring (Vₛ := Vₛ) (K := K)
          S ha0 hSrad)
        (localizedAdicCompletionValuationSubringEquiv (Vₛ := Vₛ) (K := K)
          S ha0 hSrad
          (algebraMap Vₛ (AdicCompletion
            (Ideal.span {algebraMap V Vₛ a}) Vₛ) x)) :=
  localizedAdicCompletionResidueFieldEquiv_residue (Vₛ := Vₛ) (K := K)
    S ha0 hSrad x

end ValuationRing
