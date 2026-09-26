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

#check ValuationRing.localization_isValuationRing
#check ValuationRing.localizedAdicCompletionValuationSubring
#check ValuationRing.localizedAdicCompletionValuationSubringEquiv
#check ValuationRing.coe_localizedAdicCompletionValuationSubringEquiv_apply

namespace ValuationRing

variable {V : Type u} {Vₛ : Type v} {K : Type w}
  [CommRing V] [IsDomain V] [ValuationRing V]
  [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K]
  (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K]
  {a : V} (ha0 : a ≠ 0)
  (hS : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
  [IsHausdorff (Ideal.span {a}) V]

private noncomputable def valuationSubringEquivalenceClient :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ ≃+*
      localizedAdicCompletionValuationSubring (Vₛ := Vₛ) (K := K) S ha0 hS :=
  localizedAdicCompletionValuationSubringEquiv (Vₛ := Vₛ) (K := K) S ha0 hS

private theorem embeddingClient (x : AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    ((localizedAdicCompletionValuationSubringEquiv (Vₛ := Vₛ) (K := K)
        S ha0 hS x :
      localizedAdicCompletionValuationSubring (Vₛ := Vₛ) (K := K) S ha0 hS) :
        UniformSpace.Completion K) =
      localizedAdicCompletionToFractionFieldCompletion (Vₛ := Vₛ) (K := K)
        S ha0 hS x :=
  coe_localizedAdicCompletionValuationSubringEquiv_apply
    (Vₛ := Vₛ) (K := K) S ha0 hS x

end ValuationRing
