/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules

set_option warningAsError true

noncomputable section

universe u v

#check ValuationRing.CompletionIntegers
#check ValuationRing.principalAdicCompletionEquiv
#check ValuationRing.principalAdicCompletionEquiv_algebraMap

section

variable {V : Type u} {K : Type v} [CommRing V] [IsDomain V]
  [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V]

/-- The comparison is usable with independent coefficient and fraction-field universes. -/
private noncomputable def completionEquivalenceClient :
    AdicCompletion (Ideal.span {a}) V ≃ₐ[V]
      ValuationRing.CompletionIntegers V K :=
  ValuationRing.principalAdicCompletionEquiv a ha0

/-- The comparison agrees with both canonical maps from the valuation ring. -/
private theorem canonicalMapClient (x : V) :
    ValuationRing.principalAdicCompletionEquiv (K := K) a ha0
        (algebraMap V (AdicCompletion (Ideal.span {a}) V) x) =
      algebraMap V (ValuationRing.CompletionIntegers V K) x := by
  simp

end
