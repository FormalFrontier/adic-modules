/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules

open scoped Topology

noncomputable section

universe u v

#check ValuationRing.completionIntegers_algebraMap_isLocalHom
#check ValuationRing.completionIntegers_residueFieldMap_bijective
#check ValuationRing.completionIntegers_le_localizedAtPrime
#check ValuationRing.completionIntegersValuationSubring_eq_localizedAtPrime_composite
#check ValuationRing.completionIntegersLocalizedPrime
#check ValuationRing.completionIntegersLocalizedPrime_isPrime
#check ValuationRing.completionIntegers_ofPrime_localizedPrime
#check ValuationRing.completionIntegersCompositeResidue
#check ValuationRing.completionIntegersCompositeResidue_apply
#check ValuationRing.completionIntegersCompositeResidue_surjective
#check ValuationRing.ker_completionIntegersCompositeResidue
#check ValuationRing.completionIntegersQuotientEquiv
#check ValuationRing.completionIntegersQuotientEquiv_mk

namespace ValuationRing

variable {V : Type u} {K : Type v}
  [CommRing V] [IsDomain V] [ValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

private theorem completedCompositeClient (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let C := (Valued.v : Valuation (UniformSpace.Completion K)
      (ValueGroup V K)).valuationSubring
    let hDisj :=
      primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
    let A := localizedAdicCompletionValuationSubring
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
    let W := localizedAtPrimeQuotientValuationSubring (K := K) p hp ha0
    C = A.composite W :=
  completionIntegersValuationSubring_eq_localizedAtPrime_composite p hp ha0

private noncomputable def quotientEquivalenceClient (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let C := (Valued.v : Valuation (UniformSpace.Completion K)
      (ValueGroup V K)).valuationSubring
    let W := localizedAtPrimeQuotientValuationSubring (K := K) p hp ha0
    (C ⧸ completionIntegersLocalizedPrime (K := K) p hp ha0) ≃+* W :=
  completionIntegersQuotientEquiv p hp ha0

end ValuationRing
