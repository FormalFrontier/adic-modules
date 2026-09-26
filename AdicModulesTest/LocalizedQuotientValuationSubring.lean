/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules

open scoped Topology

noncomputable section

universe u v

#check ValuationRing.primeCompl_disjoint_radical_span_singleton_of_isHausdorff
#check ValuationRing.localizedAtPrimeQuotientValuationSubring
#check ValuationRing.mem_localizedAtPrimeQuotientValuationSubring
#check ValuationRing.localizedAtPrimeQuotientValuationSubring_algebraMap_mem

namespace ValuationRing

variable {V : Type u} {K : Type v}
  [CommRing V] [IsDomain V] [ValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

private theorem quotientImageMembershipClient (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V]
    (x : V ⧸ p) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let hDisj := primeCompl_disjoint_radical_span_singleton_of_isHausdorff p hp
    let A := localizedAdicCompletionValuationSubring
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
    let e : p.ResidueField ≃+* IsLocalRing.ResidueField A :=
      localizedAdicCompletionResidueFieldEquiv
        (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
    e (algebraMap (V ⧸ p) p.ResidueField x) ∈
      localizedAtPrimeQuotientValuationSubring (K := K) p hp ha0 :=
  localizedAtPrimeQuotientValuationSubring_algebraMap_mem p hp ha0 x

end ValuationRing
