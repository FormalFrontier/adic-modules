/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules

set_option warningAsError true

noncomputable section

open scoped Topology

universe u v

#check ValuationRing.completionIntegers_exists_associated_algebraMap
#check ValuationRing.principalAdicCompletion_exists_associated_algebraMap
#check ValuationRing.principalAdicCompletion_map_comap_eq
#check ValuationRing.principalAdicCompletion_faithfullyFlat
#check ValuationRing.principalAdicCompletion_extensionValuation_isEquiv
#check ValuationRing.principalAdicCompletionPrimeSpectrumOrderIso
#check ValuationRing.principalAdicCompletion_primeHeight_comap

namespace ValuationRing

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

private theorem associatedIntegerClient (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (z : CompletionIntegers V K) :
    ∃ x : V, Associated (algebraMap V (CompletionIntegers V K) x) z :=
  completionIntegers_exists_associated_algebraMap z

variable (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
  (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
  [IsHausdorff (Ideal.span {a}) V]

include K ha0 in
private theorem associatedCompletionClient (z : AdicCompletion (Ideal.span {a}) V) :
    ∃ x : V, Associated
      (algebraMap V (AdicCompletion (Ideal.span {a}) V) x) z :=
  principalAdicCompletion_exists_associated_algebraMap K a ha0 z

include K ha0 in
private theorem idealMapComapClient (J : Ideal (AdicCompletion (Ideal.span {a}) V)) :
    Ideal.map (algebraMap V (AdicCompletion (Ideal.span {a}) V))
        (Ideal.comap (algebraMap V (AdicCompletion (Ideal.span {a}) V)) J) = J :=
  principalAdicCompletion_map_comap_eq K a ha0 J

include K ha0 ha in
private theorem faithfulFlatnessClient :
    letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isValuationRing K a ha0
    Module.FaithfullyFlat V (AdicCompletion (Ideal.span {a}) V) :=
  principalAdicCompletion_faithfullyFlat K a ha0 ha

private theorem spectrumMapReductionClient (P : PrimeSpectrum (AdicCompletion (Ideal.span {a}) V)) :
    principalAdicCompletionPrimeSpectrumOrderIso K a ha0 ha P =
      PrimeSpectrum.comap
        (algebraMap V (AdicCompletion (Ideal.span {a}) V)) P := rfl

include K ha0 ha in
private theorem heightClient (P : PrimeSpectrum (AdicCompletion (Ideal.span {a}) V)) :
    Order.height
        (PrimeSpectrum.comap
          (algebraMap V (AdicCompletion (Ideal.span {a}) V)) P) =
      Order.height P :=
  principalAdicCompletion_primeHeight_comap K a ha0 ha P

private noncomputable def valueGroupEquivalenceClient :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let A := AdicCompletion (Ideal.span {a}) V
    letI : IsDomain A := principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing A := principalAdicCompletion_isValuationRing K a ha0
    letI : Algebra A (UniformSpace.Completion K) :=
      principalAdicCompletionFractionFieldAlgebra a ha0
    letI : IsFractionRing A (UniformSpace.Completion K) :=
      principalAdicCompletion_isFractionRing a ha0
    MonoidWithZeroHom.ValueGroup₀ (.ofClass
        (Valued.v : Valuation (UniformSpace.Completion K) (ValueGroup V K))) ≃*o
      MonoidWithZeroHom.ValueGroup₀
        (.ofClass (valuation A (UniformSpace.Completion K))) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let A := AdicCompletion (Ideal.span {a}) V
  letI : IsDomain A := principalAdicCompletion_isDomain K a ha0
  letI : ValuationRing A := principalAdicCompletion_isValuationRing K a ha0
  letI : Algebra A (UniformSpace.Completion K) :=
    principalAdicCompletionFractionFieldAlgebra a ha0
  letI : IsFractionRing A (UniformSpace.Completion K) :=
    principalAdicCompletion_isFractionRing a ha0
  exact (principalAdicCompletion_extensionValuation_isEquiv K a ha0).orderMonoidIso

end ValuationRing
