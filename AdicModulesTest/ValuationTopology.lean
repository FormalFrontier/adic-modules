/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules

set_option warningAsError true

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

noncomputable section

universe u v w

#check Valuation.exists_pow_restrict_lt_of_isHausdorff
#check ValuationRing.radical_span_singleton_le_prime_of_isHausdorff
#check ValuationRing.exists_pow_valuation_lt_of_isHausdorff
#check ValuationRing.isAdic_valuationTopology_span_singleton

section Generic

variable {R : Type u} {Γ₀ : Type w} [CommRing R]
  [LinearOrderedCommGroupWithZero Γ₀]

private theorem genericPowerCofinalityClient (ν : Valuation R Γ₀)
    (hspan : ∀ x y : R, x ∈ Ideal.span {y} ↔ ν x ≤ ν y)
    {a : R} [IsHausdorff (Ideal.span {a}) R]
    (γ : (ValueGroup₀ (.ofClass ν))ˣ) :
    ∃ n : ℕ, ν.restrict a ^ n < γ.1 :=
  ν.exists_pow_restrict_lt_of_isHausdorff hspan γ

end Generic

section ValuationRing

variable {V : Type u} {K : Type v} [CommRing V] [IsDomain V]
  [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

private theorem nonzeroPrimeRadicalClient {a : V} [IsHausdorff (Ideal.span {a}) V]
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) :
    (Ideal.span {a}).radical ≤ p :=
  ValuationRing.radical_span_singleton_le_prime_of_isHausdorff p hp

private theorem valuationPowerCofinalityClient {a : V} [IsHausdorff (Ideal.span {a}) V]
    (γ : (ValueGroup₀ (.ofClass
      ((ValuationRing.valuation V K).comap (algebraMap V K))))ˣ) :
    ∃ n : ℕ,
      ((ValuationRing.valuation V K).comap (algebraMap V K)).restrict a ^ n < γ.1 :=
  ValuationRing.exists_pow_valuation_lt_of_isHausdorff γ

private theorem adicTopologyClient {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    @IsAdic V _
      (Valued.mk' ((ValuationRing.valuation V K).comap
        (algebraMap V K))).toUniformSpace.toTopologicalSpace
      (Ideal.span {a}) :=
  ValuationRing.isAdic_valuationTopology_span_singleton ha0

end ValuationRing
