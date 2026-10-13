/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The composite presentation of completed valuation integers

Inside the common completed fraction field, the valuation integers are the composite of the
completed localization at a nonzero prime and the transported quotient valuation ring. The
inverse quotient formula sends the residue of a completed valuation integer back to its
quotient class, using the characteristic API of the residue map and ring equivalence.

For `ℚ[[X]]` at its maximal ideal `(X)`, the completed composite residues of zero and one
have distinct inverse images under the quotient comparison. The inverse image of the residue
of one is its canonical quotient class.

The proofs use the completed-composite APIs of AdicModules and Mathlib.
-/

open scoped Topology

noncomputable section

universe u v

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

namespace ValuationRing

/-- In the completed composite for rational power series at `(X)`, the inverse quotient
comparison distinguishes the residues of zero and one and recovers the quotient class of one. -/
public theorem powerSeries_completionIntegersQuotient_zero_one :
    let p := IsLocalRing.maximalIdeal (PowerSeries ℚ)
    let hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field (PowerSeries ℚ)
    let hSep : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) :=
      Eq.mp
        (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ IsHausdorff I (PowerSeries ℚ))
          (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
        (inferInstance :
          IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ))
    let q := @completionIntegersQuotientEquiv
      (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
      p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep
    let r := @completionIntegersCompositeResidue
      (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
      p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep
    let J := @completionIntegersLocalizedPrime
      (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
      p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep
    q.symm (r (0 : CompletionIntegers (PowerSeries ℚ)
        (FractionRing (PowerSeries ℚ)))) ≠ q.symm (r 1) ∧
      q.symm (r 1) = Ideal.Quotient.mk J 1 := by
  let p := IsLocalRing.maximalIdeal (PowerSeries ℚ)
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field (PowerSeries ℚ)
  let hSep : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) :=
    Eq.mp
      (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ IsHausdorff I (PowerSeries ℚ))
        (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
      (inferInstance :
        IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ))
  let q := @completionIntegersQuotientEquiv
    (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
    p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep
  let r := @completionIntegersCompositeResidue
    (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
    p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep
  let J := @completionIntegersLocalizedPrime
    (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
    p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep
  let W := @localizedAtPrimeQuotientValuationSubring
    (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
    p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep
  change q.symm (r (0 : CompletionIntegers (PowerSeries ℚ)
      (FractionRing (PowerSeries ℚ)))) ≠ q.symm (r 1) ∧
    q.symm (r 1) = Ideal.Quotient.mk J 1
  constructor
  · intro h
    have hr : r 0 = r 1 := q.symm.injective h
    exact (zero_ne_one : (0 : W) ≠ 1) ((r.map_zero).symm.trans (hr.trans r.map_one))
  · exact @completionIntegersQuotientEquiv_symm_residue
      (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
      p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep
      (1 : CompletionIntegers (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)))

end ValuationRing
