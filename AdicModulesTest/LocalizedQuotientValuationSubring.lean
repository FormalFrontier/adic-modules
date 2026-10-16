/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Quotient-ring elements in a completed-localization residue field

The residue-field equivalence of a completed localization transports the image of every
quotient-ring element into the quotient valuation subring. This provides elements of that
subring through the canonical algebra map, rather than by unfolding its comap construction.
The inverse residue-field equivalence recovers the original image from this subtype lift.

For `ℚ[[X]]` at its maximal ideal `(X)`, zero and one give canonical subtype lifts into the
transported valuation subring. The round-trip formula recovers both base images, and the
fraction-field embedding of the quotient distinguishes the lifts.

The proof uses the localized residue-field and valuation-subring APIs of AdicModules and Mathlib.

## References

These clients use the inverse residue transport and subtype-lift formulas of
`AdicModules.LocalizedQuotientValuationSubring`, with Mathlib's rational
power-series DVR, quotient and fraction-field embedding APIs for the distinct
residue inputs.
-/

open scoped Topology

noncomputable section

universe u v

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

namespace ValuationRing

/-- The quotient classes zero and one of rational power series at `(X)` give distinct
canonical lifts into the completed-localization quotient valuation subring. The inverse
residue-field comparison recovers both original algebra-map images. -/
public theorem powerSeries_localizedQuotient_zero_one :
    let p := IsLocalRing.maximalIdeal (PowerSeries ℚ)
    let hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field (PowerSeries ℚ)
    let hSep : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) :=
      Eq.mp
        (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ IsHausdorff I (PowerSeries ℚ))
          (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
        (inferInstance :
          IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ))
    let hDisj := @primeCompl_disjoint_radical_span_singleton_of_isHausdorff
      (PowerSeries ℚ) _ _ _ p _ hp PowerSeries.X hSep
    let e := @localizedAdicCompletionResidueFieldEquiv
      (PowerSeries ℚ) (Localization.AtPrime p) (FractionRing (PowerSeries ℚ))
      _ _ _ _ _ _ _ p.primeCompl _ _
      PowerSeries.X PowerSeries.X_ne_zero hDisj hSep
    let W := @localizedAtPrimeQuotientValuationSubring
      (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
      p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep
    let z₀ : W :=
      ⟨e (algebraMap ((PowerSeries ℚ) ⧸ p) p.ResidueField 0),
        @localizedAtPrimeQuotientValuationSubring_algebraMap_mem
          (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
          p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep 0⟩
    let z₁ : W :=
      ⟨e (algebraMap ((PowerSeries ℚ) ⧸ p) p.ResidueField 1),
        @localizedAtPrimeQuotientValuationSubring_algebraMap_mem
          (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
          p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep 1⟩
    e.symm z₀.val = algebraMap ((PowerSeries ℚ) ⧸ p) p.ResidueField 0 ∧
      e.symm z₁.val = algebraMap ((PowerSeries ℚ) ⧸ p) p.ResidueField 1 ∧
      z₀ ≠ z₁ := by
  let p := IsLocalRing.maximalIdeal (PowerSeries ℚ)
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field (PowerSeries ℚ)
  let hSep : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) :=
    Eq.mp
      (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ IsHausdorff I (PowerSeries ℚ))
        (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
      (inferInstance :
        IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ))
  let hDisj := @primeCompl_disjoint_radical_span_singleton_of_isHausdorff
    (PowerSeries ℚ) _ _ _ p _ hp PowerSeries.X hSep
  let e := @localizedAdicCompletionResidueFieldEquiv
    (PowerSeries ℚ) (Localization.AtPrime p) (FractionRing (PowerSeries ℚ))
    _ _ _ _ _ _ _ p.primeCompl _ _
    PowerSeries.X PowerSeries.X_ne_zero hDisj hSep
  let W := @localizedAtPrimeQuotientValuationSubring
    (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
    p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep
  let z₀ : W :=
    ⟨e (algebraMap ((PowerSeries ℚ) ⧸ p) p.ResidueField 0),
      @localizedAtPrimeQuotientValuationSubring_algebraMap_mem
        (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
        p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep 0⟩
  let z₁ : W :=
    ⟨e (algebraMap ((PowerSeries ℚ) ⧸ p) p.ResidueField 1),
      @localizedAtPrimeQuotientValuationSubring_algebraMap_mem
        (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
        p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep 1⟩
  change e.symm z₀.val = algebraMap ((PowerSeries ℚ) ⧸ p) p.ResidueField 0 ∧
    e.symm z₁.val = algebraMap ((PowerSeries ℚ) ⧸ p) p.ResidueField 1 ∧ z₀ ≠ z₁
  have h₀ : e.symm z₀.val = algebraMap ((PowerSeries ℚ) ⧸ p) p.ResidueField 0 :=
    @localizedAtPrimeQuotientValuationSubring_symm_coe_algebraMap
      (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
      p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep 0
  have h₁ : e.symm z₁.val = algebraMap ((PowerSeries ℚ) ⧸ p) p.ResidueField 1 :=
    @localizedAtPrimeQuotientValuationSubring_symm_coe_algebraMap
      (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
      p _ hp PowerSeries.X PowerSeries.X_ne_zero hSep 1
  refine ⟨h₀, h₁, ?_⟩
  intro h
  have hImages : algebraMap ((PowerSeries ℚ) ⧸ p) p.ResidueField 0 =
      algebraMap ((PowerSeries ℚ) ⧸ p) p.ResidueField 1 :=
    h₀.symm.trans ((congrArg (fun z : W ↦ e.symm z.val) h).trans h₁)
  have h01 : (0 : (PowerSeries ℚ) ⧸ p) = 1 :=
    IsFractionRing.injective ((PowerSeries ℚ) ⧸ p) p.ResidueField hImages
  exact zero_ne_one h01

end ValuationRing
