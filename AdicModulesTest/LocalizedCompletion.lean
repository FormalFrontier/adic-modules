/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules
public import Mathlib.Algebra.Field.Rat
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Elements of localized completions in the completed fraction field

The localization and its principal-adic completion embed in the common completed fraction
field. The embedding respects base-ring elements and realizes the completed field as a
fraction field of the localized completion.

For the units identity localization of `PowerSeries ℚ`, the image of one in the completed
valuation integers has a unique representative in the localized `X`-adic completion, and
zero is not that representative.

The proofs reuse Mathlib's power-series discrete valuation ring, its separated maximal-ideal
filtration, and the completed-localization comparison API of AdicModules.

## References

The units-localization model uses Mathlib's power-series DVR and separated
maximal-ideal filtration. Its embedding and unique-base-representative criterion
come from `AdicModules.LocalizedCompletion`.
-/

set_option warningAsError true
set_option linter.style.haveILetI false

open scoped Topology

noncomputable section

universe u v w

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

/-- The localized completion embedding distinguishes the canonical base elements zero and one. -/
private theorem localizedComparisonSeparatesZeroOne :
    localizedAdicCompletionToFractionFieldCompletion (K := K) S ha0 hS
        (algebraMap Vₛ (AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ)
          (algebraMap V Vₛ 0)) ≠
      localizedAdicCompletionToFractionFieldCompletion (K := K) S ha0 hS
        (algebraMap Vₛ (AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ)
          (algebraMap V Vₛ 1)) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  rw [baseMapClient (K := K) S ha0 hS, baseMapClient (K := K) S ha0 hS]
  simp

end ValuationRing

namespace ValuationRing

/-- One in the completed valuation integers of `PowerSeries ℚ` has a unique representative
in the units-localized `X`-adic completion; its representative cannot be zero. -/
public theorem powerSeries_unitsLocalizedCompletion_unique_one :
    let hUnits : Disjoint (IsUnit.submonoid (PowerSeries ℚ) : Set (PowerSeries ℚ))
        ((Ideal.span {(PowerSeries.X : PowerSeries ℚ)}).radical : Set (PowerSeries ℚ)) := by
      rw [Set.disjoint_left]
      intro s hs hr
      have hnot : ¬ IsUnit s := by
        simpa only [← PowerSeries.maximalIdeal_eq_span_X (k := ℚ),
          IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using
          (PowerSeries.span_X_isPrime (R := ℚ)).isRadical hr
      exact hnot hs
    let hSep : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) :=
      Eq.mp
        (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ IsHausdorff I (PowerSeries ℚ))
          (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
        (inferInstance :
          IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ))
    let f := @localizedAdicCompletionToFractionFieldCompletion
      (PowerSeries ℚ) (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))
      _ _ _ _ _ _ _ (IsUnit.submonoid (PowerSeries ℚ)) _ _
      PowerSeries.X (PowerSeries.X_ne_zero (R := ℚ)) hUnits hSep
    (∃! z : AdicCompletion
        (Ideal.span {algebraMap (PowerSeries ℚ) (PowerSeries ℚ) PowerSeries.X})
        (PowerSeries ℚ),
      f z = (algebraMap (PowerSeries ℚ)
        (CompletionIntegers (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))) 1).val) ∧
      f 0 ≠ (algebraMap (PowerSeries ℚ)
        (CompletionIntegers (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))) 1).val := by
  intro hUnits hSep f
  letI : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) := hSep
  let A := AdicCompletion
    (Ideal.span {algebraMap (PowerSeries ℚ) (PowerSeries ℚ) PowerSeries.X})
    (PowerSeries ℚ)
  letI : IsHausdorff
      (Ideal.span {algebraMap (PowerSeries ℚ) (PowerSeries ℚ) PowerSeries.X})
      (PowerSeries ℚ) :=
    isHausdorff_localization_span_singleton
      (IsUnit.submonoid (PowerSeries ℚ)) (PowerSeries ℚ) hUnits
  letI : IsDomain A := principalAdicCompletion_isDomain (FractionRing (PowerSeries ℚ))
    (algebraMap (PowerSeries ℚ) (PowerSeries ℚ) PowerSeries.X)
    (by simp)
  have hRep (z : A) :
      f z = (algebraMap (PowerSeries ℚ)
        (CompletionIntegers (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))) 1).val ↔
      z = algebraMap (PowerSeries ℚ) A
        (algebraMap (PowerSeries ℚ) (PowerSeries ℚ) 1) :=
    localizedAdicCompletionToFractionFieldCompletion_eq_completionIntegers_iff
      (Vₛ := PowerSeries ℚ) (K := FractionRing (PowerSeries ℚ))
      (IsUnit.submonoid (PowerSeries ℚ)) (PowerSeries.X_ne_zero (R := ℚ)) hUnits z 1
  constructor
  · refine ⟨algebraMap (PowerSeries ℚ) A
      (algebraMap (PowerSeries ℚ) (PowerSeries ℚ) 1), (hRep _).2 rfl, ?_⟩
    intro z hz
    exact (hRep z).1 hz
  · intro hz
    have hzero : (0 : A) = 1 := by
      simpa only [map_one] using (hRep 0).1 hz
    exact zero_ne_one hzero

end ValuationRing
