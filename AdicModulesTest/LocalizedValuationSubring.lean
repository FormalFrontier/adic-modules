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
# Embeddings of completed localizations

The localized principal-adic completion is viewed in its common completed fraction field.
The coercion equality criterion lets two elements be compared through the valuation-subring
realization in the common completed field.

For `PowerSeries ℚ`, its canonical fraction field, generator `X`, and localization at all
units, the criterion distinguishes the completed-field realizations of zero and one.

The proofs reuse Mathlib's power-series discrete valuation ring and separated maximal-ideal
filtration, and the completion and valuation-subring APIs of AdicModules.

## References

The units-localization model uses Mathlib's power-series DVR and separated
powers. The completion embedding and valuation-subring coercion equality
criterion come from `AdicModules.LocalizedValuationSubring` and
`AdicModules.LocalizedCompletion`.
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

namespace ValuationRing

/-- The valuation-subring realization of the units-localized `X`-adic completion of
`PowerSeries ℚ` distinguishes zero and one in the common completed fraction field. -/
public theorem powerSeries_unitsLocalizedValuationSubring_zero_ne_one :
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
    let e := @localizedAdicCompletionValuationSubringEquiv
      (PowerSeries ℚ) (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))
      _ _ _ _ _ _ _ (IsUnit.submonoid (PowerSeries ℚ)) _ _
      PowerSeries.X (PowerSeries.X_ne_zero (R := ℚ)) hUnits hSep
    (e 0).val ≠ (e 1).val := by
  intro hUnits hSep e
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
  intro h
  have hzero : (0 : A) = 1 :=
    (localizedAdicCompletion_equiv_coe_eq_iff
      (Vₛ := PowerSeries ℚ) (K := FractionRing (PowerSeries ℚ))
      (IsUnit.submonoid (PowerSeries ℚ)) (PowerSeries.X_ne_zero (R := ℚ)) hUnits 0 1).1 h
  exact zero_ne_one hzero

end ValuationRing
