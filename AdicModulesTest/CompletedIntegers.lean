/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Canonical elements under the completed-integers comparison

The principal-adic comparison with the completed valuation integers respects the base-ring
algebra maps, with independent universes for the valuation ring and its fraction field.

For rational power series, the `X`-adic comparison distinguishes the canonical images of zero
and one and recovers the canonical adic one from the completed valuation integer one.

## References

The power-series discrete valuation ring, fraction ring and separated powers of the maximal ideal
are supplied by Mathlib. The comparison and its inverse criterion are supplied by
`AdicModules.CompletedIntegers`.
-/

set_option warningAsError true

noncomputable section

universe u v

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

/-- The comparison distinguishes zero and one in this nontrivial completion. -/
private theorem comparisonSeparatesZeroOne :
    ValuationRing.principalAdicCompletionEquiv (K := K) a ha0
        (0 : AdicCompletion (Ideal.span {a}) V) ≠
      ValuationRing.principalAdicCompletionEquiv (K := K) a ha0 1 := by
  let : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
    ValuationRing.principalAdicCompletion_isDomain K a ha0
  intro h
  exact zero_ne_one
    ((ValuationRing.principalAdicCompletionEquiv (K := K) a ha0).injective h)

end

/-- The `X`-adic comparison for rational power series separates the base-ring images of zero and
one, and its inverse recovers the canonical image of one. -/
public theorem PowerSeries.principalAdicCompletionEquiv_zero_one :
    let hSep : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) :=
      Eq.mp
        (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ IsHausdorff I (PowerSeries ℚ))
          (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
        (inferInstance :
          IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ))
    let e := @ValuationRing.principalAdicCompletionEquiv
      (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
      PowerSeries.X PowerSeries.X_ne_zero hSep
    (e (algebraMap (PowerSeries ℚ)
        (AdicCompletion (Ideal.span {PowerSeries.X}) (PowerSeries ℚ)) 0) ≠
      e (algebraMap (PowerSeries ℚ)
        (AdicCompletion (Ideal.span {PowerSeries.X}) (PowerSeries ℚ)) 1)) ∧
      e.symm (algebraMap (PowerSeries ℚ)
        (ValuationRing.CompletionIntegers (PowerSeries ℚ)
          (FractionRing (PowerSeries ℚ))) 1) =
        algebraMap (PowerSeries ℚ)
          (AdicCompletion (Ideal.span {PowerSeries.X}) (PowerSeries ℚ)) 1 := by
  let hSep : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) :=
    Eq.mp
      (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ IsHausdorff I (PowerSeries ℚ))
        (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
      (inferInstance :
        IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ))
  have : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) := hSep
  have : IsDomain (AdicCompletion (Ideal.span {PowerSeries.X}) (PowerSeries ℚ)) :=
    ValuationRing.principalAdicCompletion_isDomain (FractionRing (PowerSeries ℚ))
      PowerSeries.X PowerSeries.X_ne_zero
  dsimp only
  constructor
  · intro h
    have h01 :
        (0 : AdicCompletion (R := PowerSeries ℚ)
          (Ideal.span {PowerSeries.X}) (PowerSeries ℚ)) = 1 := by
      simpa only [map_zero, map_one] using
        (ValuationRing.principalAdicCompletionEquiv
          (V := PowerSeries ℚ) (K := FractionRing (PowerSeries ℚ))
          PowerSeries.X PowerSeries.X_ne_zero).injective h
    exact zero_ne_one h01
  · exact (@ValuationRing.principalAdicCompletionEquiv_symm_eq_algebraMap_iff
      (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
      PowerSeries.X PowerSeries.X_ne_zero hSep
      (algebraMap (PowerSeries ℚ)
        (ValuationRing.CompletionIntegers (PowerSeries ℚ)
          (FractionRing (PowerSeries ℚ))) 1) 1).2 rfl
