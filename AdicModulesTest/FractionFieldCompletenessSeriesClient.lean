/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Valuation.Completeness
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Power series as valuation integers in Laurent series

Over an arbitrary field, the maximal-ideal valuation on Laurent series is the usual
`X`-adic valuation, with the original Hahn-series embedding of power series. Its uniformity
is complete by Mathlib's coefficientwise construction. The completeness theorem for valuation
integers then gives completeness of power series for the powers of `(X)`. Conversely,
principal-adic completeness at `X` gives completeness for the same maximal-ideal valuation.

The coefficient in degree `-1` shows that `X⁻¹` is outside the image of power series.
No topology on the coefficient field is required.

## References

The algebraic identifications and coefficientwise completeness reuse Mathlib's power-series,
Laurent-series and discrete-valuation formalizations, in particular the work of Aaron Anderson,
María Inés de Frutos-Fernández and Filippo A. E. Nuccio. The adic conclusion uses the
valuation-integers completeness theorem in `AdicModules.Valuation.Completeness`.
-/

universe u

namespace LaurentSeries

variable (κ : Type u) [Field κ]

private theorem powerSeries_algebraMap (f : PowerSeries κ) :
    algebraMap (PowerSeries κ) (LaurentSeries κ) f = HahnSeries.ofPowerSeries ℤ κ f :=
  rfl

private theorem maximalIdeal_eq_idealX :
    IsDiscreteValuationRing.maximalIdeal (PowerSeries κ) = PowerSeries.idealX κ := by
  apply IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
  exact PowerSeries.maximalIdeal_eq_span_X

private noncomputable def maximalIdealValuation :
    Valuation (LaurentSeries κ) (WithZero (Multiplicative ℤ)) :=
  (IsDiscreteValuationRing.maximalIdeal (PowerSeries κ)).valuation (LaurentSeries κ)

private noncomputable def maximalIdealValued :
    Valued (LaurentSeries κ) (WithZero (Multiplicative ℤ)) :=
  Valued.mk' (maximalIdealValuation κ)

private theorem maximalIdealValuation_eq :
    maximalIdealValuation κ =
      (Valued.v : Valuation (LaurentSeries κ) (WithZero (Multiplicative ℤ))) := by
  rw [maximalIdealValuation, maximalIdeal_eq_idealX κ, valuation_def]

private theorem maximalIdealValued_eq :
    maximalIdealValued κ = LaurentSeries.valued κ := by
  change Valued.mk' (maximalIdealValuation κ) =
    Valued.mk' (Valued.v : Valuation (LaurentSeries κ) (WithZero (Multiplicative ℤ)))
  rw [maximalIdealValuation_eq κ]

private theorem maximalIdeal_uniformSpace_eq :
    (maximalIdealValued κ).toUniformSpace = (LaurentSeries.valued κ).toUniformSpace :=
  congrArg (fun v : Valued (LaurentSeries κ) (WithZero (Multiplicative ℤ)) ↦ v.toUniformSpace)
    (maximalIdealValued_eq κ)

private theorem maximalIdeal_completeSpace :
    @CompleteSpace (LaurentSeries κ) (maximalIdealValued κ).toUniformSpace := by
  rw [maximalIdeal_uniformSpace_eq κ]
  exact LaurentSeries.instLaurentSeriesComplete (K := κ)

private theorem maximalIdeal_integers :
    (maximalIdealValuation κ).Integers (PowerSeries κ) where
  hom_inj := IsFractionRing.injective (PowerSeries κ) (LaurentSeries κ)
  map_le_one f :=
    (IsDiscreteValuationRing.maximalIdeal (PowerSeries κ)).valuation_le_one
      (K := LaurentSeries κ) f
  exists_of_le_one {z} hz :=
    IsDiscreteValuationRing.exists_lift_of_le_one
      (A := PowerSeries κ) (K := LaurentSeries κ) hz

private theorem powerSeries_integers :
    (Valued.v : Valuation (LaurentSeries κ) (WithZero (Multiplicative ℤ))).Integers
      (PowerSeries κ) := by
  rw [← maximalIdealValuation_eq κ]
  exact maximalIdeal_integers κ

private theorem powerSeries_X_ne_zero : (PowerSeries.X : PowerSeries κ) ≠ 0 :=
  PowerSeries.X_ne_zero

private theorem powerSeries_X_hausdorff :
    IsHausdorff (Ideal.span {(PowerSeries.X : PowerSeries κ)}) (PowerSeries κ) := by
  rw [← PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

private theorem powerSeries_X_adicComplete :
    IsAdicComplete (Ideal.span {(PowerSeries.X : PowerSeries κ)}) (PowerSeries κ) := by
  have : CompleteSpace (LaurentSeries κ) := LaurentSeries.instLaurentSeriesComplete (K := κ)
  have := powerSeries_X_hausdorff κ
  exact (powerSeries_integers κ).isAdicComplete_span_singleton

private theorem powerSeries_maximalIdeal_adicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries κ)) (PowerSeries κ) := by
  rw [PowerSeries.maximalIdeal_eq_span_X]
  exact powerSeries_X_adicComplete κ

private theorem single_neg_one_not_in_range :
    (HahnSeries.single (-1 : ℤ) (1 : κ) : LaurentSeries κ) ∉
      Set.range (algebraMap (PowerSeries κ) (LaurentSeries κ)) := by
  rintro ⟨f, hf⟩
  have hcoeff := congrArg (fun g : LaurentSeries κ ↦ g.coeff (-1)) hf
  change (f : LaurentSeries κ).coeff (-1) =
    (HahnSeries.single (-1 : ℤ) (1 : κ) : LaurentSeries κ).coeff (-1) at hcoeff
  rw [PowerSeries.coeff_coe, if_pos (show (-1 : ℤ) < 0 by simp),
    HahnSeries.coeff_single_same] at hcoeff
  exact (zero_ne_one : (0 : κ) ≠ 1) hcoeff

private theorem single_neg_one_not_integer :
    ¬ maximalIdealValuation κ (HahnSeries.single (-1 : ℤ) (1 : κ)) ≤ 1 := by
  intro h
  exact single_neg_one_not_in_range κ ((maximalIdeal_integers κ).exists_of_le_one h)

private theorem maximalIdeal_completeSpace_of_adic :
    @CompleteSpace (LaurentSeries κ) (maximalIdealValued κ).toUniformSpace := by
  let : IsHausdorff (Ideal.span {(PowerSeries.X : PowerSeries κ)}) (PowerSeries κ) :=
    powerSeries_X_hausdorff κ
  exact (Valuation.Integers.isAdicComplete_span_singleton_iff
    (hv := maximalIdealValued κ) (maximalIdeal_integers κ) (powerSeries_X_ne_zero κ)).mp
      (powerSeries_X_adicComplete κ)

end LaurentSeries
