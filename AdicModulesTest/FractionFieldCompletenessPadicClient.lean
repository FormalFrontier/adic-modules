/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Valuation.Completeness
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.UniformSpace.Equiv

/-!
# The maximal-ideal valuation on the 3-adic field

The integers `ℤ_[3]` are the integers of the valuation on `ℚ_[3]` associated to their
height-one maximal ideal. Mathlib's maximal-adic completeness of `ℤ_[3]` supplies the
principal-adic input at `3`. Completeness for this valuation's uniformity follows separately
from completeness for the p-adic norm, through an identity-on-elements uniform equivalence.
All maps retain the given field operations and the usual embedding of p-adic integers.
The principal-adic completeness equivalence recovers completeness of the fraction field
for this same specified valuation uniformity.
Primality is supplied by `Nat.fact_prime_three`.

## References

These examples use Mathlib's p-adic formalization by Robert Y. Lewis, Mario Carneiro and
Johan Commelin, the valuation and DVR APIs by Kenny Lau and María Inés de Frutos-Fernández,
the normed-valued comparison by María Inés de Frutos-Fernández and Filippo A. E. Nuccio,
and Mathlib's uniform-equivalence and completeness APIs.
-/

namespace PadicInt

private noncomputable def threeAdicMap : ℤ_[3] →+* ℚ_[3] :=
  algebraMap ℤ_[3] ℚ_[3]

private noncomputable def threeAdicIdeal :
    IsDedekindDomain.HeightOneSpectrum ℤ_[3] :=
  IsDiscreteValuationRing.maximalIdeal ℤ_[3]

private noncomputable def threeAdicValuation :
    Valuation ℚ_[3] (WithZero (Multiplicative ℤ)) :=
  threeAdicIdeal.valuation ℚ_[3]

@[instance_reducible]
private noncomputable def threeAdicValued : Valued ℚ_[3] (WithZero (Multiplicative ℤ)) :=
  Valued.mk' threeAdicValuation

private theorem threeAdicMap_apply (a : ℤ_[3]) : threeAdicMap a = (a : ℚ_[3]) :=
  PadicInt.algebraMap_apply a

private theorem three_ne_zero : (3 : ℤ_[3]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 2)

private theorem threeAdicValuation_integers : threeAdicValuation.Integers ℤ_[3] where
  hom_inj := IsFractionRing.injective ℤ_[3] ℚ_[3]
  map_le_one a := threeAdicIdeal.valuation_le_one (K := ℚ_[3]) a
  exists_of_le_one {x} hx :=
    IsDiscreteValuationRing.exists_lift_of_le_one (A := ℤ_[3]) (K := ℚ_[3]) (x := x) hx

private theorem maximalIdeal_eq_span_three :
    IsLocalRing.maximalIdeal ℤ_[3] = Ideal.span {(3 : ℤ_[3])} :=
  PadicInt.maximalIdeal_eq_span_p

private theorem span_three_hausdorff : IsHausdorff (Ideal.span {(3 : ℤ_[3])}) ℤ_[3] := by
  rw [← maximalIdeal_eq_span_three]
  infer_instance

private theorem maximalIdeal_three_adicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[3]) ℤ_[3] := inferInstance

private theorem span_three_adicComplete :
    IsAdicComplete (Ideal.span {(3 : ℤ_[3])}) ℤ_[3] := by
  rw [← maximalIdeal_eq_span_three]
  exact maximalIdeal_three_adicComplete

-- This source uniformity is explicitly the one from the p-adic normed field.
private theorem padic_three_completeSpace :
    @CompleteSpace ℚ_[3] (Padic.normedField 3).toUniformSpace := inferInstance

private theorem threeAdicValuation_le_one_iff (x : ℚ_[3]) :
    threeAdicValuation x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := threeAdicValuation_integers.exists_of_le_one hx
    simpa only [PadicInt.algebraMap_apply] using a.property
  · intro hx
    simpa only [PadicInt.algebraMap_apply, Subtype.coe_mk] using!
      threeAdicValuation_integers.map_le_one (⟨x, hx⟩ : ℤ_[3])

private theorem threeAdicValuation_isEquiv_norm :
    threeAdicValuation.IsEquiv (NormedField.valuation (K := ℚ_[3])) := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  refine (threeAdicValuation_le_one_iff x).trans ?_
  simpa only [NormedField.valuation_apply, coe_nnnorm, NNReal.coe_one] using
    (NNReal.coe_le_coe (r₁ := ‖x‖₊) (r₂ := (1 : NNReal)))

private noncomputable def threeAdicUniformEquiv :
    @UniformEquiv ℚ_[3] ℚ_[3] threeAdicValued.toUniformSpace
      (Padic.normedField 3).toUniformSpace := by
  let eVal : @UniformEquiv (WithVal threeAdicValuation) ℚ_[3] _
      threeAdicValued.toUniformSpace := by
    letI : Valued ℚ_[3] (WithZero (Multiplicative ℤ)) := threeAdicValued
    exact WithVal.uniformEquiv (v := threeAdicValuation) (w := threeAdicValuation)
      rfl (Valuation.IsEquiv.refl (v := threeAdicValuation))
  let eNorm : @UniformEquiv (WithVal threeAdicValuation) ℚ_[3] _
      (Padic.normedField 3).toUniformSpace := by
    letI : Valued ℚ_[3] NNReal := NormedField.toValued (K := ℚ_[3])
    exact WithVal.uniformEquiv (v := threeAdicValuation)
      (w := NormedField.valuation (K := ℚ_[3])) rfl threeAdicValuation_isEquiv_norm
  exact @UniformEquiv.trans ℚ_[3] (WithVal threeAdicValuation) ℚ_[3]
    threeAdicValued.toUniformSpace (WithVal.instValued threeAdicValuation).toUniformSpace
    (Padic.normedField 3).toUniformSpace
    (@UniformEquiv.symm (WithVal threeAdicValuation) ℚ_[3]
      (WithVal.instValued threeAdicValuation).toUniformSpace threeAdicValued.toUniformSpace eVal)
    eNorm

private theorem threeAdicUniformEquiv_apply (x : ℚ_[3]) :
    threeAdicUniformEquiv x = x := rfl

private theorem threeAdicUniformEquiv_toEquiv :
    @UniformEquiv.toEquiv ℚ_[3] ℚ_[3] threeAdicValued.toUniformSpace
      (Padic.normedField 3).toUniformSpace threeAdicUniformEquiv =
      (RingEquiv.refl ℚ_[3]).toEquiv := rfl

private theorem threeAdicUniformEquiv_map (a : ℤ_[3]) :
    threeAdicUniformEquiv (threeAdicMap a) = (a : ℚ_[3]) := by
  rw [threeAdicUniformEquiv_apply, threeAdicMap_apply]

private theorem threeAdic_completeSpace :
    @CompleteSpace ℚ_[3] threeAdicValued.toUniformSpace := by
  exact (@UniformEquiv.completeSpace_iff ℚ_[3] ℚ_[3] threeAdicValued.toUniformSpace
    (Padic.normedField 3).toUniformSpace threeAdicUniformEquiv).mpr padic_three_completeSpace

private theorem threeAdicValuation_three :
    threeAdicValuation (3 : ℚ_[3]) = WithZero.exp (-1 : ℤ) := by
  calc
    threeAdicValuation (3 : ℚ_[3]) =
        threeAdicValuation (algebraMap ℤ_[3] ℚ_[3] (3 : ℤ_[3])) :=
      congrArg threeAdicValuation
        ((PadicInt.algebraMap_apply (3 : ℤ_[3])).trans (PadicInt.coe_natCast 3)).symm
    _ = threeAdicIdeal.intValuation (3 : ℤ_[3]) :=
      threeAdicIdeal.valuation_of_algebraMap (K := ℚ_[3]) (3 : ℤ_[3])
    _ = WithZero.exp (-1 : ℤ) :=
      threeAdicIdeal.intValuation_singleton three_ne_zero maximalIdeal_eq_span_three

private theorem threeAdic_completeSpace_of_adic :
    @CompleteSpace ℚ_[3] threeAdicValued.toUniformSpace := by
  let : IsHausdorff (Ideal.span {(3 : ℤ_[3])}) ℤ_[3] := span_three_hausdorff
  exact (Valuation.Integers.isAdicComplete_span_singleton_iff
    (hv := threeAdicValued) threeAdicValuation_integers three_ne_zero).mp
      span_three_adicComplete

end PadicInt
