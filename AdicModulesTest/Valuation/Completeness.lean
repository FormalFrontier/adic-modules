/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Valuation.Completeness
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Complete valuation integers: p-adic and discrete-valuation examples

For `ℚ_[5]` with its usual complete norm uniformity, `ℤ_[5]` is exactly the valuation
integers. Its nonzero uniformizer `5` generates the maximal ideal, whose powers are separated.
The principal-adic completeness theorem is applied to these inputs, rather than using the
existing p-adic adic-completeness instance. The zero generator tests the separate boundary.

The final example obtains maximal-ideal completeness for any discrete valuation ring
presented as the integers of a complete valued field, with no residue-field restriction.

## References

The inputs use Mathlib's usual complete p-adic valued uniformity, valuation
integers and DVR separated maximal-ideal powers. The principal-adic completeness
bridge, including its zero-generator boundary, comes from
`AdicModules.Valuation.Completeness`, whose References give its mathematical motivation.
-/

set_option warningAsError true

open scoped NNReal

public instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private noncomputable instance : Valued ℚ_[5] ℝ≥0 := NormedField.toValued

private theorem padicIntegers : (Valued.v : Valuation ℚ_[5] ℝ≥0).Integers ℤ_[5] where
  hom_inj := Subtype.coe_injective
  map_le_one x := by
    change ‖(x : ℚ_[5])‖₊ ≤ 1
    exact_mod_cast x.2
  exists_of_le_one {x} hx := by
    change ‖x‖₊ ≤ 1 at hx
    exact ⟨⟨x, by exact_mod_cast hx⟩, rfl⟩

-- The chosen valued structure retains the usual norm uniformity and its completeness.
private theorem padic_five_completeSpace : CompleteSpace ℚ_[5] := inferInstance

private theorem padicInt_five_ne_zero : (5 : ℤ_[5]) ≠ 0 := by norm_num

private theorem padicSeparated : IsHausdorff (Ideal.span {(5 : ℤ_[5])}) ℤ_[5] := by
  simpa only [PadicInt.maximalIdeal_eq_span_p, Nat.cast_ofNat] using
    (IsDiscreteValuationRing.instIsHausdorffMaximalIdeal ℤ_[5])

/-- The valuation-integers completeness bridge applied to `ℤ_[5]` and its uniformizer `5`. -/
public theorem PadicInt.isAdicComplete_span_five :
    IsAdicComplete (Ideal.span {(5 : ℤ_[5])}) ℤ_[5] := by
  have := padicSeparated
  exact padicIntegers.isAdicComplete_span_singleton

private theorem padicInt_span_zero_complete : IsAdicComplete (Ideal.span {(0 : ℤ_[5])}) ℤ_[5] := by
  have : IsHausdorff (Ideal.span {(0 : ℤ_[5])}) ℤ_[5] := by
    simp only [Ideal.span_singleton_zero]
    infer_instance
  exact padicIntegers.isAdicComplete_span_singleton

universe u v w

private theorem isAdicComplete_maximalIdeal_of_integers {V : Type u} {K : Type v} {Γ₀ : Type w}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [LinearOrderedCommGroupWithZero Γ₀]
    [hv : Valued K Γ₀] [CompleteSpace K] (hV : hv.v.Integers V) :
    IsAdicComplete (IsLocalRing.maximalIdeal V) V := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have : IsHausdorff (Ideal.span {π}) V := by
    rw [← hπ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.instIsHausdorffMaximalIdeal V
  rw [hπ.maximalIdeal_eq]
  exact hV.isAdicComplete_span_singleton
