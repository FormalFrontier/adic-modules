/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic.NormNum

/-!
# Normalized additive valuation inputs over the 3-adic field

The stock additive valuation on `ℚ_[3]` takes values in `WithTop ℤ` and sends `3` to `1`.
Its canonical valuation subring is formed using `AddValuation.toValuation`, whose value type is
`Multiplicative ((WithTop ℤ)ᵒᵈ)`. Thus membership means nonnegative additive valuation, and the
maximal ideal consists of elements of positive additive valuation. Its residue field has
characteristic `3`.

The canonical integers `1` and `4` are distinct units. Their difference has valuation `1`,
whereas the difference of their cubes has valuation exactly `2`, not at least `3`. In particular,
they realize the positive-depth case `m = n = 1` of a one-step valuation improvement, without
using a general estimate. The computation uses `1 - 4 = -3` and
`1 ^ 3 - 4 ^ 3 = -(3 ^ 2 * 7)` in the actual 3-adic field.

The zero-depth boundary is different: the difference of `0` and `1`, and the difference of
their cubes, both have valuation zero.

## References

The 3-adic field and its additive valuation are Mathlib's `Padic` and `Padic.addValuation`,
from `Mathlib.NumberTheory.Padics.PadicNumbers` (Robert Y. Lewis). The integer-valued
normalization and values of natural numbers use that module's `Padic.valuation_p` and
`Padic.valuation_ofNat`. The canonical integer and residue constructions use Mathlib's
valuation-subring and local-ring residue-field APIs.
-/

@[expose] public section

namespace ValuationPowerModel

noncomputable section

private abbrev v3 : AddValuation ℚ_[3] (WithTop ℤ) := Padic.addValuation

private abbrev O3 : ValuationSubring ℚ_[3] :=
  (AddValuation.toValuation v3).valuationSubring

private theorem value_three : v3 (3 : ℚ_[3]) = 1 := by
  have h : Padic.valuation (3 : ℚ_[3]) = 1 := by
    simpa only [Nat.cast_ofNat] using (Padic.valuation_p (p := 3))
  simpa only [h, WithTop.coe_one] using
    (Padic.addValuation.apply (p := 3) (x := (3 : ℚ_[3])) (by norm_num))

private theorem value_four : v3 (4 : ℚ_[3]) = 0 := by
  have h : padicValNat 3 4 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  simpa only [Padic.valuation_ofNat, h, Nat.cast_zero, WithTop.coe_zero] using
    (Padic.addValuation.apply (p := 3) (x := (4 : ℚ_[3])) (by norm_num))

private theorem value_seven : v3 (7 : ℚ_[3]) = 0 := by
  have h : padicValNat 3 7 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  simpa only [Padic.valuation_ofNat, h, Nat.cast_zero, WithTop.coe_zero] using
    (Padic.addValuation.apply (p := 3) (x := (7 : ℚ_[3])) (by norm_num))

private theorem value_difference : v3 ((1 : ℚ_[3]) - 4) = 1 := by
  have h : (1 : ℚ_[3]) - 4 = -3 := by norm_num
  rw [h, v3.map_neg, value_three]

private theorem value_cube_difference : v3 ((1 : ℚ_[3]) ^ 3 - 4 ^ 3) = 2 := by
  have h : (1 : ℚ_[3]) ^ 3 - 4 ^ 3 = -((3 : ℚ_[3]) ^ 2 * 7) := by norm_num
  rw [h, v3.map_neg, v3.map_mul, v3.map_pow, value_three, value_seven]
  norm_num [two_nsmul]

private theorem residue_characteristic : CharP (IsLocalRing.ResidueField O3) 3 := by
  apply (CharP.charP_iff_prime_eq_zero (show Nat.Prime 3 from Fact.out)).mpr
  have hmem : (3 : O3) ∈ IsLocalRing.maximalIdeal O3 := by
    apply (Valuation.mem_maximalIdeal_iff ℚ_[3] (AddValuation.toValuation v3)).mpr
    change (0 : WithTop ℤ) < v3 (algebraMap O3 ℚ_[3] (3 : O3))
    rw [map_ofNat, value_three]
    exact WithTop.coe_lt_coe.mpr (by norm_num : (0 : ℤ) < 1)
  simpa only [map_ofNat, Nat.cast_ofNat] using
    (IsLocalRing.residue_eq_zero_iff (3 : O3)).mpr hmem

private theorem four_isUnit : IsUnit (4 : O3) := by
  apply (Valuation.valuationSubring.integers (AddValuation.toValuation v3)).isUnit_of_one'
  rw [map_ofNat]
  change v3 (4 : ℚ_[3]) = 0
  exact value_four

/-- Canonical integer data, residue characteristic and an exact positive-depth computation over
`ℚ_[3]`. The two inputs are the canonical integer numerals, mapped by the stock algebra map. -/
theorem canonicalQ3_inputs :
    let v : AddValuation ℚ_[3] (WithTop ℤ) := Padic.addValuation
    let O := (AddValuation.toValuation v).valuationSubring
    let a : O := 1
    let b : O := 4
    CharP (IsLocalRing.ResidueField O) 3 ∧
      v (3 : ℚ_[3]) = 1 ∧
      algebraMap O ℚ_[3] a = 1 ∧
      algebraMap O ℚ_[3] b = 4 ∧
      IsUnit a ∧ IsUnit b ∧
      0 ≤ v (algebraMap O ℚ_[3] a) ∧
      0 ≤ v (algebraMap O ℚ_[3] b) ∧
      algebraMap O ℚ_[3] a - algebraMap O ℚ_[3] b ≠ 0 ∧
      v (algebraMap O ℚ_[3] a - algebraMap O ℚ_[3] b) = 1 ∧
      v ((algebraMap O ℚ_[3] a) ^ (3 ^ 1 : ℕ) -
        (algebraMap O ℚ_[3] b) ^ (3 ^ 1 : ℕ)) = 2 ∧
      2 ≤ v ((algebraMap O ℚ_[3] a) ^ (3 ^ 1 : ℕ) -
        (algebraMap O ℚ_[3] b) ^ (3 ^ 1 : ℕ)) ∧
      ¬ (3 ≤ v ((algebraMap O ℚ_[3] a) ^ (3 ^ 1 : ℕ) -
        (algebraMap O ℚ_[3] b) ^ (3 ^ 1 : ℕ))) := by
  dsimp only
  refine ⟨residue_characteristic, value_three, by simp only [map_one],
    by simp only [map_ofNat], isUnit_one, four_isUnit, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [map_one, AddValuation.map_one, le_refl]
  · simpa only [map_ofNat, value_four] using (le_refl (0 : WithTop ℤ))
  · simp only [map_one, map_ofNat]
    norm_num
  · simpa only [map_one, map_ofNat] using value_difference
  · simpa only [map_one, map_ofNat, pow_one] using value_cube_difference
  · simpa only [map_one, map_ofNat, pow_one, value_cube_difference] using
      (le_refl (2 : WithTop ℤ))
  · simp only [map_one, map_ofNat, pow_one, value_cube_difference]
    change ¬ (((3 : ℤ) : WithTop ℤ) ≤ ((2 : ℤ) : WithTop ℤ))
    rw [WithTop.coe_le_coe]
    norm_num

/-- At depth zero, cubing the integral pair `0, 1` does not improve the valuation. -/
theorem canonicalQ3_zero_depth :
    let v : AddValuation ℚ_[3] (WithTop ℤ) := Padic.addValuation
    v ((0 : ℚ_[3]) - 1) = 0 ∧
      v ((0 : ℚ_[3]) ^ 3 - 1 ^ 3) = 0 ∧
      ¬ (1 ≤ v ((0 : ℚ_[3]) ^ 3 - 1 ^ 3)) := by
  dsimp only
  have h : v3 ((0 : ℚ_[3]) ^ 3 - 1 ^ 3) = 0 := by
    simp only [zero_pow (by decide : 3 ≠ 0), one_pow, zero_sub, AddValuation.map_neg,
      AddValuation.map_one]
  refine ⟨?_, h, ?_⟩
  · simp only [zero_sub, AddValuation.map_neg, AddValuation.map_one]
  · rw [h]
    exact not_le_of_gt (WithTop.coe_lt_coe.mpr (by norm_num : (0 : ℤ) < 1))

end

end ValuationPowerModel
