/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Polynomial.HenselianFactorization
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Ideal-power factorization precision over `ZMod 256`

For the ideal `(2)`, the factors `2X + 1` and `2X + 3` have resultant `4`.
The error `128` is nonzero and lies in the seventh ideal power. With `s = 3`
and `t = 2`, the precision corollary gives corrections in the fourth power,
not merely the third. The resultant is a zero divisor and both leading
coefficients are nonunits. Nilpotence proves Henselianity independently of
the explicit corrected factors `2X + 65` and `2X + 195`.
-/

open Polynomial

example :
    let M : Ideal (ZMod 256) := Ideal.span {2}
    let g₀ : (ZMod 256)[X] := 2 * X + 1
    let h₀ : (ZMod 256)[X] := 2 * X + 3
    let f := g₀ * h₀ + 128
    let lift := fun g h : (ZMod 256)[X] ↦
      f = g * h ∧
        (g - g₀).degree < (g₀.natDegree : WithBot ℕ) ∧
        (h - h₀).degree < (h₀.natDegree : WithBot ℕ) ∧
        ∀ i : ℕ, (g - g₀).coeff i ∈ M ^ 4 ∧ (h - h₀).coeff i ∈ M ^ 4
    (∃ g h, lift g h) ∧ lift (2 * X + 65) (2 * X + 195) ∧
      f - g₀ * h₀ ≠ 0 ∧
      ¬ IsUnit g₀.leadingCoeff ∧ ¬ IsUnit h₀.leadingCoeff ∧
      resultant g₀ h₀ g₀.natDegree h₀.natDegree * 64 = 0 ∧
      (64 : ZMod 256) ≠ 0 := by
  let M : Ideal (ZMod 256) := Ideal.span {2}
  let g₀ : (ZMod 256)[X] := 2 * X + 1
  let h₀ : (ZMod 256)[X] := 2 * X + 3
  let f := g₀ * h₀ + 128
  let lift := fun g h : (ZMod 256)[X] ↦
    f = g * h ∧
      (g - g₀).degree < (g₀.natDegree : WithBot ℕ) ∧
      (h - h₀).degree < (h₀.natDegree : WithBot ℕ) ∧
      ∀ i : ℕ, (g - g₀).coeff i ∈ M ^ 4 ∧ (h - h₀).coeff i ∈ M ^ 4
  change (∃ g h, lift g h) ∧ lift (2 * X + 65) (2 * X + 195) ∧
    f - g₀ * h₀ ≠ 0 ∧
    ¬ IsUnit g₀.leadingCoeff ∧ ¬ IsUnit h₀.leadingCoeff ∧
    resultant g₀ h₀ g₀.natDegree h₀.natDegree * 64 = 0 ∧ (64 : ZMod 256) ≠ 0
  have hM8 : M ^ 8 = ⊥ := by
    change (Ideal.span {(2 : ZMod 256)}) ^ 8 = ⊥
    rw [Ideal.span_singleton_pow, show (2 : ZMod 256) ^ 8 = 0 by decide]
    simp
  -- A Cauchy sequence stabilizes at its eighth term because the eighth power vanishes.
  let : IsAdicComplete M (ZMod 256) := {
    haus' := by
      intro x hx
      simpa [hM8] using hx 8
    prec' := by
      intro u hu
      refine ⟨u 8, fun n ↦ ?_⟩
      by_cases hn : n ≤ 8
      · exact hu hn
      · have heq : u 8 = u n := by
          simpa [hM8] using hu (by omega : 8 ≤ n)
        simp [heq] }
  have hgdeg : g₀.natDegree = 1 := by
    change (C (2 : ZMod 256) * X + C 1).natDegree = 1
    rw [natDegree_add_C, natDegree_C_mul_X _ (by decide)]
  have hhdeg : h₀.natDegree = 1 := by
    change (C (2 : ZMod 256) * X + C 3).natDegree = 1
    rw [natDegree_add_C, natDegree_C_mul_X _ (by decide)]
  have hd : resultant g₀ h₀ g₀.natDegree h₀.natDegree = 4 := by
    rw [hgdeg, hhdeg, resultant]
    have hmatrix : sylvester g₀ h₀ 1 1 = !![3, 1; 2, 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [sylvester, g₀, h₀, Fin.addCases, coeff_one]
    rw [hmatrix, Matrix.det_fin_two]
    norm_num
  have hspan : Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree} = M ^ 2 := by
    rw [hd]
    change Ideal.span {(4 : ZMod 256)} = (Ideal.span {(2 : ZMod 256)}) ^ 2
    rw [Ideal.span_singleton_pow]
    norm_num
  have herr : f - g₀ * h₀ = C (128 : ZMod 256) := by
    rw [C_ofNat]
    dsimp [f]
    ring
  have hdegree : (f - g₀ * h₀).degree <
      (g₀.natDegree + h₀.natDegree : WithBot ℕ) := by
    rw [herr, hgdeg, hhdeg]
    exact lt_of_le_of_lt degree_C_le (by norm_num)
  have h128 : (128 : ZMod 256) ∈ M ^ 7 := by
    change (128 : ZMod 256) ∈ (Ideal.span {(2 : ZMod 256)}) ^ 7
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨1, by norm_num⟩
  have herror : ∀ i : ℕ, (f - g₀ * h₀).coeff i ∈ M ^ (2 * 3 + 1) := by
    intro i
    rw [herr]
    by_cases hi : i = 0
    · subst i
      simpa using h128
    · simp [coeff_C, hi]
  have hex : ∃ g h, lift g h :=
    exists_factorization_of_resultant_span_eq_pow M (s := 3) (t := 2)
      hdegree hspan (by norm_num) herror
  have h64 : (64 : ZMod 256) ∈ M ^ 4 := by
    change (64 : ZMod 256) ∈ (Ideal.span {(2 : ZMod 256)}) ^ 4
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨4, by norm_num⟩
  have h192 : (192 : ZMod 256) ∈ M ^ 4 := by
    change (192 : ZMod 256) ∈ (Ideal.span {(2 : ZMod 256)}) ^ 4
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨12, by norm_num⟩
  have hgc : (2 * X + 65 : (ZMod 256)[X]) - g₀ = C (64 : ZMod 256) := by
    rw [C_ofNat]
    dsimp [g₀]
    ring
  have hhc : (2 * X + 195 : (ZMod 256)[X]) - h₀ = C (192 : ZMod 256) := by
    rw [C_ofNat]
    dsimp [h₀]
    ring
  have hw : lift (2 * X + 65) (2 * X + 195) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h256 : (256 : (ZMod 256)[X]) = 0 := by
        have hz : (256 : ZMod 256) = 0 := by decide
        simpa only [C_ofNat, C_0] using congrArg (C : ZMod 256 → (ZMod 256)[X]) hz
      calc
        f = (2 * X + 65) * (2 * X + 195) - 256 * (2 * X + 49) := by
          dsimp [f, g₀, h₀]
          ring
        _ = (2 * X + 65) * (2 * X + 195) := by rw [h256]; ring
    · rw [hgc, hgdeg]
      exact lt_of_le_of_lt degree_C_le (by norm_num)
    · rw [hhc, hhdeg]
      exact lt_of_le_of_lt degree_C_le (by norm_num)
    · intro i
      rw [hgc, hhc]
      by_cases hi : i = 0
      · subst i
        simpa using And.intro h64 h192
      · simp [coeff_C, hi]
  refine ⟨hex, hw, ?_, ?_, ?_, ?_, ?_⟩
  · rw [herr, C_ne_zero]
    decide
  · have hlc : g₀.leadingCoeff = 2 := by
      rw [Polynomial.leadingCoeff, hgdeg]
      norm_num [g₀, coeff_one]
    rw [hlc]
    simpa only [Nat.cast_ofNat] using
      mt (ZMod.isUnit_iff_coprime 2 256).mp (by decide : ¬ Nat.Coprime 2 256)
  · have hlc : h₀.leadingCoeff = 2 := by
      rw [Polynomial.leadingCoeff, hhdeg]
      norm_num [h₀]
    rw [hlc]
    simpa only [Nat.cast_ofNat] using
      mt (ZMod.isUnit_iff_coprime 2 256).mp (by decide : ¬ Nat.Coprime 2 256)
  · rw [hd]
    decide
  · decide
