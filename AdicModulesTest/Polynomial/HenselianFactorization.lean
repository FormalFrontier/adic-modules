/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Polynomial.Hensel
import AdicModules.Polynomial.HenselianFactorization
import AdicModules.RingTheory.HenselianIdeal
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Monic factor lifting and nonmonic resultant-controlled input

The polynomial `X² - 4` over the 3-adic integers has the ordered coprime residue
factors `X - 1` and `X + 1` modulo `(3)`. The 3-adic example applies
`HenselianRing.exists_monic_factorization` to obtain monic factors with these
prescribed reductions. Completeness supplies the Henselian-pair instance, and
`3 = 0` in the quotient gives the coprime residue factorization.

The zero ring also admits factor lifting at its top ideal, which equals its
bottom ideal; no properness condition on the ideal is needed.

The independent input over `ZMod 64` has two nonunit leading coefficients,
a nonzero zero-divisor resultant, and a nonzero error in the required ideal.
Its Henselian structure is obtained from the nil ideal, without assuming any
corrected factors or invoking a factor-lifting theorem.
-/

open Polynomial

/-- Lifting the ordered residue factors of `X² - 4` over the 3-adic integers. -/
private theorem padicInt_three_monic_factorization :
    ∃ g h : (PadicInt 3)[X],
      g.Monic ∧ h.Monic ∧ (X ^ 2 - 4 : (PadicInt 3)[X]) = g * h ∧
        g.map (Ideal.Quotient.mk (Ideal.span {(3 : PadicInt 3)})) = X - 1 ∧
        h.map (Ideal.Quotient.mk (Ideal.span {(3 : PadicInt 3)})) = X + 1 := by
  have : HenselianRing (PadicInt 3) (Ideal.span {(3 : PadicInt 3)}) := by
    have hmax : IsLocalRing.maximalIdeal (PadicInt 3) =
        Ideal.span {(3 : PadicInt 3)} := by
      simpa only [Nat.cast_ofNat] using (PadicInt.maximalIdeal_eq_span_p (p := 3))
    rw [← hmax]
    exact IsAdicComplete.henselianRing _ _
  have hquot : (3 : PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)}) = 0 := by
    have hmem : (3 : PadicInt 3) ∈ Ideal.span {(3 : PadicInt 3)} :=
      Ideal.subset_span (by simp)
    simpa only [map_ofNat] using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hthree : (3 : (PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)})[X]) = 0 := by
    simpa only [C_ofNat, map_zero] using congrArg
      (C : (PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)}) →+*
        (PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)})[X]) hquot
  have hcop : IsCoprime
      (X - 1 : (PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)})[X]) (X + 1) := by
    refine ⟨1, -1, ?_⟩
    linear_combination -hthree
  have hfac : (X ^ 2 - 4 : (PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)})[X]) =
      (X - 1) * (X + 1) := by
    linear_combination -hthree
  exact HenselianRing.exists_monic_factorization (Ideal.span {(3 : PadicInt 3)})
    (by simpa only [C_ofNat] using
      (monic_X_pow_sub_C (4 : PadicInt 3) (by decide : (2 : ℕ) ≠ 0)))
    (by simpa using (monic_X_sub_C (1 : PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)})))
    (by simpa using (monic_X_add_C (1 : PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)})))
    hcop (by simpa using hfac)

/-- Factor lifting at the top ideal of the zero ring. -/
private theorem zmod_one_monic_factorization :
    ∃ g h : (ZMod 1)[X],
      g.Monic ∧ h.Monic ∧ (1 : (ZMod 1)[X]) = g * h ∧
        g.map (Ideal.Quotient.mk (⊤ : Ideal (ZMod 1))) = 1 ∧
        h.map (Ideal.Quotient.mk (⊤ : Ideal (ZMod 1))) = 1 := by
  have : HenselianRing (ZMod 1) (⊤ : Ideal (ZMod 1)) :=
    IsAdicComplete.henselianRing (ZMod 1) ⊤
  obtain ⟨g, h, hgm, hhm, _, hgh, hredg, hredh⟩ :=
    Polynomial.exists_monic_factorization_of_isAdicComplete (⊤ : Ideal (ZMod 1))
      monic_one monic_one monic_one isCoprime_one_left (by simp)
  exact ⟨g, h, hgm, hhm, hgh, hredg, hredh⟩


private def zmod64FactorIdeal : Ideal (ZMod 64) := Ideal.span {(2 : ZMod 64)}

private noncomputable def zmod64FactorG : (ZMod 64)[X] := C 2 * X + C 1

private noncomputable def zmod64FactorH : (ZMod 64)[X] := C 2 * X + C 3

private noncomputable def zmod64FactorF : (ZMod 64)[X] :=
  zmod64FactorG * zmod64FactorH + C 32

private theorem zmod64Factor_natDegrees :
    zmod64FactorG.natDegree = 1 ∧ zmod64FactorH.natDegree = 1 := by
  constructor <;> exact natDegree_linear (by decide : (2 : ZMod 64) ≠ 0)

private theorem zmod64Factor_resultant :
    resultant zmod64FactorG zmod64FactorH
      zmod64FactorG.natDegree zmod64FactorH.natDegree = 4 := by
  rw [zmod64Factor_natDegrees.1, zmod64Factor_natDegrees.2]
  rw [resultant, Matrix.det_fin_two]
  norm_num [sylvester, Fin.addCases, zmod64FactorG, zmod64FactorH,
    coeff_X, coeff_C, coeff_one]

private theorem zmod64Factor_error :
    zmod64FactorF - zmod64FactorG * zmod64FactorH = C 32 := by
  simp [zmod64FactorF]

private theorem zmod64Factor_henselian :
    HenselianRing (ZMod 64) zmod64FactorIdeal := by
  apply (HenselianRing.iff_le_henselianRadical zmod64FactorIdeal).mpr
  refine le_trans ?_ (Ideal.nilradical_le_henselianRadical (ZMod 64))
  change Ideal.span {(2 : ZMod 64)} ≤ (⊥ : Ideal (ZMod 64)).radical
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact Ideal.mem_radical_iff.mpr ⟨6, by
    simpa only [Ideal.mem_bot] using (by decide : (2 : ZMod 64) ^ 6 = 0)⟩

/-- A nonvacuous input with nilpotent resultant and nonunit leading coefficients.
All hypotheses are verified directly, independently of any corrected factors. -/
private theorem zmod64_fixed_leading_resultant_input :
    HenselianRing (ZMod 64) zmod64FactorIdeal ∧
      (zmod64FactorF - zmod64FactorG * zmod64FactorH).degree <
        (zmod64FactorG.natDegree + zmod64FactorH.natDegree : WithBot ℕ) ∧
      (∀ i : ℕ, (zmod64FactorF - zmod64FactorG * zmod64FactorH).coeff i ∈
        Ideal.span {resultant zmod64FactorG zmod64FactorH
          zmod64FactorG.natDegree zmod64FactorH.natDegree ^ 2} * zmod64FactorIdeal) ∧
      zmod64FactorG.leadingCoeff = 2 ∧ zmod64FactorH.leadingCoeff = 2 ∧
      ¬ IsUnit (2 : ZMod 64) ∧
      resultant zmod64FactorG zmod64FactorH
        zmod64FactorG.natDegree zmod64FactorH.natDegree = 4 ∧
      ¬ IsUnit (4 : ZMod 64) ∧
      (∃ z : ZMod 64, z ≠ 0 ∧ (4 : ZMod 64) * z = 0) ∧
      zmod64FactorF.coeff 2 = 4 ∧
      zmod64FactorF - zmod64FactorG * zmod64FactorH ≠ 0 := by
  refine ⟨zmod64Factor_henselian, ?_, ?_, ?_, ?_, ?_,
    zmod64Factor_resultant, ?_, ?_, ?_, ?_⟩
  · rw [zmod64Factor_error, zmod64Factor_natDegrees.1, zmod64Factor_natDegrees.2]
    exact lt_of_le_of_lt degree_C_le (by norm_num)
  · have h32 : (32 : ZMod 64) ∈
        Ideal.span {(4 : ZMod 64) ^ 2} * zmod64FactorIdeal := by
      rw [zmod64FactorIdeal, Ideal.span_singleton_mul_span_singleton,
        show (4 : ZMod 64) ^ 2 * 2 = 32 by norm_num]
      exact Ideal.subset_span (by simp)
    intro i
    rw [zmod64Factor_error, zmod64Factor_resultant]
    by_cases hi : i = 0
    · simpa [hi] using h32
    · simp [coeff_C, hi]
  · exact leadingCoeff_linear (by decide : (2 : ZMod 64) ≠ 0)
  · exact leadingCoeff_linear (by decide : (2 : ZMod 64) ≠ 0)
  · simpa only [Nat.cast_ofNat] using
      (not_congr (ZMod.isUnit_iff_coprime 2 64)).mpr (by decide)
  · simpa only [Nat.cast_ofNat] using
      (not_congr (ZMod.isUnit_iff_coprime 4 64)).mpr (by decide)
  · exact ⟨16, by decide, by decide⟩
  · norm_num [zmod64FactorF, zmod64FactorG, zmod64FactorH,
      mul_add, add_mul, mul_assoc, coeff_X_mul, coeff_C_mul, coeff_C, coeff_X, coeff_one]
  · rw [zmod64Factor_error]
    simpa only [ne_eq, C_eq_zero] using (by decide : (32 : ZMod 64) ≠ 0)

/-- The completed criterion factors the independent nonmonic input with its nonzero
nilpotent resultant, retaining the stated strict-degree and ideal precision. -/
private theorem zmod64_fixed_leading_factorization :
    ∃ g h : (ZMod 64)[X], zmod64FactorF = g * h ∧
      (g - zmod64FactorG).degree < (1 : WithBot ℕ) ∧
      (h - zmod64FactorH).degree < (1 : WithBot ℕ) ∧
      ∀ i : ℕ, (g - zmod64FactorG).coeff i ∈
          Ideal.span {(4 : ZMod 64)} * zmod64FactorIdeal ∧
        (h - zmod64FactorH).coeff i ∈
          Ideal.span {(4 : ZMod 64)} * zmod64FactorIdeal := by
  obtain ⟨hH, hdegree, herror, _⟩ := zmod64_fixed_leading_resultant_input
  let : HenselianRing (ZMod 64) zmod64FactorIdeal := hH
  have h := exists_factorization_of_resultant_sq zmod64FactorIdeal hdegree herror
  rw [zmod64Factor_resultant, zmod64Factor_natDegrees.1, zmod64Factor_natDegrees.2] at h
  exact h
