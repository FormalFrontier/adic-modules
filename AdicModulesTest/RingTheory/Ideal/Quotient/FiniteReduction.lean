/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.Ideal.Quotient.Finite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Reduction of a fixed integer Chinese remainder class

The class of `8` for the squares of the span ideals at `2` and `3` has
coordinates `0` modulo `4` and `8` modulo `9`. The public forward reduction
square sends these coordinates to `0` modulo `2` and `2` modulo `3`, and the
inverse square reduces their inverse class to the class of `8`. A mixed coarse
precision of `0` and `1` includes the genuine modulus `2 ^ 0 = 1` and its
trivial quotient.

## References

The forward and inverse precision-reduction squares come from
`AdicModules.RingTheory.Ideal.Quotient.Finite`, using Mathlib's canonical quotient
factors and integer residues, including the trivial zeroth-power quotient.
-/

namespace Ideal

private def moduli : Fin 2 → ℤ := ![2, 3]
private def fineResidues : Fin 2 → ℤ := ![0, 8]
private def coarseResidues : Fin 2 → ℤ := ![0, 2]
private def integerIdeals (i : Fin 2) : Ideal ℤ := Ideal.span {moduli i}

private theorem pairwise_sup :
    Pairwise (fun i j => integerIdeals i ⊔ integerIdeals j = ⊤) := by
  intro i j hij
  apply Ideal.isCoprime_iff_sup_eq.mp
  apply (Ideal.isCoprime_span_singleton_iff (moduli i) (moduli j)).mpr
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact ⟨-1, 1, by norm_num [moduli]⟩
  · exact ⟨1, -1, by norm_num [moduli]⟩
  · exact (hij rfl).elim

private theorem forward_fine_eight :
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop (fun i => integerIdeals i ^ 2)
        (pairwise_sup_eq_top_pow integerIdeals pairwise_sup (fun _ => 2))
        (Quotient.mk (⨅ i, integerIdeals i ^ 2) 8) =
      fun i => Quotient.mk (integerIdeals i ^ 2) (fineResidues i) := by
  rw [quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_mk]
  funext i
  apply (Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [integerIdeals, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  fin_cases i <;> norm_num [moduli, fineResidues]

private theorem forward_coarse_eight :
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop (fun i => integerIdeals i ^ 1)
        (pairwise_sup_eq_top_pow integerIdeals pairwise_sup (fun _ => 1))
        (Quotient.mk (⨅ i, integerIdeals i ^ 1) 8) =
      fun i => Quotient.mk (integerIdeals i ^ 1) (coarseResidues i) := by
  rw [quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_mk]
  funext i
  apply (Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [integerIdeals, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  fin_cases i <;> norm_num [moduli, coarseResidues]

private theorem forward_reduction_eight :
    (fun i => Quotient.factor (pow_le_pow_right (I := integerIdeals i) (Nat.le_succ 1))
      (Quotient.mk (integerIdeals i ^ 2) (fineResidues i))) =
      fun i => Quotient.mk (integerIdeals i ^ 1) (coarseResidues i) := by
  have h := congrFun
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_pow_comp_factor
      integerIdeals pairwise_sup (fun _ => 1) (fun _ => 2) (fun _ => Nat.le_succ 1))
    (Quotient.mk (⨅ i, integerIdeals i ^ 2) 8)
  simpa only [Function.comp_apply, Quotient.factor_mk, forward_fine_eight,
    forward_coarse_eight] using h.symm

private theorem inverse_reduction_eight :
    Quotient.factor
        (iInf_mono (fun i => pow_le_pow_right (I := integerIdeals i) (Nat.le_succ 1)))
        ((quotientInfRingEquivPiQuotientOfPairwiseSupEqTop
          (fun i => integerIdeals i ^ 2)
          (pairwise_sup_eq_top_pow integerIdeals pairwise_sup (fun _ => 2))).symm
          (fun i => Quotient.mk (integerIdeals i ^ 2) (fineResidues i))) =
      Quotient.mk (⨅ i, integerIdeals i ^ 1) 8 := by
  rw [quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_pow_factor_symm_apply
    integerIdeals pairwise_sup (fun _ => 1) (fun _ => 2) (fun _ => Nat.le_succ 1),
    forward_reduction_eight]
  apply (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop
    (fun i => integerIdeals i ^ 1)
    (pairwise_sup_eq_top_pow integerIdeals pairwise_sup (fun _ => 1))).injective
  rw [RingEquiv.apply_symm_apply, forward_coarse_eight]

private theorem mixed_le (i : Fin 2) : (![0, 1] : Fin 2 → ℕ) i ≤ 2 := by
  fin_cases i <;> norm_num

private theorem mixed_zero_reduction_eight :
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop
        (fun i => integerIdeals i ^ (![0, 1] : Fin 2 → ℕ) i)
        (pairwise_sup_eq_top_pow integerIdeals pairwise_sup ![0, 1])
        (Quotient.factor
          (iInf_mono (fun i => pow_le_pow_right (I := integerIdeals i) (mixed_le i)))
          (Quotient.mk (⨅ i, integerIdeals i ^ 2) 8)) 0 = 0 := by
  rw [quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_pow_factor_apply_apply
    integerIdeals pairwise_sup ![0, 1] (fun _ => 2) mixed_le,
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_mk_apply, Quotient.factor_mk]
  apply Quotient.eq_zero_iff_mem.mpr
  change (8 : ℤ) ∈ Ideal.span {(2 : ℤ)} ^ 0
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  norm_num

private theorem zero_precision_trivial : Subsingleton (ℤ ⧸ integerIdeals 0 ^ 0) :=
  Quotient.subsingleton_iff.mpr (by simp)

end Ideal
