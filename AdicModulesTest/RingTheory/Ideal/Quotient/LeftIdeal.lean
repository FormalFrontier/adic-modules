/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Three pairwise comaximal left ideals of integer matrices

In `Matrix (Fin 2) (Fin 2) ℤ`, the kernels of right multiplication by
`E00`, `E11`, and `E00 + E10` are the left ideals of matrices whose first
column, second column, and column sum, respectively, vanish. All three are
nonzero, proper, idempotent, and not two-sided. Each pair has join top, but
the three congruences with residues `0`, `0`, and `1` have no common solution.
Consequently the canonical diagonal into the three module quotients is not
surjective, even though all positive powers of these ideals are unchanged.

The quotients and their scalar actions are the canonical quotients of the regular
left module. No multiplication on these quotient modules is used. In contrast,
the binary diagonal is surjective and admits the stock linear first isomorphism.

## References

These independent binary and ternary calculations use Mathlib's kernels of
right matrix multiplication, regular-left-module quotients and linear first
isomorphism API. They do not use a ring quotient CRT for arbitrary left ideals.
-/

namespace LeftIdealExamples

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

private abbrev matrixUnit (i j : Fin 2) : Mat := Matrix.single i j 1

private abbrev firstColumnKernel : Ideal Mat :=
  LinearMap.ker (LinearMap.mulRight Mat (matrixUnit 0 0))

private abbrev secondColumnKernel : Ideal Mat :=
  LinearMap.ker (LinearMap.mulRight Mat (matrixUnit 1 1))

private abbrev columnSumKernel : Ideal Mat :=
  LinearMap.ker (LinearMap.mulRight Mat (matrixUnit 0 0 + matrixUnit 1 0))

private abbrev sumProjection : Mat := matrixUnit 0 0 - matrixUnit 0 1

private lemma matrixUnits_mul (i j k l : Fin 2) :
    matrixUnit i j * matrixUnit k l = if j = k then matrixUnit i l else 0 := by
  by_cases h : j = k
  · subst k
    simp [matrixUnit]
  · simp [matrixUnit, h, Matrix.single_mul_single_of_ne]

private lemma matrixUnit_ne_zero (i j : Fin 2) : matrixUnit i j ≠ 0 := by
  intro h
  have hij := congrArg (fun X : Mat => X i j) h
  norm_num [matrixUnit] at hij

private theorem noncommutative : ¬ ∀ X Y : Mat, X * Y = Y * X := by
  intro h
  have h01 := h (matrixUnit 0 1) (matrixUnit 1 0)
  have h00 := congrArg (fun X : Mat => X 0 0) h01
  norm_num [matrixUnits_mul, matrixUnit, Matrix.single_apply] at h00

private lemma mem_firstColumnKernel_iff (X : Mat) :
    X ∈ firstColumnKernel ↔ ∀ r, X r 0 = 0 := by
  change X * matrixUnit 0 0 = 0 ↔ _
  constructor
  · intro h r
    simpa [matrixUnit] using congrArg (fun Y : Mat => Y r 0) h
  · intro h
    ext r c
    fin_cases c
    · simpa [matrixUnit] using h r
    · simp [matrixUnit, Matrix.mul_single_apply_of_ne]

private lemma mem_secondColumnKernel_iff (X : Mat) :
    X ∈ secondColumnKernel ↔ ∀ r, X r 1 = 0 := by
  change X * matrixUnit 1 1 = 0 ↔ _
  constructor
  · intro h r
    simpa [matrixUnit] using congrArg (fun Y : Mat => Y r 1) h
  · intro h
    ext r c
    fin_cases c
    · simp [matrixUnit, Matrix.mul_single_apply_of_ne]
    · simpa [matrixUnit] using h r

private lemma mem_columnSumKernel_iff (X : Mat) :
    X ∈ columnSumKernel ↔ ∀ r, X r 0 + X r 1 = 0 := by
  change X * (matrixUnit 0 0 + matrixUnit 1 0) = 0 ↔ _
  constructor
  · intro h r
    simpa [matrixUnit, mul_add, Matrix.add_apply] using
      congrArg (fun Y : Mat => Y r 0) h
  · intro h
    ext r c
    fin_cases c
    · simpa [matrixUnit, mul_add, Matrix.add_apply] using h r
    · simp [matrixUnit, mul_add, Matrix.add_apply, Matrix.mul_single_apply_of_ne]

private lemma firstProjection_mem : matrixUnit 1 1 ∈ firstColumnKernel := by
  apply (mem_firstColumnKernel_iff _).mpr
  intro r
  simp [matrixUnit]

private lemma secondProjection_mem : matrixUnit 0 0 ∈ secondColumnKernel := by
  apply (mem_secondColumnKernel_iff _).mpr
  intro r
  simp [matrixUnit]

private lemma sumProjection_mem : sumProjection ∈ columnSumKernel := by
  apply (mem_columnSumKernel_iff _).mpr
  intro r
  fin_cases r <;> norm_num [sumProjection, matrixUnit, Matrix.single_apply]

private lemma sumProjection_ne_zero : sumProjection ≠ 0 := by
  intro h
  have h00 := congrArg (fun X : Mat => X 0 0) h
  norm_num [sumProjection, matrixUnit] at h00

private theorem firstColumnKernel_nonzero_proper :
    firstColumnKernel ≠ ⊥ ∧ firstColumnKernel ≠ ⊤ := by
  constructor
  · exact firstColumnKernel.ne_bot_iff.mpr
      ⟨matrixUnit 1 1, firstProjection_mem, matrixUnit_ne_zero 1 1⟩
  · apply (Ideal.ne_top_iff_one _).mpr
    intro h
    have h00 := (mem_firstColumnKernel_iff _).mp h 0
    norm_num at h00

private theorem secondColumnKernel_nonzero_proper :
    secondColumnKernel ≠ ⊥ ∧ secondColumnKernel ≠ ⊤ := by
  constructor
  · exact secondColumnKernel.ne_bot_iff.mpr
      ⟨matrixUnit 0 0, secondProjection_mem, matrixUnit_ne_zero 0 0⟩
  · apply (Ideal.ne_top_iff_one _).mpr
    intro h
    have h11 := (mem_secondColumnKernel_iff _).mp h 1
    norm_num at h11

private theorem columnSumKernel_nonzero_proper :
    columnSumKernel ≠ ⊥ ∧ columnSumKernel ≠ ⊤ := by
  constructor
  · exact columnSumKernel.ne_bot_iff.mpr
      ⟨sumProjection, sumProjection_mem, sumProjection_ne_zero⟩
  · apply (Ideal.ne_top_iff_one _).mpr
    intro h
    have h00 := (mem_columnSumKernel_iff _).mp h 0
    norm_num at h00

private theorem first_second_sup : firstColumnKernel ⊔ secondColumnKernel = ⊤ := by
  apply top_unique
  intro X _
  apply Submodule.mem_sup.mpr
  refine ⟨Matrix.of (fun r c => if c = 0 then 0 else X r 1), ?_,
    Matrix.of (fun r c => if c = 0 then X r 0 else 0), ?_, ?_⟩
  · apply (mem_firstColumnKernel_iff _).mpr
    intro r
    simp
  · apply (mem_secondColumnKernel_iff _).mpr
    intro r
    simp
  · ext r c
    fin_cases c <;> simp [Matrix.of_apply, Matrix.add_apply]

private theorem first_sum_sup : firstColumnKernel ⊔ columnSumKernel = ⊤ := by
  apply top_unique
  intro X _
  apply Submodule.mem_sup.mpr
  refine ⟨Matrix.of (fun r c => if c = 0 then 0 else X r 1 + X r 0), ?_,
    Matrix.of (fun r c => if c = 0 then X r 0 else -X r 0), ?_, ?_⟩
  · apply (mem_firstColumnKernel_iff _).mpr
    intro r
    simp
  · apply (mem_columnSumKernel_iff _).mpr
    intro r
    simp
  · ext r c
    fin_cases c <;> simp [Matrix.of_apply, Matrix.add_apply, add_assoc]

private theorem second_sum_sup : secondColumnKernel ⊔ columnSumKernel = ⊤ := by
  apply top_unique
  intro X _
  apply Submodule.mem_sup.mpr
  refine ⟨Matrix.of (fun r c => if c = 0 then X r 0 + X r 1 else 0), ?_,
    Matrix.of (fun r c => if c = 0 then -X r 1 else X r 1), ?_, ?_⟩
  · apply (mem_secondColumnKernel_iff _).mpr
    intro r
    simp
  · apply (mem_columnSumKernel_iff _).mpr
    intro r
    simp
  · ext r c
    fin_cases c <;> simp [Matrix.of_apply, Matrix.add_apply, add_assoc]

private lemma eq_zero_of_mem_first_second {X : Mat}
    (h₁ : X ∈ firstColumnKernel) (h₂ : X ∈ secondColumnKernel) : X = 0 := by
  have hfirst := (mem_firstColumnKernel_iff _).mp h₁
  have hsecond := (mem_secondColumnKernel_iff _).mp h₂
  ext r c
  fin_cases c
  · exact hfirst r
  · exact hsecond r

private theorem first_second_inf : firstColumnKernel ⊓ secondColumnKernel = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro X h
  exact eq_zero_of_mem_first_second h.1 h.2

private theorem no_simultaneous_representative :
    ¬ ∃ X : Mat, X ∈ firstColumnKernel ∧ X ∈ secondColumnKernel ∧
      X - 1 ∈ columnSumKernel := by
  rintro ⟨X, h₁, h₂, hv⟩
  have hX := eq_zero_of_mem_first_second h₁ h₂
  subst X
  have h00 := (mem_columnSumKernel_iff _).mp hv 0
  norm_num at h00

private lemma first_projection_fixes {X : Mat} (hX : X ∈ firstColumnKernel) :
    X * matrixUnit 1 1 = X := by
  have h := (mem_firstColumnKernel_iff _).mp hX
  ext r c
  fin_cases c
  · simp [matrixUnit, Matrix.mul_single_apply_of_ne, h r]
  · simp [matrixUnit]

private lemma second_projection_fixes {X : Mat} (hX : X ∈ secondColumnKernel) :
    X * matrixUnit 0 0 = X := by
  have h := (mem_secondColumnKernel_iff _).mp hX
  ext r c
  fin_cases c
  · simp [matrixUnit]
  · simp [matrixUnit, Matrix.mul_single_apply_of_ne, h r]

private lemma sum_projection_fixes {X : Mat} (hX : X ∈ columnSumKernel) :
    X * sumProjection = X := by
  have h := (mem_columnSumKernel_iff _).mp hX
  ext r c
  fin_cases c
  · simp [sumProjection, matrixUnit, mul_sub, Matrix.sub_apply,
      Matrix.mul_single_apply_of_ne]
  · have hr : -X r 0 = X r 1 := by
      calc
        -X r 0 = -X r 0 + 0 := (add_zero _).symm
        _ = -X r 0 + (X r 0 + X r 1) := by rw [h r]
        _ = X r 1 := by simp [← add_assoc]
    simpa [sumProjection, matrixUnit, mul_sub, Matrix.sub_apply,
      Matrix.mul_single_apply_of_ne] using hr

private theorem firstColumnKernel_idempotent :
    firstColumnKernel * firstColumnKernel = firstColumnKernel := by
  apply le_antisymm Ideal.mul_le_right
  intro X hX
  simpa only [first_projection_fixes hX] using Ideal.mul_mem_mul hX firstProjection_mem

private theorem secondColumnKernel_idempotent :
    secondColumnKernel * secondColumnKernel = secondColumnKernel := by
  apply le_antisymm Ideal.mul_le_right
  intro X hX
  simpa only [second_projection_fixes hX] using Ideal.mul_mem_mul hX secondProjection_mem

private theorem columnSumKernel_idempotent :
    columnSumKernel * columnSumKernel = columnSumKernel := by
  apply le_antisymm Ideal.mul_le_right
  intro X hX
  simpa only [sum_projection_fixes hX] using Ideal.mul_mem_mul hX sumProjection_mem

private theorem firstColumnKernel_not_twoSided : ¬ firstColumnKernel.IsTwoSided := by
  intro h
  have hm := firstColumnKernel.mul_mem_right (matrixUnit 1 0) firstProjection_mem
  have h10 := (mem_firstColumnKernel_iff _).mp hm 1
  norm_num [matrixUnits_mul, matrixUnit, Matrix.single_apply] at h10

private theorem secondColumnKernel_not_twoSided : ¬ secondColumnKernel.IsTwoSided := by
  intro h
  have hm := secondColumnKernel.mul_mem_right (matrixUnit 0 1) secondProjection_mem
  have h01 := (mem_secondColumnKernel_iff _).mp hm 0
  norm_num [matrixUnits_mul, matrixUnit, Matrix.single_apply] at h01

private theorem columnSumKernel_not_twoSided : ¬ columnSumKernel.IsTwoSided := by
  intro h
  have hm := columnSumKernel.mul_mem_right (matrixUnit 0 0) sumProjection_mem
  have h00 := (mem_columnSumKernel_iff _).mp hm 0
  norm_num [sumProjection, sub_mul, matrixUnits_mul, matrixUnit, Matrix.single_apply] at h00

private abbrev ideals (i : Fin 3) : Ideal Mat :=
  if i = 0 then firstColumnKernel else if i = 1 then secondColumnKernel else columnSumKernel

private theorem ideals_nonzero_proper (i : Fin 3) : ideals i ≠ ⊥ ∧ ideals i ≠ ⊤ := by
  fin_cases i
  · simpa [ideals] using firstColumnKernel_nonzero_proper
  · simpa [ideals] using secondColumnKernel_nonzero_proper
  · simpa [ideals] using columnSumKernel_nonzero_proper

private theorem ideals_pairwise_sup :
    Pairwise (fun i j : Fin 3 => ideals i ⊔ ideals j = ⊤) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simpa [ideals] using first_second_sup
  · simpa [ideals] using first_sum_sup
  · simpa [ideals, sup_comm] using first_second_sup
  · exact (hij rfl).elim
  · simpa [ideals] using second_sum_sup
  · simpa [ideals, sup_comm] using first_sum_sup
  · simpa [ideals, sup_comm] using second_sum_sup
  · exact (hij rfl).elim

private theorem ideals_idempotent (i : Fin 3) : ideals i * ideals i = ideals i := by
  fin_cases i
  · simpa [ideals] using firstColumnKernel_idempotent
  · simpa [ideals] using secondColumnKernel_idempotent
  · simpa [ideals] using columnSumKernel_idempotent

private theorem ideals_pow_succ (i : Fin 3) (n : ℕ) : ideals i ^ (n + 1) = ideals i := by
  induction n with
  | zero => exact Submodule.pow_one _
  | succ n ih => rw [Submodule.pow_succ, ih, ideals_idempotent]

private theorem ideals_positive_powers (i : Fin 3) {n : ℕ} (hn : n ≠ 0) :
    ideals i ^ n = ideals i := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n => exact ideals_pow_succ i n

private theorem ideals_pow_zero (i : Fin 3) : ideals i ^ 0 = ⊤ := by
  rw [Submodule.pow_zero, Ideal.one_eq_top]

private theorem no_simultaneous_positive_power_representative
    {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ¬ ∃ X : Mat, X ∈ ideals 0 ^ a ∧ X ∈ ideals 1 ^ b ∧ X - 1 ∈ ideals 2 ^ c := by
  rw [ideals_positive_powers 0 ha, ideals_positive_powers 1 hb, ideals_positive_powers 2 hc]
  simpa [ideals] using no_simultaneous_representative

private theorem diagonal_not_surjective :
    ¬ Function.Surjective (LinearMap.pi (fun i : Fin 3 => (ideals i).mkQ)) := by
  intro hs
  let y : ∀ i : Fin 3, Mat ⧸ ideals i :=
    fun i => (ideals i).mkQ (if i = 2 then 1 else 0)
  obtain ⟨X, hX⟩ := hs y
  have h₁ : X ∈ firstColumnKernel := by
    simpa [LinearMap.pi_apply, ideals, y, Submodule.mkQ_apply] using
      congrArg (fun q : ∀ i : Fin 3, Mat ⧸ ideals i => q 0) hX
  have h₂ : X ∈ secondColumnKernel := by
    simpa [LinearMap.pi_apply, ideals, y, Submodule.mkQ_apply] using
      congrArg (fun q : ∀ i : Fin 3, Mat ⧸ ideals i => q 1) hX
  have hv : (Submodule.Quotient.mk X : Mat ⧸ columnSumKernel) =
      Submodule.Quotient.mk (1 : Mat) := by
    simpa [LinearMap.pi_apply, ideals, y, Submodule.mkQ_apply] using
      congrArg (fun q : ∀ i : Fin 3, Mat ⧸ ideals i => q 2) hX
  exact no_simultaneous_representative
    ⟨X, h₁, h₂, (Submodule.Quotient.eq columnSumKernel).mp hv⟩

private theorem binary_diagonal_surjective :
    Function.Surjective (firstColumnKernel.mkQ.prod secondColumnKernel.mkQ) := by
  apply LinearMap.range_eq_top.mp
  rw [LinearMap.range_prod_eq (f := firstColumnKernel.mkQ) (g := secondColumnKernel.mkQ)
    (by simpa only [Submodule.ker_mkQ] using first_second_sup)]
  simp only [Submodule.range_mkQ]
  ext z
  simp

private theorem binary_first_isomorphism :
    Nonempty ((Mat ⧸ LinearMap.ker (firstColumnKernel.mkQ.prod secondColumnKernel.mkQ)) ≃ₗ[Mat]
      (Mat ⧸ firstColumnKernel) × (Mat ⧸ secondColumnKernel)) := by
  exact ⟨LinearMap.quotKerEquivOfSurjective _ binary_diagonal_surjective⟩

private theorem three_pairwise_comaximal_counterexample :
    (∀ i : Fin 3, ideals i ≠ ⊥ ∧ ideals i ≠ ⊤) ∧
      Pairwise (fun i j : Fin 3 => ideals i ⊔ ideals j = ⊤) ∧
      (∀ (i : Fin 3) (n : ℕ), n ≠ 0 → ideals i ^ n = ideals i) ∧
      ¬ Function.Surjective (LinearMap.pi (fun i : Fin 3 => (ideals i).mkQ)) := by
  exact ⟨ideals_nonzero_proper, ideals_pairwise_sup,
    fun i _ hn => ideals_positive_powers i hn, diagonal_not_surjective⟩

end LeftIdealExamples
