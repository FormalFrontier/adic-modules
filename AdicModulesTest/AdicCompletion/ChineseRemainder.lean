/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.AdicCompletion.ChineseRemainder
import Mathlib.Tactic.NormNum.IsCoprime

/-!
# The (2), (3), (6) decomposition over the integers

The diagonal image of 3 is not the completed pair (1, 0). That pair instead has
inverse residues 3 modulo 6 and 9 modulo 36. Thus its first-power residue does
not describe its higher-precision data.
-/

noncomputable section

open AdicCompletion

private def ideals (b : Bool) : Ideal ℤ := Ideal.span {if b then 3 else 2}

private theorem comaximal :
    (↑(Finset.univ : Finset Bool) : Set Bool).Pairwise (fun i j => ideals i ⊔ ideals j = ⊤) := by
  intro i _ j _ hij
  apply Ideal.isCoprime_iff_sup_eq.mp
  cases i <;> cases j <;> try contradiction
  all_goals
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    norm_num

private abbrev productIdeal := ∏ b : Bool, ideals b

private theorem product_eq_six : productIdeal = Ideal.span {(6 : ℤ)} := by
  norm_num [productIdeal, Fintype.prod_bool, ideals, Ideal.span_singleton_mul_span_singleton]

private def decomposition :
    AdicCompletion productIdeal ℤ ≃ₗ[ℤ]
      ((i : (Finset.univ : Finset Bool)) → AdicCompletion (ideals i.1) ℤ) :=
  equivPiOfPairwiseSupEqTop ℤ ideals Finset.univ comaximal

private def pair (i : (Finset.univ : Finset Bool)) : AdicCompletion (ideals i.1) ℤ :=
  of (ideals i.1) ℤ (if i.1 then 0 else 1)

private theorem residue_eq_iff (b : Bool) (n : ℕ) (a c : ℤ) :
    (Submodule.Quotient.mk a : ℤ ⧸ (ideals b ^ n • (⊤ : Submodule ℤ ℤ))) =
        Submodule.Quotient.mk c ↔ (if b then (3 : ℤ) else 2) ^ n ∣ a - c := by
  rw [Submodule.Quotient.eq]
  change a - c ∈ (ideals b ^ n • (⊤ : Ideal ℤ)) ↔ _
  rw [Ideal.smul_eq_mul, Ideal.mul_top, ideals, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

/-- The canonical diagonal formula holds for every integer, with product ideal (6). -/
private theorem diagonal (a : ℤ) :
    productIdeal = Ideal.span {(6 : ℤ)} ∧
      decomposition (of productIdeal ℤ a) =
        fun i : (Finset.univ : Finset Bool) => of (ideals i.1) ℤ a :=
  ⟨product_eq_six, equivPiOfPairwiseSupEqTop_of ℤ ideals Finset.univ comaximal a⟩

/-- Precision two already distinguishes completed 3 from the completed pair (1, 0):
its coordinates are 3 modulo 4 and 3 modulo 9. -/
private theorem completed_three_ne_pair : decomposition (of productIdeal ℤ 3) ≠ pair := by
  intro h
  have htwo := congrArg (fun y : (i : (Finset.univ : Finset Bool)) →
      AdicCompletion (ideals i.1) ℤ =>
    eval (ideals false) ℤ 2 (y ⟨false, Finset.mem_univ _⟩)) h
  rw [(diagonal 3).2] at htwo
  have hbad : ¬ (2 : ℤ) ^ 2 ∣ 3 - 1 := by norm_num
  apply hbad
  apply (residue_eq_iff false 2 3 1).mp
  exact htwo

/-- The inverse completed pair has residues 3 modulo 6 and 9 modulo 36, not
constant residue 3 at all precisions. -/
private theorem inverse_pair_stages :
    eval productIdeal ℤ 1 (decomposition.symm pair) = Submodule.Quotient.mk 3 ∧
      eval productIdeal ℤ 2 (decomposition.symm pair) = Submodule.Quotient.mk 9 := by
  constructor
  · apply (equivPiOfPairwiseSupEqTop_symm_eval_eq_mk_iff
      ℤ ideals Finset.univ comaximal pair 1 3).mpr
    intro i
    change eval (ideals i.1) ℤ 1 (of (ideals i.1) ℤ (if i.1 then 0 else 1)) = _
    rw [eval_of]
    apply (residue_eq_iff i.1 1 _ 3).mpr
    rcases i with ⟨b, hb⟩
    cases b <;> norm_num
  · apply (equivPiOfPairwiseSupEqTop_symm_eval_eq_mk_iff
      ℤ ideals Finset.univ comaximal pair 2 9).mpr
    intro i
    change eval (ideals i.1) ℤ 2 (of (ideals i.1) ℤ (if i.1 then 0 else 1)) = _
    rw [eval_of]
    apply (residue_eq_iff i.1 2 _ 9).mpr
    rcases i with ⟨b, hb⟩
    cases b <;> norm_num
