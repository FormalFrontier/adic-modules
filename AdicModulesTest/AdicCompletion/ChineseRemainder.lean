/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.AdicCompletion.ChineseRemainderIdempotents
import Mathlib.Tactic.NormNum.IsCoprime

/-!
# The (2), (3), (6) decomposition over the integers

The diagonal image of 3 is not the completed pair (1, 0). That pair instead has
inverse residues 3 modulo 6 and 9 modulo 36. Thus its first-power residue does
not describe its higher-precision data.

The inverse pair is the completed coordinate idempotent for the (2) factor.
It is neither zero nor one, and it is not the completed integer 3.
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

private def selector : AdicCompletion productIdeal ℤ :=
  comaximalIdempotent ℤ ideals Finset.univ comaximal ⟨false, Finset.mem_univ _⟩

/-- The multiplicative selector is the same inverse pair whose two residues
were computed above, using the algebra equivalence's underlying linear map. -/
private theorem selector_eq_inverse_pair : selector = decomposition.symm pair := by
  apply decomposition.injective
  rw [LinearEquiv.apply_symm_apply]
  change equivPiOfPairwiseSupEqTop ℤ ideals Finset.univ comaximal selector = pair
  rw [← algEquivPiOfPairwiseSupEqTop_toLinearEquiv]
  change algEquivPiOfPairwiseSupEqTop ℤ ideals Finset.univ comaximal selector = pair
  funext i
  rw [algEquivPiOfPairwiseSupEqTop_apply]
  rcases i with ⟨b, hb⟩
  cases b
  · change mapOfLEₐ ℤ _ selector = 1
    exact mapOfLEₐ_comaximalIdempotent_same ℤ ideals Finset.univ comaximal
      ⟨false, Finset.mem_univ _⟩
  · change mapOfLEₐ ℤ _ selector = 0
    exact mapOfLEₐ_comaximalIdempotent_of_ne ℤ ideals Finset.univ comaximal
      ⟨false, Finset.mem_univ _⟩ ⟨true, Finset.mem_univ _⟩ (by decide)

/-- The completed selector is a genuine nonendpoint idempotent, not the
completed integer 3. Its residues are 3 modulo 6 and 9 modulo 36, as computed
for the inverse pair above. Its endpoints are distinguished in the first
quotients of the (2) and (3) factors, without extra completion hypotheses. -/
private theorem selector_isIdempotent_nonendpoint :
    IsIdempotentElem selector ∧ selector ≠ 0 ∧ selector ≠ 1 ∧
      selector ≠ of productIdeal ℤ 3 ∧
      (eval productIdeal ℤ 1 selector = Submodule.Quotient.mk 3 ∧
        eval productIdeal ℤ 2 selector = Submodule.Quotient.mk 9) := by
  refine ⟨(completeOrthogonalIdempotents_comaximalIdempotent
    ℤ ideals Finset.univ comaximal).idem ⟨false, Finset.mem_univ _⟩, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hcomponent := mapOfLEₐ_comaximalIdempotent_same
      ℤ ideals Finset.univ comaximal ⟨false, Finset.mem_univ _⟩
    change mapOfLEₐ ℤ _ selector = 1 at hcomponent
    rw [hzero, _root_.map_zero] at hcomponent
    have hres := congrArg (eval (ideals false) ℤ 1) hcomponent
    have hbad : ¬ (2 : ℤ) ^ 1 ∣ 0 - 1 := by norm_num
    exact hbad ((residue_eq_iff false 1 0 1).mp hres)
  · intro hone
    have hcomponent := mapOfLEₐ_comaximalIdempotent_of_ne
      ℤ ideals Finset.univ comaximal
      ⟨false, Finset.mem_univ _⟩ ⟨true, Finset.mem_univ _⟩ (by decide)
    change mapOfLEₐ ℤ _ selector = 0 at hcomponent
    rw [hone, map_one] at hcomponent
    have hres := congrArg (eval (ideals true) ℤ 1) hcomponent
    have hbad : ¬ (3 : ℤ) ^ 1 ∣ 1 - 0 := by norm_num
    exact hbad ((residue_eq_iff true 1 1 0).mp hres)
  · intro hthree
    apply completed_three_ne_pair
    rw [← hthree, selector_eq_inverse_pair, LinearEquiv.apply_symm_apply]
  · simpa only [selector_eq_inverse_pair] using inverse_pair_stages
