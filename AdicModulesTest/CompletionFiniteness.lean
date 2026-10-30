/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import AdicModules.AdicCompletion.TensorProduct

/-!
# An integer-rational product for algebraic adic completion

The first adic quotient and the algebraic adic completion of an integer-rational
product can be finitely generated even when the original module is not.

## Limitations

The finite-first-quotient theorem describes raw algebraic adic completion for
arbitrary ideals. It asserts neither intrinsic completeness nor existence of a
completion in a stronger sense; finite generation of the ideal can be needed for
such existence results. The integer-rational product applies this theorem to a
nonzero example with nonfinite original module, using the canonical action of
the completed ring.

## References

The quotient and completion constructions are Mathlib's. The finite-first-quotient
theorem is provided by `AdicModules.AdicCompletion.TensorProduct`.
-/

@[expose] public section

open scoped Pointwise

namespace AdicCompletion

private def ratDenominatorSubmodule (D : ℕ) : Submodule ℤ ℚ :=
  ({ carrier := {q | q.den ∣ D}
     zero_mem' := by
       change (0 : ℚ).den ∣ D
       rw [Rat.den_zero]
       exact one_dvd D
     add_mem' := by
       intro q r hq hr
       change q.den ∣ D at hq
       change r.den ∣ D at hr
       change (q + r).den ∣ D
       exact (Rat.add_den_dvd_lcm q r).trans (lcm_dvd hq hr)
     neg_mem' := by
       intro q hq
       change (-q).den ∣ D
       rw [Rat.den_neg_eq_den]
       exact hq } : AddSubgroup ℚ).toIntSubmodule

private lemma mem_ratDenominatorSubmodule (D : ℕ) (q : ℚ) :
    q ∈ ratDenominatorSubmodule D ↔ q.den ∣ D :=
  Iff.rfl

private lemma not_finite_rat : ¬ Module.Finite ℤ ℚ := by
  intro h
  rcases Module.finite_def.mp h with ⟨s, hs⟩
  let D : ℕ := s.prod Rat.den
  have hD : 0 < D := Finset.prod_pos fun q _ => Rat.pos q
  have hspan : Submodule.span ℤ (s : Set ℚ) ≤ ratDenominatorSubmodule D := by
    apply Submodule.span_le.mpr
    intro q hq
    apply (mem_ratDenominatorSubmodule D q).mpr
    exact Finset.dvd_prod_of_mem Rat.den hq
  have hall (q : ℚ) : q.den ∣ D := by
    apply (mem_ratDenominatorSubmodule D q).mp
    apply hspan
    rw [hs]
    trivial
  have hinv := hall (((D + 1 : ℕ) : ℚ)⁻¹)
  rw [Rat.inv_natCast_den_of_pos (Nat.succ_pos D)] at hinv
  exact (Nat.lt_succ_self D).not_ge (Nat.le_of_dvd hD hinv)

private lemma not_finite_integer_rational_product : ¬ Module.Finite ℤ (ℤ × ℚ) := by
  intro h
  let : Module.Finite ℤ (ℤ × ℚ) := h
  exact not_finite_rat
    (Module.Finite.of_surjective
      (LinearMap.snd ℤ ℤ ℚ) (fun q => ⟨(0, q), rfl⟩))

private lemma integer_rational_product_mod_two_inl_surjective :
    Function.Surjective
      (((Ideal.span ({(2 : ℤ)} : Set ℤ)) •
        (⊤ : Submodule ℤ (ℤ × ℚ))).mkQ ∘ₗ LinearMap.inl ℤ ℤ ℚ) := by
  let I : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  let P : Submodule ℤ (ℤ × ℚ) := I • ⊤
  change Function.Surjective (P.mkQ ∘ₗ LinearMap.inl ℤ ℤ ℚ)
  intro y
  obtain ⟨⟨a, b⟩, rfl⟩ := P.mkQ_surjective y
  have htwo : (2 : ℤ) ∈ I := Ideal.subset_span (by simp)
  have hdiff : ((a, b) - (a, 0) : ℤ × ℚ) ∈ P := by
    have heq : ((a, b) - (a, 0) : ℤ × ℚ) =
        (2 : ℤ) • ((0 : ℤ), b / 2) := by
      simp only [two_smul]
      ext <;> simp
    rw [heq]
    exact Submodule.smul_mem_smul htwo Submodule.mem_top
  refine ⟨a, ?_⟩
  change P.mkQ (a, 0) = P.mkQ (a, b)
  exact ((Submodule.Quotient.eq P).2 hdiff).symm

private lemma integer_rational_product_quotient_finite :
    Module.Finite ℤ
      ((ℤ × ℚ) ⧸ ((Ideal.span ({(2 : ℤ)} : Set ℤ)) •
        (⊤ : Submodule ℤ (ℤ × ℚ)))) := by
  exact Module.Finite.of_surjective
    (((Ideal.span ({(2 : ℤ)} : Set ℤ)) •
      (⊤ : Submodule ℤ (ℤ × ℚ))).mkQ ∘ₗ LinearMap.inl ℤ ℤ ℚ)
    integer_rational_product_mod_two_inl_surjective

private lemma integer_rational_product_quotient_one_ne_zero :
    (((Ideal.span ({(2 : ℤ)} : Set ℤ)) •
      (⊤ : Submodule ℤ (ℤ × ℚ))).mkQ ((1 : ℤ), (0 : ℚ))) ≠ 0 := by
  let I : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  let P : Submodule ℤ (ℤ × ℚ) := I • ⊤
  change P.mkQ ((1 : ℤ), (0 : ℚ)) ≠ 0
  intro h
  have hp : ((1 : ℤ), (0 : ℚ)) ∈ P :=
    (Submodule.Quotient.mk_eq_zero P).1 h
  have hf : (1 : ℤ) ∈ I • (⊤ : Submodule ℤ ℤ) :=
    (Submodule.smul_top_le_comap_smul_top I (LinearMap.fst ℤ ℤ ℚ)) hp
  have hi : (1 : ℤ) ∈ I := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hf
  have hd : (2 : ℤ) ∣ 1 := Ideal.mem_span_singleton.1 hi
  norm_num at hd

private lemma integer_rational_product_quotient_nontrivial :
    Nontrivial
      ((ℤ × ℚ) ⧸ ((Ideal.span ({(2 : ℤ)} : Set ℤ)) •
        (⊤ : Submodule ℤ (ℤ × ℚ)))) := by
  exact ⟨⟨(((Ideal.span ({(2 : ℤ)} : Set ℤ)) •
    (⊤ : Submodule ℤ (ℤ × ℚ))).mkQ ((1 : ℤ), (0 : ℚ))),
    0, integer_rational_product_quotient_one_ne_zero⟩⟩

private lemma integer_rational_product_completion_finite :
    Module.Finite
      (AdicCompletion (Ideal.span ({(2 : ℤ)} : Set ℤ)) ℤ)
      (AdicCompletion (Ideal.span ({(2 : ℤ)} : Set ℤ)) (ℤ × ℚ)) := by
  let := integer_rational_product_quotient_finite
  exact moduleFinite_of_finite_quotient _ (ℤ × ℚ)

private lemma integer_rational_product_completion_nontrivial :
    Nontrivial
      (AdicCompletion (Ideal.span ({(2 : ℤ)} : Set ℤ)) (ℤ × ℚ)) := by
  let I : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  refine ⟨⟨AdicCompletion.of I (ℤ × ℚ) ((1 : ℤ), (0 : ℚ)), 0, ?_⟩⟩
  intro h
  have he := congrArg (AdicCompletion.eval I (ℤ × ℚ) 1) h
  rw [AdicCompletion.eval_of] at he
  change ((I ^ 1 • ⊤ : Submodule ℤ (ℤ × ℚ)).mkQ
    ((1 : ℤ), (0 : ℚ))) = 0 at he
  apply integer_rational_product_quotient_one_ne_zero
  change ((I • ⊤ : Submodule ℤ (ℤ × ℚ)).mkQ
    ((1 : ℤ), (0 : ℚ))) = 0
  rw [← pow_one I]
  exact he

/-- The integer-rational product is not finite over the integers, although its
reduction modulo `(2)` and its adic completion are nonzero and finite over the
integers and the completed ring, respectively. -/
theorem integer_rational_product_completion :
    Module.Finite ℤ
      ((ℤ × ℚ) ⧸ ((Ideal.span ({(2 : ℤ)} : Set ℤ)) •
        (⊤ : Submodule ℤ (ℤ × ℚ)))) ∧
    Nontrivial
      ((ℤ × ℚ) ⧸ ((Ideal.span ({(2 : ℤ)} : Set ℤ)) •
        (⊤ : Submodule ℤ (ℤ × ℚ)))) ∧
    ¬ Module.Finite ℤ (ℤ × ℚ) ∧
    Module.Finite
      (AdicCompletion (Ideal.span ({(2 : ℤ)} : Set ℤ)) ℤ)
      (AdicCompletion (Ideal.span ({(2 : ℤ)} : Set ℤ)) (ℤ × ℚ)) ∧
    Nontrivial
      (AdicCompletion (Ideal.span ({(2 : ℤ)} : Set ℤ)) (ℤ × ℚ)) := by
  exact ⟨integer_rational_product_quotient_finite,
    integer_rational_product_quotient_nontrivial,
    not_finite_integer_rational_product,
    integer_rational_product_completion_finite,
    integer_rational_product_completion_nontrivial⟩

end AdicCompletion
