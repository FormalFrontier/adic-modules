/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.WittVector.Torsion
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Torsion.Prod
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.WittVector.Domain
import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Integer torsion in concrete Witt rings

The product of two copies of `ZMod 3` is reduced but not a domain. Its Witt ring has no
integer torsion by the reduced-coefficient criterion.

The square-zero element of the dual-number ring `TrivSqZeroExt (ZMod 3) (ZMod 3)` has a
nonzero Teichmüller lift killed by `3`. These examples use the existing Witt maps,
coefficient formulas, and the torsion-free module API from Mathlib.
-/

@[expose] public section

private theorem product_witt_isTorsionFree_int :
    IsReduced (ZMod 3 × ZMod 3) ∧
      ¬ IsDomain (ZMod 3 × ZMod 3) ∧
      Module.IsTorsionFree ℤ (WittVector 3 (ZMod 3 × ZMod 3)) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro h
    have := h
    have hzero : ((1, 0) : ZMod 3 × ZMod 3) * (0, 1) = 0 := by
      ext <;> simp
    rcases mul_eq_zero.mp hzero with hleft | hright
    · exact one_ne_zero (congrArg Prod.fst hleft)
    · exact one_ne_zero (congrArg Prod.snd hright)
  · exact (WittVector.isTorsionFree_int_iff_isReduced (p := 3)
      (R := ZMod 3 × ZMod 3)).mpr inferInstance

private theorem dualNumber_witt_has_int_torsion :
    ¬ IsReduced (TrivSqZeroExt (ZMod 3) (ZMod 3)) ∧
      (∃ x : WittVector 3 (TrivSqZeroExt (ZMod 3) (ZMod 3)),
        x.coeff 0 ≠ 0 ∧ (∀ n : ℕ, 0 < n → x.coeff n = 0) ∧ (3 : ℤ) • x = 0) ∧
      ¬ Module.IsTorsionFree ℤ (WittVector 3 (TrivSqZeroExt (ZMod 3) (ZMod 3))) := by
  have : CharP (TrivSqZeroExt (ZMod 3) (ZMod 3)) 3 :=
    charP_of_injective_ringHom
      (f := TrivSqZeroExt.inlHom (ZMod 3) (ZMod 3))
      TrivSqZeroExt.inl_injective 3
  let ε : TrivSqZeroExt (ZMod 3) (ZMod 3) := TrivSqZeroExt.inr (1 : ZMod 3)
  have hε : ε ≠ 0 := by
    intro h
    apply (one_ne_zero : (1 : ZMod 3) ≠ 0)
    apply TrivSqZeroExt.inr_injective (R := ZMod 3)
    simpa only [ε, TrivSqZeroExt.inr_zero] using h
  have hε₂ : ε ^ 2 = 0 := by
    simpa only [ε, pow_two] using
      TrivSqZeroExt.inr_mul_inr (ZMod 3) (1 : ZMod 3) (1 : ZMod 3)
  have hε₃ : ε ^ 3 = 0 := by
    calc
      ε ^ 3 = ε ^ 2 * ε := pow_succ ε 2
      _ = 0 := by rw [hε₂, zero_mul]
  have hnotred : ¬ IsReduced (TrivSqZeroExt (ZMod 3) (ZMod 3)) := by
    intro h
    have := h
    exact hε (eq_zero_of_pow_eq_zero hε₂)
  let x : WittVector 3 (TrivSqZeroExt (ZMod 3) (ZMod 3)) :=
    WittVector.teichmuller 3 ε
  have hx₀ : x.coeff 0 = ε := WittVector.teichmuller_coeff_zero 3 ε
  have hx₀ne : x.coeff 0 ≠ 0 := by simpa only [hx₀] using hε
  have hx : x ≠ 0 := by
    intro h
    apply hx₀ne
    rw [h, WittVector.zero_coeff]
  have hxpos : ∀ n : ℕ, 0 < n → x.coeff n = 0 :=
    WittVector.teichmuller_coeff_pos 3 ε
  have hxcoeff : ∀ i : ℕ, x.coeff i ^ (3 ^ 1) = 0 := by
    intro i
    cases i with
    | zero => simpa only [pow_one, hx₀] using hε₃
    | succ i =>
      rw [hxpos _ (Nat.succ_pos _)]
      exact zero_pow (by decide)
  have hxmul : x * (3 : WittVector 3 (TrivSqZeroExt (ZMod 3) (ZMod 3))) ^ 1 = 0 :=
    (WittVector.mul_p_pow_eq_zero_iff_coeff_pow_eq_zero x 1).mpr hxcoeff
  have hkill : (3 : ℤ) • x = 0 := by
    calc
      (3 : ℤ) • x = (3 : WittVector 3 (TrivSqZeroExt (ZMod 3) (ZMod 3))) * x := by
        simp only [zsmul_eq_mul, Int.cast_ofNat]
      _ = x * (3 : WittVector 3 (TrivSqZeroExt (ZMod 3) (ZMod 3))) := mul_comm _ _
      _ = 0 := by simpa only [pow_one] using hxmul
  refine ⟨hnotred, ⟨x, hx₀ne, hxpos, hkill⟩, ?_⟩
  intro htf
  have hzero := (Module.isTorsionFree_iff_smul_eq_zero.mp htf) (3 : ℤ) x hkill
  rcases hzero with h3 | hxzero
  · exact (by decide : (3 : ℤ) ≠ 0) h3
  · exact hx hxzero
