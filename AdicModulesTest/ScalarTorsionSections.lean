/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.AdicCompletion.QuotientTorsion
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Field.Rat
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.NormNum

/-!
# Rational sections of scalar-power torsion kernels

For an integer scalar `ℓ`, the successor arrow between the kernels of `ℓ ^ (n + 1)`
and `ℓ ^ n` is the restriction of multiplication by `ℓ`. We instantiate
`Functor.ofOpSequence` with these arrows and construct sections directly in
`ModuleCat.sectionsSubmodule`.

For the rational quotient by the integer multiples of `1`, the coordinates are
`[1 / ℓ ^ n]`. Successor compatibility is extended to all arrows using
`NatTrans.ofOpSequence`. The scalar `-2` gives a nonzero section, together
with independently proved ambient bijectivity. The zeroth coordinate is zero.
The nonzero section and its finite-level sign calibration do not use the
completion comparison.

## References

The nonvanishing argument follows the rational half-class example in
`GroupTheoryTest.QuotientTorsion`, using the canonical quotient and rational APIs.
-/

-- This module consists solely of private examples.
set_option linter.privateModule false

open CategoryTheory

universe u

private theorem zsmul_mapsTo_power_ker {A : Type u} [AddCommGroup A] (ℓ : ℤ) (n : ℕ) :
    Set.MapsTo (zsmulAddGroupHom (α := A) ℓ)
      (zsmulAddGroupHom (α := A) (ℓ ^ (n + 1))).ker
      (zsmulAddGroupHom (α := A) (ℓ ^ n)).ker := by
  intro x hx
  change (ℓ ^ n) • (ℓ • x) = 0
  rw [← mul_smul, ← pow_succ]
  exact hx

private abbrev scalarTorsionDiagram {V : Type u} [AddCommGroup V]
    (L : AddSubgroup V) (ℓ : ℤ) : ℕᵒᵖ ⥤ ModuleCat ℤ :=
  Functor.ofOpSequence
    (X := fun n => ModuleCat.of ℤ ((zsmulAddGroupHom (α := V ⧸ L) (ℓ ^ n)).ker))
    (fun n => ModuleCat.ofHom
      (AddMonoidHom.restrict (zsmul_mapsTo_power_ker (A := V ⧸ L) ℓ n)).toIntLinearMap)

private abbrev integerMultiples : AddSubgroup ℚ := AddSubgroup.zmultiples (1 : ℚ)

private theorem rational_zsmul_bijective (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    Function.Bijective (zsmulAddGroupHom (α := ℚ) ℓ) := by
  have hq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ
  constructor
  · intro a b hab
    apply mul_left_cancel₀ hq
    simpa only [zsmulAddGroupHom_apply, zsmul_eq_mul] using hab
  · intro q
    refine ⟨q / ℓ, ?_⟩
    simpa only [zsmulAddGroupHom_apply, zsmul_eq_mul] using
      (mul_div_cancel₀ q hq)

private def rationalTorsionCoordinate (ℓ : ℤ) (hℓ : ℓ ≠ 0) (n : ℕ) :
    (zsmulAddGroupHom (α := ℚ ⧸ integerMultiples) (ℓ ^ n)).ker := by
  have hq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ
  refine ⟨((1 / (ℓ : ℚ) ^ n : ℚ) : ℚ ⧸ integerMultiples), ?_⟩
  change (ℓ ^ n) • ((1 / (ℓ : ℚ) ^ n : ℚ) : ℚ ⧸ integerMultiples) = 0
  rw [← QuotientAddGroup.mk_zsmul]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  have hmul : (ℓ ^ n) • (1 / (ℓ : ℚ) ^ n : ℚ) = 1 := by
    rw [zsmul_eq_mul, Int.cast_pow]
    exact mul_one_div_cancel (pow_ne_zero n hq)
  rw [hmul]
  exact AddSubgroup.mem_zmultiples (1 : ℚ)

private theorem rationalTorsionCoordinate_succ (ℓ : ℤ) (hℓ : ℓ ≠ 0) (n : ℕ) :
    (scalarTorsionDiagram integerMultiples ℓ).map
        (homOfLE (Nat.le_add_right n 1)).op (rationalTorsionCoordinate ℓ hℓ (n + 1)) =
      rationalTorsionCoordinate ℓ hℓ n := by
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  apply Subtype.ext
  change ℓ • ((1 / (ℓ : ℚ) ^ (n + 1) : ℚ) : ℚ ⧸ integerMultiples) =
    ((1 / (ℓ : ℚ) ^ n : ℚ) : ℚ ⧸ integerMultiples)
  rw [← QuotientAddGroup.mk_zsmul]
  have hq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ
  congr 1
  simp [zsmul_eq_mul, pow_succ, mul_inv_rev, ← mul_assoc, hq, div_eq_mul_inv]

private def rationalTorsionSections (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    ModuleCat.sectionsSubmodule (scalarTorsionDiagram integerMultiples ℓ) := by
  let α : (Functor.const ℕᵒᵖ).obj PUnit ⟶
      scalarTorsionDiagram integerMultiples ℓ ⋙ forget (ModuleCat ℤ) :=
    NatTrans.ofOpSequence
      (fun n => homOfElement (rationalTorsionCoordinate ℓ hℓ n)) (by
        intro n
        ext x
        exact (rationalTorsionCoordinate_succ ℓ hℓ n).symm)
  refine ⟨fun n => rationalTorsionCoordinate ℓ hℓ n.unop, ?_⟩
  intro i j f
  exact (congrArg (fun g => g PUnit.unit) (α.naturality f)).symm

private theorem rationalTorsionSections_coordinate (ℓ : ℤ) (hℓ : ℓ ≠ 0) (n : ℕ) :
    Subtype.val ((rationalTorsionSections ℓ hℓ).val (Opposite.op n)) =
      ((1 / (ℓ : ℚ) ^ n : ℚ) : ℚ ⧸ integerMultiples) := rfl

private theorem rationalTorsionSections_zero (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    Subtype.val ((rationalTorsionSections ℓ hℓ).val (Opposite.op 0)) = 0 := by
  rw [rationalTorsionSections_coordinate]
  simp only [pow_zero, div_one]
  exact (QuotientAddGroup.eq_zero_iff (1 : ℚ)).mpr
    (AddSubgroup.mem_zmultiples (1 : ℚ))

private theorem rational_half_ne_zero :
    ((1 / 2 : ℚ) : ℚ ⧸ integerMultiples) ≠ 0 := by
  intro hzero
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp
    ((QuotientAddGroup.eq_zero_iff (1 / 2 : ℚ)).mp hzero)
  have hz' : (z : ℚ) = 1 / 2 := by simpa only [zsmul_eq_mul, mul_one] using hz
  have hden := congrArg Rat.den hz'
  rw [Rat.div_def', Rat.den_divInt] at hden
  norm_num at hden

private theorem rational_neg_two_sections_model :
    Function.Bijective (zsmulAddGroupHom (α := ℚ) (-2 : ℤ)) ∧
      ∃ s : ModuleCat.sectionsSubmodule (scalarTorsionDiagram integerMultiples (-2 : ℤ)),
      (∀ n, Subtype.val (s.val (Opposite.op n)) =
        ((1 / (-2 : ℚ) ^ n : ℚ) : ℚ ⧸ integerMultiples)) ∧
      Subtype.val (s.val (Opposite.op 1)) ≠ 0 ∧
      Subtype.val (s.val (Opposite.op 0)) = 0 := by
  refine ⟨rational_zsmul_bijective (-2) (by norm_num),
    rationalTorsionSections (-2) (by norm_num), ?_, ?_,
    rationalTorsionSections_zero (-2) (by norm_num)⟩
  · simpa using rationalTorsionSections_coordinate (-2) (by norm_num)
  · rw [rationalTorsionSections_coordinate]
    have hneg : (1 / (-2 : ℚ)) = -(1 / 2 : ℚ) := by norm_num
    simpa only [pow_one, Int.cast_neg, Int.cast_ofNat, Nat.cast_ofNat, hneg,
      QuotientAddGroup.mk_neg, neg_ne_zero] using rational_half_ne_zero

private def integerOne : integerMultiples := ⟨1, AddSubgroup.mem_zmultiples (1 : ℚ)⟩

-- The natural kernel transport keeps the very same quotient element of the section.
private def rationalNegTwoNatCoordinate (n : ℕ) :
    (nsmulAddMonoidHom (α := ℚ ⧸ integerMultiples) (2 ^ n)).ker := by
  let x := (rationalTorsionSections (-2) (by norm_num)).val (Opposite.op n)
  refine ⟨x.val, ?_⟩
  have hn : ((-2 : ℤ) ^ n).natAbs = 2 ^ n := by simp
  change (2 ^ n) • x.val = 0
  rw [← hn]
  exact natAbs_nsmul_eq_zero.mpr x.property

private theorem rational_two_pow_bijective (n : ℕ) :
    Function.Bijective (nsmulAddMonoidHom (α := ℚ) (2 ^ n)) := by
  have h := rational_zsmul_bijective ((2 : ℤ) ^ n) (pow_ne_zero n (by norm_num))
  change Function.Bijective (fun q : ℚ => (2 ^ n : ℕ) • q)
  have hf : (fun q : ℚ => (2 ^ n : ℕ) • q) = fun q : ℚ => ((2 : ℤ) ^ n) • q := by
    funext q
    simp only [nsmul_eq_mul, zsmul_eq_mul, Nat.cast_pow, Int.cast_pow,
      Nat.cast_ofNat, Int.cast_ofNat]
  rw [hf]
  exact h

private noncomputable def rationalNegTwoRaw (n : ℕ) :
    integerMultiples ⧸ (nsmulAddMonoidHom (α := integerMultiples) (2 ^ n)).range :=
  QuotientAddGroup.nsmulTorsionEquivQuotient integerMultiples (2 ^ n)
    (rational_two_pow_bijective n) (rationalNegTwoNatCoordinate n)

private theorem rationalNegTwoRaw_two :
    rationalNegTwoRaw 2 =
      (integerOne : integerMultiples ⧸
        (nsmulAddMonoidHom (α := integerMultiples) (2 ^ 2)).range) := by
  have hv : (2 ^ 2 : ℕ) • (1 / (-2 : ℚ) ^ 2) ∈ integerMultiples := by
    have heq : (2 ^ 2 : ℕ) • (1 / (-2 : ℚ) ^ 2) = 1 := by norm_num [nsmul_eq_mul]
    rw [heq]
    exact AddSubgroup.mem_zmultiples (1 : ℚ)
  have hx : rationalNegTwoNatCoordinate 2 =
      ⟨((1 / (-2 : ℚ) ^ 2 : ℚ) : ℚ ⧸ integerMultiples), by
        change (2 ^ 2 : ℕ) • ((1 / (-2 : ℚ) ^ 2 : ℚ) : ℚ ⧸ integerMultiples) = 0
        rw [← QuotientAddGroup.mk_nsmul]
        exact (QuotientAddGroup.eq_zero_iff _).mpr hv⟩ := rfl
  have heq : (⟨(2 ^ 2 : ℕ) • (1 / (-2 : ℚ) ^ 2), hv⟩ : integerMultiples) =
      integerOne := by
    apply Subtype.ext
    norm_num [integerOne, nsmul_eq_mul]
  unfold rationalNegTwoRaw
  rw [hx]
  simpa only [heq] using
    (QuotientAddGroup.nsmulTorsionEquivQuotient_apply_mk integerMultiples (2 ^ 2)
      (rational_two_pow_bijective 2) (1 / (-2 : ℚ) ^ 2) hv)

private theorem rationalNegTwoRaw_three :
    rationalNegTwoRaw 3 =
      (-integerOne : integerMultiples ⧸
        (nsmulAddMonoidHom (α := integerMultiples) (2 ^ 3)).range) := by
  have hv : (2 ^ 3 : ℕ) • (1 / (-2 : ℚ) ^ 3) ∈ integerMultiples := by
    have heq : (2 ^ 3 : ℕ) • (1 / (-2 : ℚ) ^ 3) = -1 := by norm_num [nsmul_eq_mul]
    rw [heq]
    exact integerMultiples.neg_mem (AddSubgroup.mem_zmultiples (1 : ℚ))
  have hx : rationalNegTwoNatCoordinate 3 =
      ⟨((1 / (-2 : ℚ) ^ 3 : ℚ) : ℚ ⧸ integerMultiples), by
        change (2 ^ 3 : ℕ) • ((1 / (-2 : ℚ) ^ 3 : ℚ) : ℚ ⧸ integerMultiples) = 0
        rw [← QuotientAddGroup.mk_nsmul]
        exact (QuotientAddGroup.eq_zero_iff _).mpr hv⟩ := rfl
  have heq : (⟨(2 ^ 3 : ℕ) • (1 / (-2 : ℚ) ^ 3), hv⟩ : integerMultiples) =
      -integerOne := by
    apply Subtype.ext
    norm_num [integerOne, nsmul_eq_mul]
  unfold rationalNegTwoRaw
  rw [hx]
  simpa only [heq, QuotientAddGroup.mk_neg] using
    (QuotientAddGroup.nsmulTorsionEquivQuotient_apply_mk integerMultiples (2 ^ 3)
      (rational_two_pow_bijective 3) (1 / (-2 : ℚ) ^ 3) hv)

private def rationalReductionEightFour :
    (integerMultiples ⧸ (nsmulAddMonoidHom (α := integerMultiples) (2 ^ 3)).range) →+
      integerMultiples ⧸ (nsmulAddMonoidHom (α := integerMultiples) (2 ^ 2)).range :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id integerMultiples) (by
    change (nsmulAddMonoidHom (α := integerMultiples) 8).range ≤
      (nsmulAddMonoidHom (α := integerMultiples) 4).range
    exact AddMonoidHom.range_nsmul_mul_le (A := integerMultiples) 4 2)

private theorem rationalNegTwoRaw_not_compatible :
    rationalNegTwoRaw 2 ≠ rationalReductionEightFour (rationalNegTwoRaw 3) := by
  rw [rationalNegTwoRaw_two, rationalNegTwoRaw_three]
  change (integerOne : integerMultiples ⧸
      (nsmulAddMonoidHom (α := integerMultiples) (2 ^ 2)).range) ≠
    (-integerOne : integerMultiples)
  intro heq
  obtain ⟨x, hx⟩ := QuotientAddGroup.eq_iff_sub_mem.mp heq
  have hxq : (4 : ℚ) * (x : ℚ) = 2 := by
    have ht := congrArg (fun y : integerMultiples => (y : ℚ)) hx
    norm_num [integerOne, nsmul_eq_mul] at ht
    exact ht
  have hxhalf : (x : ℚ) = 1 / 2 := by
    apply (mul_left_cancel₀ (by norm_num : (4 : ℚ) ≠ 0))
    calc
      (4 : ℚ) * (x : ℚ) = 2 := hxq
      _ = 4 * (1 / 2 : ℚ) := by norm_num
  apply rational_half_ne_zero
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact hxhalf ▸ x.property

private theorem rationalNegTwo_normalized_control :
    ((-1 : ℤ) ^ 2) • rationalNegTwoRaw 2 =
        (integerOne : integerMultiples ⧸
          (nsmulAddMonoidHom (α := integerMultiples) (2 ^ 2)).range) ∧
      ((-1 : ℤ) ^ 3) • rationalNegTwoRaw 3 =
        (integerOne : integerMultiples ⧸
          (nsmulAddMonoidHom (α := integerMultiples) (2 ^ 3)).range) ∧
      rationalReductionEightFour (((-1 : ℤ) ^ 3) • rationalNegTwoRaw 3) =
        ((-1 : ℤ) ^ 2) • rationalNegTwoRaw 2 := by
  rw [rationalNegTwoRaw_two, rationalNegTwoRaw_three]
  norm_num [rationalReductionEightFour, ← QuotientAddGroup.mk_neg,
    QuotientAddGroup.map_mk]

private theorem rational_neg_two_sections_completion_image :
    QuotientAddGroup.scalarTorsionEquivAdicCompletion integerMultiples (-2)
        (rational_zsmul_bijective (-2) (by norm_num))
        (rationalTorsionSections (-2) (by norm_num)) =
      AdicCompletion.of (Ideal.span {(-2 : ℤ)}) integerMultiples integerOne := by
  apply (QuotientAddGroup.scalarTorsionEquivAdicCompletion integerMultiples (-2)
    (rational_zsmul_bijective (-2) (by norm_num))).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  funext n
  apply Subtype.ext
  have hv : ((-2 : ℤ) ^ n.unop) • (1 / ((-2 : ℤ) : ℚ) ^ n.unop : ℚ) ∈
      integerMultiples := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    rw [QuotientAddGroup.mk_zsmul]
    exact (rationalTorsionCoordinate (-2) (by norm_num) n.unop).property
  have hmul : ((-2 : ℤ) ^ n.unop) • (1 / ((-2 : ℤ) : ℚ) ^ n.unop : ℚ) = 1 := by
    rw [zsmul_eq_mul, Int.cast_pow]
    exact mul_one_div_cancel (pow_ne_zero n.unop (by norm_num))
  have hOne : (⟨((-2 : ℤ) ^ n.unop) • (1 / ((-2 : ℤ) : ℚ) ^ n.unop : ℚ), hv⟩ :
      integerMultiples) = integerOne := Subtype.ext hmul
  have hcoord :=
    (QuotientAddGroup.scalarTorsionEquivAdicCompletion_symm_coordinate_iff
      integerMultiples (-2) (rational_zsmul_bijective (-2) (by norm_num))
      (AdicCompletion.of (Ideal.span {(-2 : ℤ)}) integerMultiples integerOne)
      n.unop (1 / ((-2 : ℤ) : ℚ) ^ n.unop : ℚ) hv).mpr (by
        exact (AdicCompletion.eval_of (Ideal.span {(-2 : ℤ)}) integerMultiples
          n.unop integerOne).trans (congrArg
            ((Ideal.span {(-2 : ℤ)}) ^ n.unop • ⊤ : Submodule ℤ integerMultiples).mkQ
            hOne.symm))
  exact (rationalTorsionSections_coordinate (-2) (by norm_num) n.unop).trans hcoord.symm
