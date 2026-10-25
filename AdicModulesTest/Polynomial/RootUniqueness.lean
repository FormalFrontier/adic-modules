/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Polynomial.RootUniqueness
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Simple roots under residue reduction

The canonical map from `ZMod 4` to `ZMod 2` reflects units and has simple-root
uniqueness, including for the nonmonic quadratic `2 * X ^ 2 + X` with nonunit leading
coefficient. The polynomial `X ^ 2` under the same map shows the derivative-unit
condition is needed. Reduction from `ZMod 6` to `ZMod 2` identifies distinct simple
roots of `X ^ 2 - X`, showing that unit reflection is needed.

Specialization to a local ring's residue map recovers Mathlib's local root equality.
-/

@[expose] public section

universe u

open Polynomial

/-- Reduction modulo two has simple-root uniqueness, including for a nonmonic
quadratic with nonunit leading coefficient over `ZMod 4`. -/
private theorem simple_root_uniqueness_mod_four :
    IsLocalHom (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) ∧
    (∀ (g : (ZMod 4)[X]) (a b : ZMod 4),
      g.IsRoot a → g.IsRoot b →
      ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) a =
        ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) b →
      IsUnit (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (g.derivative.eval a)) →
      a = b) ∧
    (C (2 : ZMod 4) * X ^ 2 + X) ≠ 0 ∧
    (C (2 : ZMod 4) * X ^ 2 + X).natDegree = 2 ∧
    (C (2 : ZMod 4) * X ^ 2 + X).leadingCoeff = 2 ∧
    ¬ (C (2 : ZMod 4) * X ^ 2 + X).Monic ∧
    ¬ IsUnit (C (2 : ZMod 4) * X ^ 2 + X).leadingCoeff ∧
    (C (2 : ZMod 4) * X ^ 2 + X).IsRoot 0 ∧
    ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
      ((C (2 : ZMod 4) * X ^ 2 + X).derivative.eval 0) = 1 ∧
    IsUnit (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
      ((C (2 : ZMod 4) * X ^ 2 + X).derivative.eval 0)) ∧
    (0 : ZMod 4) ≠ 2 ∧
    ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (0 : ZMod 4) =
      ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (2 : ZMod 4) ∧
    ¬ (C (2 : ZMod 4) * X ^ 2 + X).IsRoot 2 := by
  let q : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
  let f : (ZMod 4)[X] := C (2 : ZMod 4) * X ^ 2 + X
  have hq : IsLocalHom q := by
    constructor
    intro a ha
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
    have hn : ¬ 2 ∣ n := by
      apply (ZMod.isUnit_natCast_iff_not_dvd_pow
        (p := 2) (d := 1) (a := n) (by decide) (by decide)).mp
      simpa only [map_natCast] using ha
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow
      (p := 2) (d := 2) (a := n) (by decide) (by decide)).mpr hn
  let : IsLocalHom q := hq
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : IsLocalRing (ZMod 4) := RingHom.domain_isLocalRing q
  -- Application of `Polynomial.IsRoot.eq_of_map_eq` to roots with equal reductions modulo two.
  have hunique : ∀ (g : (ZMod 4)[X]) (a b : ZMod 4),
      g.IsRoot a → g.IsRoot b → q a = q b →
      IsUnit (q (g.derivative.eval a)) → a = b := by
    intro g a b ha hb hab hs
    exact Polynomial.IsRoot.eq_of_map_eq ha hb q hab hs
  have htwo_ne : (2 : ZMod 4) ≠ 0 := by decide
  have hCtwo : (C (2 : ZMod 4) : (ZMod 4)[X]) ≠ 0 := C_ne_zero.mpr htwo_ne
  have hquadratic : (C (2 : ZMod 4) * X ^ 2).natDegree = 2 := by
    rw [natDegree_mul_X_pow 2 hCtwo, natDegree_C, zero_add]
  have hdegree : f.natDegree = 2 := by
    have hlt : (X : (ZMod 4)[X]).natDegree <
        (C (2 : ZMod 4) * X ^ 2).natDegree := by
      rw [natDegree_X, hquadratic]
      decide
    exact (natDegree_add_eq_left_of_natDegree_lt hlt).trans hquadratic
  have hne : f ≠ 0 := by
    intro hf
    have h := hdegree
    rw [hf, natDegree_zero] at h
    exact (by decide : (0 : ℕ) ≠ 2) h
  have hleading : f.leadingCoeff = 2 := by
    change f.coeff f.natDegree = 2
    rw [hdegree]
    simp only [f, coeff_add, C_mul_X_pow_eq_monomial, coeff_monomial_same, coeff_X]
    decide
  have hnonmonic : ¬ f.Monic := by
    intro hm
    have hm' : f.leadingCoeff = 1 := hm
    rw [hleading] at hm'
    exact (by decide : (2 : ZMod 4) ≠ 1) hm'
  have hnonunit : ¬ IsUnit f.leadingCoeff := by
    rw [hleading]
    intro hu
    exact (by decide : ¬ Nat.Coprime 2 4) ((ZMod.isUnit_iff_coprime 2 4).mp hu)
  have hroot : f.IsRoot 0 := by
    simp [f, Polynomial.IsRoot]
  have hderivative : f.derivative = 1 := by
    have hfour : (2 : ZMod 4) * 2 = 0 := by decide
    simp only [f, derivative_add, derivative_C_mul_X_sq, derivative_X,
      hfour, map_zero, zero_mul, zero_add]
  have hmapped : q (f.derivative.eval 0) = 1 := by
    rw [hderivative, eval_one, map_one]
  have hsimple : IsUnit (q (f.derivative.eval 0)) := by
    rw [hmapped]
    exact isUnit_one
  have hcollision : q (0 : ZMod 4) = q (2 : ZMod 4) := by
    calc
      q 0 = (0 : ZMod 2) := map_zero q
      _ = (2 : ZMod 2) := by decide
      _ = q (2 : ZMod 4) := (map_natCast q 2).symm
  have heval_two : f.eval (2 : ZMod 4) = 2 := by
    simp only [f, eval_add, eval_C_mul, eval_X_pow, eval_X]
    decide
  have hother : ¬ f.IsRoot 2 := by
    change ¬ (f.eval 2 = 0)
    rw [heval_two]
    exact htwo_ne
  exact ⟨hq, hunique, hne, hdegree, hleading, hnonmonic, hnonunit, hroot, hmapped,
    hsimple, by decide, hcollision, hother⟩

namespace Polynomial

/-- Unit reflection alone does not give uniqueness of roots in a scalar fiber:
`X ^ 2` has the distinct roots `0` and `2` modulo `4`, with equal images modulo `2`.
The mapped derivative at `0` is zero, so the derivative-unit condition fails. -/
private theorem zmod_four_to_two_derivative_unit_necessary :
    IsLocalHom (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) ∧
      (X ^ 2 : (ZMod 4)[X]).IsRoot 0 ∧
      (X ^ 2 : (ZMod 4)[X]).IsRoot 2 ∧
      ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2) (0 : ZMod 4) =
        ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2) (2 : ZMod 4) ∧
      (0 : ZMod 4) ≠ 2 ∧
      ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)
        ((X ^ 2 : (ZMod 4)[X]).derivative.eval 0) = 0 ∧
      ¬ IsUnit (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)
        ((X ^ 2 : (ZMod 4)[X]).derivative.eval 0)) := by
  let φ : ZMod 4 →+* ZMod 2 :=
    ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)
  have hlocal : IsLocalHom φ := by
    refine ⟨?_⟩
    intro a ha
    have ha' : IsUnit (a.val : ZMod 2) := by
      rw [← ZMod.natCast_zmod_val a, map_natCast] at ha
      exact ha
    have hodd : ¬ (2 : ℕ) ∣ a.val :=
      (ZMod.isUnit_natCast_iff_not_dvd_pow
        (p := 2) (d := 1) (a := a.val) (by decide) (by decide)).mp ha'
    have haunit : IsUnit (a.val : ZMod 4) :=
      (ZMod.isUnit_natCast_iff_not_dvd_pow
        (p := 2) (d := 2) (a := a.val) (by decide) (by decide)).mpr hodd
    simpa only [ZMod.natCast_zmod_val] using haunit
  have hderiv : φ ((X ^ 2 : (ZMod 4)[X]).derivative.eval 0) = 0 := by
    rw [derivative_X_sq, eval_C_mul, eval_X, mul_zero, map_zero]
  refine ⟨hlocal, ?_, ?_, ?_, ?_, hderiv, ?_⟩
  · change (X ^ 2 : (ZMod 4)[X]).eval 0 = 0
    rw [eval_X_pow]
    decide
  · change (X ^ 2 : (ZMod 4)[X]).eval 2 = 0
    rw [eval_X_pow]
    decide
  · change φ (0 : ZMod 4) = φ (2 : ZMod 4)
    decide
  · decide
  · change ¬ IsUnit (φ ((X ^ 2 : (ZMod 4)[X]).derivative.eval 0))
    rw [hderiv]
    intro hzero
    have hodd : ¬ (2 : ℕ) ∣ 0 :=
      (ZMod.isUnit_natCast_iff_not_dvd_pow
        (p := 2) (d := 1) (a := 0) (by decide) (by decide)).mp hzero
    exact hodd (by decide)

end Polynomial

namespace Polynomial

/-- Without scalar unit reflection, roots with the same scalar image need not agree, even
when the derivative at the first root is a source unit and the scalar map is surjective. -/
private theorem zmod_six_root_uniqueness_without_unit_reflection :
    (X ^ 2 - X : Polynomial (ZMod 6)).IsRoot 0 ∧
    (X ^ 2 - X : Polynomial (ZMod 6)).IsRoot 4 ∧
    (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)) 0 =
      (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)) 4 ∧
    IsUnit ((ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2))
      ((X ^ 2 - X : Polynomial (ZMod 6)).derivative.eval 0)) ∧
    (0 : ZMod 6) ≠ 4 ∧
    ¬ IsLocalHom (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)) ∧
    (X ^ 2 - X : Polynomial (ZMod 6)).derivative.eval 0 = -1 ∧
    IsUnit ((X ^ 2 - X : Polynomial (ZMod 6)).derivative.eval 0) ∧
    (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2))
      ((X ^ 2 - X : Polynomial (ZMod 6)).derivative.eval 0) = 1 ∧
    ¬ IsUnit (3 : ZMod 6) ∧
    (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)) 3 = 1 ∧
    IsUnit ((ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)) 3) ∧
    Function.Surjective (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)) := by
  let φ : ZMod 6 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)
  let f : Polynomial (ZMod 6) := X ^ 2 - X
  change f.IsRoot 0 ∧ f.IsRoot 4 ∧ φ 0 = φ 4 ∧
    IsUnit (φ (f.derivative.eval 0)) ∧ (0 : ZMod 6) ≠ 4 ∧ ¬ IsLocalHom φ ∧
    f.derivative.eval 0 = -1 ∧ IsUnit (f.derivative.eval 0) ∧
    φ (f.derivative.eval 0) = 1 ∧ ¬ IsUnit (3 : ZMod 6) ∧
    φ 3 = 1 ∧ IsUnit (φ 3) ∧ Function.Surjective φ
  have hroot_zero : f.IsRoot 0 := by
    simpa only [f, IsRoot.def, eval_sub, eval_X_pow, eval_X] using
      (by decide : (0 : ZMod 6) ^ 2 - 0 = 0)
  have hroot_four : f.IsRoot 4 := by
    simpa only [f, IsRoot.def, eval_sub, eval_X_pow, eval_X] using
      (by decide : (4 : ZMod 6) ^ 2 - 4 = 0)
  have hfour : φ 4 = 0 := (map_natCast φ 4).trans (by decide)
  have himages : φ 0 = φ 4 := (map_zero φ).trans hfour.symm
  have hdistinct : (0 : ZMod 6) ≠ 4 := by decide
  have hderivative : f.derivative.eval 0 = (-1 : ZMod 6) := by
    simp only [f, derivative_sub, derivative_X_sq, derivative_X, eval_sub,
      eval_C_mul, eval_X, eval_one, mul_zero, zero_sub]
  have hsource_unit : IsUnit (f.derivative.eval 0) := by
    have hneg_one : (-1 : ZMod 6) = 5 := by decide
    rw [hderivative, hneg_one]
    exact (ZMod.isUnit_iff_coprime 5 6).2 (by decide)
  have hderivative_image : φ (f.derivative.eval 0) = 1 := by
    simpa only [hderivative, map_neg, map_one] using
      (by decide : (-1 : ZMod 2) = 1)
  have htarget_unit : IsUnit (φ (f.derivative.eval 0)) := by
    rw [hderivative_image]
    exact (ZMod.isUnit_iff_coprime 1 2).2 (by decide)
  have hthree_nonunit : ¬ IsUnit (3 : ZMod 6) := by
    intro hu
    exact (by decide : ¬ Nat.Coprime 3 6)
      ((ZMod.isUnit_iff_coprime 3 6).mp hu)
  have hthree_image : φ 3 = 1 := (map_natCast φ 3).trans (by decide)
  have hthree_image_unit : IsUnit (φ 3) := by
    rw [hthree_image]
    exact (ZMod.isUnit_iff_coprime 1 2).2 (by decide)
  have hnot_local : ¬ IsLocalHom φ := by
    rintro ⟨hreflect⟩
    exact hthree_nonunit (hreflect 3 hthree_image_unit)
  have hsurjective : Function.Surjective φ :=
    ZMod.castHom_surjective (by decide : 2 ∣ 6)
  exact ⟨hroot_zero, hroot_four, himages, htarget_unit, hdistinct, hnot_local,
    hderivative, hsource_unit, hderivative_image, hthree_nonunit, hthree_image,
    hthree_image_unit, hsurjective⟩

end Polynomial

/-- The local-ring root equality follows by specializing to the residue homomorphism. -/
private theorem local_root_eq_of_not_isUnit_sub
    {R : Type u} [CommRing R] [IsLocalRing R] {f : R[X]} {a b : R}
    (ha : f.eval a = 0) (hb : f.eval b = 0) (hab : ¬ IsUnit (a - b))
    (hderiv : IsUnit (f.derivative.eval a)) : a = b := by
  have hresidue : IsLocalRing.residue R (a - b) = 0 := by
    by_contra hne
    exact hab ((IsLocalRing.residue_ne_zero_iff_isUnit (a - b)).mp hne)
  have hmap : IsLocalRing.residue R a = IsLocalRing.residue R b :=
    sub_eq_zero.mp (by simpa only [map_sub] using hresidue)
  exact Polynomial.IsRoot.eq_of_map_eq (show f.IsRoot a from ha) (show f.IsRoot b from hb)
    (IsLocalRing.residue R) hmap (hderiv.map (IsLocalRing.residue R))
