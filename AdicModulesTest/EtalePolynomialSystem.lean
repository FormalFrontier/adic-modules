/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.Etale.PolynomialSystem
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic

/-!
# A nonlinear square system over the integers

The single equation is `X² - X - 2`, the ideal is `(2)`, and the approximate
solution is zero. The equation evaluates to `-2`, while its Jacobian determinant
evaluates to the unit `-1`. Its image in the coefficient quotient supplies the
quotient point's unit hypothesis. The coefficient quotient is nontrivial and the equation
is not affine. All of these input facts are proved before invoking the localized
coordinate-algebra declarations. No integer root is supplied.
-/

open MvPolynomial

namespace EtalePolynomialSystem

private noncomputable def equations : Fin 1 → MvPolynomial (Fin 1) ℤ :=
  fun _ => X 0 ^ 2 - X 0 - C 2

private def coefficientIdeal : Ideal ℤ := Ideal.span {(2 : ℤ)}

private def approximate : Fin 1 → ℤ := fun _ => 0

private theorem equation_at_approximate (i : Fin 1) :
    eval approximate (equations i) = -2 := by
  norm_num [equations, approximate]

private theorem equation_mem_ideal (i : Fin 1) :
    eval approximate (equations i) ∈ coefficientIdeal := by
  rw [equation_at_approximate]
  have htwo : (2 : ℤ) ∈ coefficientIdeal := Ideal.subset_span (by simp)
  exact coefficientIdeal.neg_mem htwo

private theorem jacobian_at_approximate :
    eval approximate (Matrix.det (fun i j => pderiv j (equations i))) = -1 := by
  rw [Matrix.det_fin_one (fun i j => pderiv j (equations i))]
  simp only [equations, map_sub, pderiv_C, pderiv_pow, pderiv_X]
  norm_num [approximate]

private theorem jacobian_isUnit :
    IsUnit (eval approximate (Matrix.det (fun i j => pderiv j (equations i)))) := by
  rw [jacobian_at_approximate]
  exact isUnit_neg_one

private theorem coefficientIdeal_ne_top : coefficientIdeal ≠ ⊤ := by
  intro h
  have hmem : (1 : ℤ) ∈ coefficientIdeal := by
    rw [h]
    trivial
  have hdiv : (2 : ℤ) ∣ 1 := by
    simpa only [coefficientIdeal, Ideal.mem_span_singleton] using hmem
  norm_num at hdiv

private theorem coefficientQuotient_nontrivial : Nontrivial (ℤ ⧸ coefficientIdeal) :=
  Ideal.Quotient.nontrivial_iff.mpr coefficientIdeal_ne_top

private theorem second_difference :
    eval (fun _ => (2 : ℤ)) (equations 0) -
      2 * eval (fun _ => (1 : ℤ)) (equations 0) +
      eval (fun _ => (0 : ℤ)) (equations 0) = 2 := by
  have hzero : eval (fun _ => (0 : ℤ)) (equations 0) = -2 :=
    equation_at_approximate 0
  rw [hzero]
  norm_num [equations]

private theorem equation_not_affine :
    ¬ ∃ b c : ℤ, ∀ x : ℤ, eval (fun _ => x) (equations 0) = b * x + c := by
  rintro ⟨b, c, h⟩
  have hd := second_difference
  rw [h 2, h 1, h 0] at hd
  omega

example :
    Algebra.Etale ℤ (Localization.Away
      (Ideal.Quotient.mk (Ideal.span (Set.range equations))
        (Matrix.det (fun i j => pderiv j (equations i))))) :=
  etale_localizationAway_jacobian equations

example :
    let J := Ideal.span (Set.range equations)
    let d := Ideal.Quotient.mk J (Matrix.det (fun i j => pderiv j (equations i)))
    ∃ φ : Localization.Away d →ₐ[ℤ] ℤ ⧸ coefficientIdeal,
      ∀ i : Fin 1, φ (algebraMap (MvPolynomial (Fin 1) ℤ ⧸ J)
        (Localization.Away d) (Ideal.Quotient.mk J (X i))) = 0 := by
  refine ⟨residuePoint equations coefficientIdeal approximate equation_mem_ideal
    (jacobian_isUnit.map (Ideal.Quotient.mk coefficientIdeal)), ?_⟩
  intro i
  simpa only [approximate, map_zero] using
    residuePoint_apply_X equations coefficientIdeal approximate equation_mem_ideal
      (jacobian_isUnit.map (Ideal.Quotient.mk coefficientIdeal)) i

end EtalePolynomialSystem
