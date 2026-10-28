/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Polynomial.HenselianFactorization
import Mathlib.Tactic

/-!
# Crossed factor uniqueness with arbitrary high tails

The comparison polynomials are arbitrary: neither their equality nor their
reference congruences are supplied. There are no degree bounds on `A` or `B`.
The scalar hypotheses hold for the ideal `(3)` in the 3-adic integers; that
specialization is mathematical motivation, not an additional instance here.
-/

open Polynomial

universe u

example {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ (⊥ : Ideal R).jacobson) (h3I : (3 : R) ∈ I)
    (h3 : (3 : R) ∈ nonZeroDivisors R) (A B G₂ H : R[X])
    (hprod : (X + 1 + C (9 : R) * A) * H =
      G₂ * (X + C (4 : R) + C (9 : R) * B))
    (hG : (X + 1 + C (9 : R) * A - G₂).degree < (1 : WithBot ℕ))
    (hH : (H - (X + C (4 : R) + C (9 : R) * B)).degree < (1 : WithBot ℕ)) :
    X + 1 + C (9 : R) * A = G₂ ∧ H = X + C (4 : R) + C (9 : R) * B := by
  have hresultant : (X + 1 : R[X]).resultant (X + C (4 : R)) 1 1 = (3 : R) := by
    have hcoeff_one : (1 : R[X]).coeff 1 = 0 := by
      rw [← map_one (C : R →+* R[X])]
      simp only [Polynomial.coeff_C, ite_eq_right (by decide : (1 : ℕ) ≠ 0)]
    unfold Polynomial.resultant
    rw [Matrix.det_fin_two]
    norm_num [Polynomial.sylvester, Fin.addCases, hcoeff_one]
  refine Polynomial.eq_factors_of_regular_resultant_of_degree_sub_lt I hI
    (g₀ := X + 1) (h₀ := X + C (4 : R)) (n := 1) (m := 1)
    ?_ ?_ ?_ hprod hG hH ?_ ?_
  · exact (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
  · exact (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
  · simpa only [hresultant] using h3
  · intro k
    rw [add_sub_cancel_left, coeff_C_mul, hresultant]
    convert Ideal.mul_mem_mul
      (Ideal.subset_span (by simp : (3 : R) ∈ ({3} : Set R)))
      (I.mul_mem_left (A.coeff k) h3I) using 1; ring
  · intro k
    rw [add_sub_cancel_left, coeff_C_mul, hresultant]
    convert Ideal.mul_mem_mul
      (Ideal.subset_span (by simp : (3 : R) ∈ ({3} : Set R)))
      (I.mul_mem_left (B.coeff k) h3I) using 1; ring
