/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.MvPolynomial.Evaluation
import Mathlib.Data.ZMod.Basic

/-!
# Two-coordinate value association with nonzero zero divisors

Over `ZMod 64`, take the ideal `(2)`, the natural-coefficient polynomial `X₀ * X₁`,
and the points `(2, 2)` and `(10, 10)`. Both coordinates move by `8 ∈ (4)(2)`.
The ideal `(2)` lies in the Jacobson radical because `2 ^ 6 = 0`.

The values are the distinct nonzero elements `4` and `36`. The nonzero element `16`
annihilates each, so neither value is regular. Their association below is obtained
from `MvPolynomial.associated_eval₂_of_sub_mem_span_mul`, not from a chosen unit.
-/

@[expose] public section

noncomputable section

private def evenIdeal : Ideal (ZMod 64) := Ideal.span {2}

private def productPolynomial : MvPolynomial (Fin 2) ℕ :=
  MvPolynomial.X 0 * MvPolynomial.X 1

private def lowerPoint : Fin 2 → ZMod 64 := fun _ => 2

private def upperPoint : Fin 2 → ZMod 64 := fun _ => 10

private theorem product_values_nonregular_model :
    Associated
        (productPolynomial.eval₂ (Nat.castRingHom (ZMod 64)) upperPoint)
        (productPolynomial.eval₂ (Nat.castRingHom (ZMod 64)) lowerPoint) ∧
      productPolynomial.eval₂ (Nat.castRingHom (ZMod 64)) lowerPoint = 4 ∧
      productPolynomial.eval₂ (Nat.castRingHom (ZMod 64)) upperPoint = 36 ∧
      (∀ i, upperPoint i ≠ lowerPoint i) ∧
      (4 : ZMod 64) ≠ 0 ∧ (36 : ZMod 64) ≠ 0 ∧ (4 : ZMod 64) ≠ 36 ∧
      (16 : ZMod 64) ≠ 0 ∧ (4 : ZMod 64) * 16 = 0 ∧ (36 : ZMod 64) * 16 = 0 := by
  have ha : productPolynomial.eval₂ (Nat.castRingHom (ZMod 64)) lowerPoint = 4 := by
    simp only [productPolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, lowerPoint]
    decide
  have hb : productPolynomial.eval₂ (Nat.castRingHom (ZMod 64)) upperPoint = 36 := by
    simp only [productPolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, upperPoint]
    decide
  have hI : evenIdeal ≤ Ideal.jacobson (⊥ : Ideal (ZMod 64)) := by
    apply (Ideal.span_singleton_le_iff_mem _).2
    apply Ideal.radical_le_jacobson
    exact Ideal.mem_radical_iff.mpr ⟨6, by
      change (2 : ZMod 64) ^ 6 = 0
      decide⟩
  have hab : ∀ i, upperPoint i - lowerPoint i ∈
      Ideal.span {productPolynomial.eval₂ (Nat.castRingHom (ZMod 64)) lowerPoint} *
        evenIdeal := by
    intro i
    have hδ : upperPoint i - lowerPoint i = (4 : ZMod 64) * 2 := by
      change (10 : ZMod 64) - 2 = 4 * 2
      decide
    rw [hδ, ha]
    exact Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  refine ⟨MvPolynomial.associated_eval₂_of_sub_mem_span_mul evenIdeal hI
    (Nat.castRingHom (ZMod 64)) productPolynomial lowerPoint upperPoint
    (fun i _ => hab i), ha, hb, ?_⟩
  decide
