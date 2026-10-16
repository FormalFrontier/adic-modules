/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Polynomial.Evaluation
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.NormNum

/-!
# Derivative association over the 3-adic integers

For `f = X³`, `a = 1`, `b = 10` and the maximal ideal of `ℤ_[3]`, the displacement
is `9 = 3 * 3` and the initial derivative is the nonunit `3`. Thus the proximity input
is nontrivial and does not imply that the derivative is a unit. These inputs are
proved independently of polynomial-value association. The derivative comparison is
then an application of the general polynomial theorem.

The final example allows a zero derivative in every commutative ring, including the zero ring.

## References

The independent proximity and nonunit inputs use Mathlib's 3-adic ideal,
Jacobson-radical and polynomial-derivative arithmetic. The derivative conclusion
applies `Polynomial.associated_eval_of_sub_mem_span_mul` from
`AdicModules.Polynomial.Evaluation`.
-/

public section

open Polynomial

namespace AdicModulesTest.Polynomial.Evaluation

universe u

/-- The derivative contract is an application of the polynomial-value theorem, with
no derivative-unit, Henselian, domain or completeness assumption. -/
theorem derivative_associated {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) (f : R[X]) (a b : R)
    (hab : b - a ∈ Ideal.span {f.derivative.eval a} * I) :
    Associated (f.derivative.eval b) (f.derivative.eval a) :=
  Polynomial.associated_eval_of_sub_mem_span_mul I hI f.derivative a b hab

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

local notation "I₃" => IsLocalRing.maximalIdeal ℤ_[3]

/-- The canonical maximal ideal of the 3-adic integers lies in the Jacobson radical. -/
theorem padicInt_three_jacobson : I₃ ≤ Ideal.jacobson (⊥ : Ideal ℤ_[3]) :=
  IsLocalRing.maximalIdeal_le_jacobson ⊥

/-- Independent proximity data for `X³` at the distinct arguments `1` and `10` in `ℤ₃`.
The derivative at `1` is the nonunit `3`; the displacement is `3` times an element of `I₃`. -/
theorem padicInt_three_cubic_data :
    (X ^ 3 : ℤ_[3][X]).derivative.eval 1 = 3 ∧
      ¬ IsUnit ((X ^ 3 : ℤ_[3][X]).derivative.eval 1) ∧
      (1 : ℤ_[3]) ≠ 10 ∧
      (10 : ℤ_[3]) - 1 ∈ Ideal.span {(X ^ 3 : ℤ_[3][X]).derivative.eval 1} * I₃ ∧
      (X ^ 3 : ℤ_[3][X]).derivative.eval 10 = 300 := by
  have hd : (X ^ 3 : ℤ_[3][X]).derivative.eval 1 = 3 := by norm_num
  have hmem : (3 : ℤ_[3]) ∈ I₃ := by
    rw [show I₃ = Ideal.span {(3 : ℤ_[3])} by
      simpa only [Nat.cast_ofNat] using (PadicInt.maximalIdeal_eq_span_p (p := 3))]
    exact Ideal.subset_span (Set.mem_singleton _)
  refine ⟨hd, ?_, by norm_num, ?_, by norm_num⟩
  · rw [hd]
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
  · rw [hd]
    exact Ideal.mem_span_singleton_mul.mpr ⟨3, hmem, by norm_num⟩

/-- The derivative values of `X³` at `10` and `1` are associated in `ℤ₃` itself.
The initial derivative is not a unit and the arguments are distinct. -/
theorem padicInt_three_cubic_derivative_associated :
    Associated ((X ^ 3 : ℤ_[3][X]).derivative.eval 10)
      ((X ^ 3 : ℤ_[3][X]).derivative.eval 1) :=
  derivative_associated I₃ padicInt_three_jacobson (X ^ 3) 1 10
    padicInt_three_cubic_data.2.2.2.1

/-- Independent boundary data: `X²` has zero derivative at zero and zero displacement. -/
theorem zero_derivative_data {R : Type u} [CommRing R] :
    (X ^ 2 : R[X]).derivative.eval 0 = 0 ∧
      (0 : R) - 0 ∈ Ideal.span {(X ^ 2 : R[X]).derivative.eval 0} * (⊥ : Ideal R) := by
  constructor <;> simp

/-- The derivative association theorem also applies when the initial derivative is zero. -/
theorem zero_derivative_associated {R : Type u} [CommRing R] :
    Associated ((X ^ 2 : R[X]).derivative.eval 0) ((X ^ 2 : R[X]).derivative.eval 0) :=
  derivative_associated ⊥ bot_le (X ^ 2) 0 0 zero_derivative_data.2

end AdicModulesTest.Polynomial.Evaluation
