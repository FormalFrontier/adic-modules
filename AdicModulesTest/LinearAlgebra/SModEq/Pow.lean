/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.LinearAlgebra.SModEq.Pow
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.NormNum

/-!
# Positive-depth power congruences over the 3-adic integers

The canonical ring `ℤ_[3]`, ideal `(3)`, and elements `1` and `10` give a
congruence of exact depth two, with difference `-9`. The ideal is nonzero and
proper. Its membership and the input congruence are established independently
of the iterated-power result, using Mathlib's ideal and integer arithmetic APIs.

The generic starting-depth-one specialization recovers Kenny Lau's
`SModEq.pow_pow_add_one`, including its `n + 1` indexing convention.

## References

The independent 3-adic inputs use Mathlib's ideal and integer arithmetic APIs.
The depth-one comparison is with Kenny Lau's `SModEq.pow_pow_add_one` and
one-step power-congruence method; final consumers use the positive-depth
iteration in `AdicModules.LinearAlgebra.SModEq.Pow`.
-/

namespace AdicModulesTest.SModEqPow

private instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable def threeIdeal : Ideal ℤ_[3] :=
  Ideal.span {(3 : ℤ_[3])}

private theorem three_mem : (3 : ℤ_[3]) ∈ threeIdeal :=
  Ideal.mem_span_singleton_self _

private theorem threeIdeal_ne_bot : threeIdeal ≠ ⊥ := by
  intro hbot
  have hzero : (3 : ℤ_[3]) = 0 := Ideal.span_singleton_eq_bot.mp hbot
  norm_num at hzero

private theorem threeIdeal_ne_top : threeIdeal ≠ ⊤ := by
  exact Ideal.span_singleton_ne_top (PadicInt.p_nonunit (p := 3))

private theorem difference : (1 : ℤ_[3]) - 10 = ((-9 : ℤ) : ℤ_[3]) := by
  norm_num

private theorem difference_ne_zero : (1 : ℤ_[3]) - 10 ≠ 0 := by
  rw [difference]
  norm_num

private theorem depth_two_ne_zero : (2 : ℕ) ≠ 0 := by decide

private theorem initial : (1 : ℤ_[3]) ≡ 10 [SMOD threeIdeal ^ 2] := by
  rw [SModEq.sub_mem, threeIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨-1, by norm_num⟩

private theorem not_depth_three : ¬ (1 : ℤ_[3]) ≡ 10 [SMOD threeIdeal ^ 3] := by
  rw [SModEq.sub_mem, threeIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, difference]
  intro hd
  have hint : (3 ^ 3 : ℤ) ∣ (-9 : ℤ) :=
    (PadicInt.pow_p_dvd_int_iff (p := 3) 3 (-9)).mp hd
  norm_num at hint

/-- One step uses the existing Mathlib theorem, not the iterated result. -/
private theorem stock_one_step : (1 : ℤ_[3]) ^ 3 ≡ 10 ^ 3 [SMOD threeIdeal ^ 3] :=
  initial.pow_add_one three_mem depth_two_ne_zero

/-- The zeroth iterate is precisely the input congruence. -/
private theorem zero_iterate {R : Type*} [CommRing R] {I : Ideal R} {q m : ℕ}
    {x y : R} (h : x ≡ y [SMOD I ^ m]) :
    x ^ (q ^ 0) ≡ y ^ (q ^ 0) [SMOD I ^ (m + 0)] := by
  simpa only [pow_zero, pow_one, Nat.add_zero] using h

/-- Zero is an allowed exponent parameter, including at the zeroth iterate. -/
private theorem zero_parameter {R : Type*} [CommRing R] {I : Ideal R} {m : ℕ}
    {x y : R} (h : x ≡ y [SMOD I ^ m]) (n : ℕ) :
    x ^ (0 ^ n) ≡ y ^ (0 ^ n) [SMOD I ^ (m + n)] := by
  cases n with
  | zero => exact zero_iterate h
  | succ n => simp

/-- If one belongs to the ideal, every congruence is automatic. -/
private theorem one_parameter {R : Type*} [CommRing R] {I : Ideal R} {m : ℕ}
    {x y : R} (h1 : (1 : R) ∈ I) (n : ℕ) :
    x ^ (1 ^ n) ≡ y ^ (1 ^ n) [SMOD I ^ (m + n)] := by
  have hI : I = ⊤ := Ideal.eq_top_of_isUnit_mem I h1 isUnit_one
  simp [hI, Ideal.top_pow]

private theorem zero_depth_input :
    (0 : ℤ) ≡ 1 [SMOD (Ideal.span {(3 : ℤ)} : Ideal ℤ) ^ 0] := by
  simp

/-- At starting depth zero even the first asserted improvement can fail. -/
private theorem zero_depth_failure :
    ¬ (0 : ℤ) ^ (3 ^ 1) ≡ 1 ^ (3 ^ 1)
      [SMOD (Ideal.span {(3 : ℤ)} : Ideal ℤ) ^ (0 + 1)] := by
  rw [SModEq.sub_mem]
  norm_num [Ideal.mem_span_singleton]

/-- The starting-depth-one specialization has Mathlib's original target. -/
private theorem stock_recovery {R : Type*} [CommRing R] {I : Ideal R} {q : ℕ}
    {x y : R} (hqI : (q : R) ∈ I) (h : x ≡ y [SMOD I]) (n : ℕ) :
    x ^ (q ^ n) ≡ y ^ (q ^ n) [SMOD I ^ (n + 1)] := by
  have h1 : x ≡ y [SMOD I ^ 1] := by simpa only [pow_one] using h
  simpa only [Nat.add_comm 1 n] using h1.pow_pow_add hqI Nat.one_ne_zero n

/-- The supplied 3-adic inputs instantiate the iterated-power conclusion for every `n`. -/
private theorem threeAdic_iterates (n : ℕ) :
    (1 : ℤ_[3]) ^ (3 ^ n) ≡ 10 ^ (3 ^ n) [SMOD threeIdeal ^ (2 + n)] :=
  initial.pow_pow_add three_mem depth_two_ne_zero n

end AdicModulesTest.SModEqPow
