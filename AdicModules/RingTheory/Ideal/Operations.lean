/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Comaximality and powers of left ideals

If `J ⊔ I = ⊤`, then `J ⊔ I ^ n = ⊤` for every natural exponent,
where `J` and `I` are arbitrary left ideals of a semiring. The semiring may
be noncommutative and need not have additive inverses or multiplication
cancellation. Neither ideal is required to be two-sided. Powers are formed
as ideals in the original semiring, not as spans of powers of chosen generators.

The proof uses a subtraction-free geometric-sum recurrence. Starting with
`j + i = 1`, where `j ∈ J` and `i ∈ I`, it constructs `x ∈ J` with
`x + i ^ n = 1`. The successor step replaces `x` by `x + i ^ n * j`,
using only closure of `J` under left multiplication.

The two-sided specializations recover Mathlib's comaximal-power statements
under their respective two-sidedness hypotheses.

## References

* Mathlib's left-ideal operations and power API in
  `Mathlib.RingTheory.Ideal.Operations`, authored by Kenny Lau.
* `Ideal.sup_pow_eq_top` and `Ideal.sup_pow_eq_top'` in that module give
  comaximal-power results when the unpowered or powered ideal, respectively,
  is two-sided.
* Neil Strickland's geometric-sum identities in `Mathlib.Algebra.Ring.GeomSum`.
  The recurrence here avoids both subtraction and a commutation assumption.
-/

@[expose] public section

universe u

namespace Ideal

/-- Comaximal left ideals remain comaximal after taking any natural power of
one of them. This extends Mathlib's `Ideal.sup_pow_eq_top` and
`Ideal.sup_pow_eq_top'` without requiring either ideal to be two-sided.
The proof uses a subtraction-free geometric-sum recurrence. -/
theorem sup_pow_eq_top_of_sup_eq_top {R : Type u} [Semiring R]
    {J I : Ideal R} {n : ℕ} (h : J ⊔ I = ⊤) : J ⊔ I ^ n = ⊤ := by
  obtain ⟨j, hj, i, hi, hji⟩ :=
    Submodule.mem_sup.mp ((eq_top_iff_one _).mp h)
  have hp : ∃ x ∈ J, x + i ^ n = 1 := by
    induction n with
    | zero => exact ⟨0, J.zero_mem, by rw [pow_zero, zero_add]⟩
    | succ n ih =>
      obtain ⟨x, hx, hxi⟩ := ih
      refine ⟨x + i ^ n * j, J.add_mem hx (J.mul_mem_left _ hj), ?_⟩
      calc
        (x + i ^ n * j) + i ^ (n + 1) = x + i ^ n * (j + i) := by
          rw [pow_succ, mul_add, add_assoc]
        _ = x + i ^ n := by rw [hji, mul_one]
        _ = 1 := hxi
  obtain ⟨x, hx, hxi⟩ := hp
  exact (eq_top_iff_one _).mpr
    (Submodule.mem_sup.mpr ⟨x, hx, i ^ n, pow_mem_pow hi n, hxi⟩)

/-- The comaximal-power conclusion when the unpowered ideal is two-sided. -/
private theorem sup_pow_eq_top_of_isTwoSided_left
    {R : Type u} [Semiring R] {I J : Ideal R} [I.IsTwoSided] {n : ℕ}
    (h : I ⊔ J = ⊤) : I ⊔ J ^ n = ⊤ :=
  sup_pow_eq_top_of_sup_eq_top (J := I) (I := J) (n := n) h

/-- The comaximal-power conclusion when the powered ideal is two-sided. -/
private theorem sup_pow_eq_top_of_isTwoSided_right
    {R : Type u} [Semiring R] {I J : Ideal R} [J.IsTwoSided] {n : ℕ}
    (h : I ⊔ J = ⊤) : I ⊔ J ^ n = ⊤ :=
  sup_pow_eq_top_of_sup_eq_top (J := I) (I := J) (n := n) h

end Ideal
