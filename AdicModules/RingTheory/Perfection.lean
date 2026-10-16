/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.RingTheory.Perfection

/-!
# The inverse-Frobenius limit of a field

For a field `K` of prime characteristic `p`, the noncomputable field
structure on `Perfection K p` extends its existing commutative ring structure.
No perfectness assumption on `K` is needed. This is the inverse limit of Frobenius,
not the extension obtained by adjoining roots to `K`.

The coefficient ring homomorphisms are unchanged. Their compatibility with inverses,
division and integer powers follows from `map_inv₀`, `map_div₀` and `map_zpow₀`;
natural powers use `map_pow`. The inverse is chosen by the units-or-zero field
constructor, so coefficientwise inversion is a propositional equality, not a
prescribed definitional reduction. The existing characteristic and perfect-ring
instances are retained.

This field structure does not assert surjectivity of the zeroth coefficient onto
an imperfect `K`, or identify its image with an intersection of Frobenius images.

## References

The construction extends Kenny Lau's Mathlib formalization of perfection and uses
Mathlib's `Field.ofIsUnitOrEqZero` and its unit-based inverse construction.
-/

@[expose] public section

universe u

namespace Perfection

variable {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The inverse-Frobenius limit of a field of prime characteristic is a field,
with the same commutative ring structure and coefficient maps as its perfection. -/
noncomputable instance instField : Field (Perfection K p) := by
  letI : Nontrivial (Perfection K p) :=
    domain_nontrivial (coeff K p 0) (map_zero _) (map_one _)
  have units_or_zero : ∀ a : Perfection K p, IsUnit a ∨ a = 0 := by
    classical
    intro a
    by_cases ha : a = 0
    · exact Or.inr ha
    left
    have h0 : coeff K p 0 a ≠ 0 := by
      intro h
      apply ha
      apply Perfection.ext
      intro n
      rw [map_zero]
      exact eq_zero_of_pow_eq_zero ((coeffMonoidHom_pow_p_pow_self a n).trans h)
    have hn (n : ℕ) : coeff K p n a ≠ 0 :=
      coeff_ne_zero_of_le h0 (Nat.zero_le n)
    let b : Perfection K p :=
      ⟨fun n ↦ (coeff K p n a)⁻¹, fun n ↦ by rw [inv_pow, coeff_pow_p']⟩
    refine isUnit_iff_exists_inv.mpr ⟨b, Perfection.ext fun n ↦ ?_⟩
    rw [map_mul, map_one]
    change coeff K p n a * (coeff K p n a)⁻¹ = 1
    exact mul_inv_cancel₀ (hn n)
  exact Field.ofIsUnitOrEqZero units_or_zero

end Perfection
