/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Henselian
import AdicModules.Polynomial.Evaluation

/-!
# Uniqueness of polynomial roots under unit-reflecting maps

A scalar ring homomorphism satisfying `IsLocalHom` reflects units. Two roots in the same
fiber of such a homomorphism coincide if the derivative at one root has unit image.
The source is a commutative ring; the target may be a noncommutative semiring.

This generalizes Mathlib's local-ring root equality
`IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`; its local case is recovered through
the residue homomorphism.
-/

@[expose] public section

universe u v

namespace Polynomial

/-- Two roots with the same image under a unit-reflecting scalar homomorphism are equal
if the image of the derivative at the first root is a unit. -/
theorem IsRoot.eq_of_map_eq {R : Type u} {S : Type v} [CommRing R] [Semiring S]
    {f : R[X]} {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b)
    (φ : R →+* S) [IsLocalHom φ] (hab : φ a = φ b)
    (hderiv : IsUnit (φ (f.derivative.eval a))) : a = b := by
  change f.eval a = 0 at ha
  change f.eval b = 0 at hb
  have hd : IsUnit (f.derivative.eval a) := IsUnit.of_map φ _ hderiv
  have hI : RingHom.ker φ ≤ Ideal.jacobson (⊥ : Ideal R) := by
    intro x hx
    apply Ideal.mem_jacobson_bot.mpr
    intro y
    apply IsUnit.of_map φ _
    simpa only [map_add, map_mul, RingHom.mem_ker.mp hx, zero_mul, zero_add, map_one]
      using (isUnit_one : IsUnit (1 : S))
  have hspan : Ideal.span {f.derivative.eval a} * RingHom.ker φ = RingHom.ker φ := by
    rw [Ideal.span_singleton_eq_top.mpr hd, Ideal.top_mul]
  have hδ : b - a ∈ RingHom.ker φ := by
    change φ (b - a) = 0
    calc
      φ (b - a) = φ (b + -a) := by rw [sub_eq_add_neg]
      _ = φ b + φ (-a) := map_add φ b (-a)
      _ = φ a + φ (-a) := by rw [hab]
      _ = φ (a + -a) := (map_add φ a (-a)).symm
      _ = 0 := by rw [add_neg_cancel, map_zero]
  have hinj := injOn_eval₂_of_mem_nonZeroDivisors_derivative
    (RingHom.id R) (RingHom.ker φ) hI f a
    (by simpa only [eval₂_id] using hd.mem_nonZeroDivisors)
  apply hinj
  · simp only [Set.mem_ofPred_eq, sub_self, Submodule.zero_mem]
  · simpa only [Set.mem_ofPred_eq, eval₂_id, hspan] using hδ
  · simp only [eval₂_id, ha, hb]

end Polynomial
