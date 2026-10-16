/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.FrobeniusCore
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Field.ZMod
meta import Lean.Elab.Tactic.Omega

/-!
# Frobenius-range intersections in an imperfect Laurent series field

The Laurent series field over `ZMod 3` is infinite and imperfect: the monomial
of order one is not a cube. The constant two is neither zero nor one and has
roots of every Frobenius depth, supplied independently by the stock perfection
lift from the prime field. The intersection's inclusion contract is instantiated
on this imperfect ambient field, including the associated equivalence and
universal property. A reduced product ring checks the non-domain boundary.
-/

noncomputable section

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private abbrev κ := LaurentSeries (ZMod 3)

private instance laurent_charP : CharP κ 3 :=
  charP_of_injective_ringHom (f := HahnSeries.C) HahnSeries.C_injective 3

local notation "C" =>
  (⨅ n : ℕ, RingHom.fieldRange (iterateFrobenius κ 3 n) : Subfield κ)

private theorem laurent_reduced : IsReduced κ := inferInstance

private theorem laurent_infinite : Infinite κ :=
  Infinite.of_injective (fun n : ℤ ↦ (HahnSeries.single n (1 : ZMod 3) : κ)) (by
    intro a b h
    simpa only [HahnSeries.order_single one_ne_zero] using congrArg HahnSeries.order h)

private theorem monomial_not_cube :
    ¬ ∃ a : κ, a ^ 3 = HahnSeries.single (1 : ℤ) (1 : ZMod 3) := by
  rintro ⟨a, ha⟩
  have hord := congrArg HahnSeries.order ha
  rw [HahnSeries.order_pow, HahnSeries.order_single one_ne_zero] at hord
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hord
  omega

private theorem laurent_imperfect : ¬ Function.Surjective (frobenius κ 3) := by
  intro h
  obtain ⟨a, ha⟩ := h (HahnSeries.single (1 : ℤ) (1 : ZMod 3))
  exact monomial_not_cube ⟨a, ha⟩

private theorem constant_two_ne_zero : (HahnSeries.C (2 : ZMod 3) : κ) ≠ 0 := by
  intro h
  have : (2 : ZMod 3) = 0 := HahnSeries.C_injective (Γ := ℤ) (by
    rw [HahnSeries.C_zero]
    exact h)
  exact (by decide : (2 : ZMod 3) ≠ 0) this

private theorem constant_two_ne_one : (HahnSeries.C (2 : ZMod 3) : κ) ≠ 1 := by
  intro h
  have : (2 : ZMod 3) = 1 := HahnSeries.C_injective (Γ := ℤ) (by
    rw [HahnSeries.C_one]
    exact h)
  exact (by decide : (2 : ZMod 3) ≠ 1) this

private def constantTwoPerfection : Perfection κ 3 :=
  Perfection.lift 3 (ZMod 3) κ HahnSeries.C 2

private theorem constantTwoPerfection_coeff_zero :
    Perfection.coeff κ 3 0 constantTwoPerfection = HahnSeries.C (2 : ZMod 3) := rfl

private theorem constant_two_roots (n : ℕ) :
    ∃ y : κ, y ^ (3 ^ n) = HahnSeries.C (2 : ZMod 3) := by
  refine ⟨Perfection.coeff κ 3 n constantTwoPerfection, ?_⟩
  exact Perfection.coeffMonoidHom_pow_p_pow_self constantTwoPerfection n

/-- In an imperfect Laurent series field, the perfect intersection is nontrivial
and proper; its stock perfection equivalence recovers the constant two. -/
theorem laurentSeries_frobenius_intersection :
    PerfectRing C 3 ∧
      HahnSeries.C (2 : ZMod 3) ∈ C ∧
      HahnSeries.single (1 : ℤ) (1 : ZMod 3) ∉ C ∧
      ((Subfield.perfectionMap_iInf_fieldRange_iterateFrobenius κ 3).equiv.symm
        constantTwoPerfection : κ) = HahnSeries.C (2 : ZMod 3) := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · exact (Subfield.mem_iInf_fieldRange_iterateFrobenius 3 _).mpr constant_two_roots
  · intro h
    obtain ⟨a, ha⟩ := (Subfield.mem_iInf_fieldRange_iterateFrobenius 3 _).mp h 1
    exact monomial_not_cube ⟨a, by simpa only [pow_one] using ha⟩
  · exact (Subfield.coe_perfectionMap_iInf_fieldRange_iterateFrobenius_symm
      κ 3 constantTwoPerfection).trans constantTwoPerfection_coeff_zero

-- The existing equivalence's forward coefficients are iterated inverse roots.
example (x : C) (n : ℕ) :
    Perfection.coeff κ 3 n
      ((Subfield.perfectionMap_iInf_fieldRange_iterateFrobenius κ 3).equiv x) =
        (((frobeniusEquiv C 3).symm)^[n] x : κ) := by
  rw [PerfectionMap.equiv_apply, Perfection.coeff_lift]
  rfl

section UniversalProperty

universe w

variable {A : Type w} [CommSemiring A] [CharP A 3] [PerfectRing A 3]

-- The DATA and uniqueness are the stock engine, with an independently-universed
-- commutative-semiring source, rather than a new core lifting construction.
example (f : A →+* κ) :
    (Subfield.subtype C).comp (PerfectionMap.lift 3 A κ C (Subfield.subtype C)
      (Subfield.perfectionMap_iInf_fieldRange_iterateFrobenius κ 3) f) = f := by
  exact (PerfectionMap.lift 3 A κ _ _
    (Subfield.perfectionMap_iInf_fieldRange_iterateFrobenius κ 3)).symm_apply_apply f

example (f g : A →+*
    (⨅ n : ℕ, (iterateFrobenius κ 3 n).fieldRange : Subfield κ))
    (h : ∀ a, (f a : κ) = (g a : κ)) : f = g :=
  PerfectionMap.hom_ext _
    (Subfield.perfectionMap_iInf_fieldRange_iterateFrobenius κ 3) h

end UniversalProperty

-- The zeroth Frobenius range is unrestricted, and zero belongs to every range.
example : (iterateFrobenius κ 3 0).fieldRange = ⊤ := by
  apply RingHom.fieldRange_eq_top_iff.mpr
  intro x
  exact ⟨x, by simp only [iterateFrobenius_def, pow_zero, pow_one]⟩

example : (0 : κ) ∈
    (⨅ n : ℕ, (iterateFrobenius κ 3 n).fieldRange : Subfield κ) :=
  Subfield.zero_mem _

-- The perfect ambient prime field gives the whole field, not a smaller subfield.
example : (⨅ n : ℕ, (iterateFrobenius (ZMod 3) 3 n).fieldRange :
    Subfield (ZMod 3)) = ⊤ := by
  apply top_unique
  exact Subfield.le_iInf_fieldRange_iterateFrobenius 3 ⊤

-- Exponential characteristic one is the identity-power boundary.
example : PerfectRing (⨅ n : ℕ, (iterateFrobenius ℚ 1 n).range : Subring ℚ) 1 :=
  inferInstance

-- Reduced need not mean a domain; this product has nonzero zero divisors.
example : IsReduced (κ × κ) := inferInstance

private theorem product_zero_divisors :
    ((1, 0) : κ × κ) ≠ 0 ∧ ((0, 1) : κ × κ) ≠ 0 ∧
      ((1, 0) : κ × κ) * ((0, 1) : κ × κ) = 0 := by
  simp

example : PerfectRing
    (⨅ n : ℕ, (iterateFrobenius (κ × κ) 3 n).range : Subring (κ × κ)) 3 :=
  inferInstance

example : PerfectionMap 3
    (⨅ n : ℕ, (iterateFrobenius (κ × κ) 3 n).range : Subring (κ × κ)).subtype :=
  Subring.perfectionMap_iInf_range_iterateFrobenius (κ × κ) 3
