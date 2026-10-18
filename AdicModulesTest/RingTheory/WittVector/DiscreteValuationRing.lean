/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Algebra.Ring.Prod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Coefficient rings and discrete valuation rings of Witt vectors

The Witt vectors over `ZMod 3` form a discrete valuation ring. The zero coefficient ring
is excluded by the domain property. The field `ZMod 2` has bijective cubing but the wrong
characteristic for `3`-typical Witt vectors; its ghost isomorphism gives zero divisors.
The product `ZMod 3 × ZMod 3` is perfect of characteristic three but is not a field,
and complementary Teichmüller lifts give zero divisors in its Witt vectors.

The positive example applies the perfect-field characterization. These examples use
Mathlib's ring structures, perfectness instances, ghost isomorphism, and Teichmüller map.
-/

namespace WittVector

/-- Witt vectors over the field with three elements satisfy the discrete valuation ring
condition, and the coefficient ring satisfies all three field, characteristic, and
perfectness properties. -/
private theorem zmod_three_discreteValuationRing :
    (∃ hD : IsDomain (WittVector 3 (ZMod 3)),
      @IsDiscreteValuationRing (WittVector 3 (ZMod 3)) _ hD) ∧
    IsField (ZMod 3) ∧ CharP (ZMod 3) 3 ∧ PerfectRing (ZMod 3) 3 := by
  have hR : IsField (ZMod 3) ∧ CharP (ZMod 3) 3 ∧ PerfectRing (ZMod 3) 3 :=
    ⟨Field.toIsField (ZMod 3), inferInstance, inferInstance⟩
  exact ⟨(WittVector.isDiscreteValuationRing_iff (p := 3) (R := ZMod 3)).mpr hR, hR⟩

/-- The zero ring is not a field, and its Witt vectors do not admit a domain structure
making them a discrete valuation ring. -/
private theorem zmod_one_not_discreteValuationRing :
    ¬ (∃ hD : IsDomain (WittVector 3 (ZMod 1)),
      @IsDiscreteValuationRing (WittVector 3 (ZMod 1)) _ hD) ∧
    ¬ IsField (ZMod 1) := by
  constructor
  · rintro ⟨hD, _⟩
    letI : IsDomain (WittVector 3 (ZMod 1)) := hD
    exact (zero_ne_one : (0 : WittVector 3 (ZMod 1)) ≠ 1)
      (WittVector.ext fun _ ↦ Subsingleton.elim _ _)
  · exact not_isField_of_subsingleton (ZMod 1)

/-- A product of two fields with three elements is perfect of characteristic three but
not a field. The Teichmüller lifts of its complementary idempotents are nonzero zero
divisors, so its Witt vectors cannot satisfy the discrete valuation ring condition. -/
private theorem zmod_three_prod_not_discreteValuationRing :
    CharP (ZMod 3 × ZMod 3) 3 ∧ PerfectRing (ZMod 3 × ZMod 3) 3 ∧
    ¬ IsField (ZMod 3 × ZMod 3) ∧
    WittVector.teichmuller 3 ((1, 0) : ZMod 3 × ZMod 3) ≠ 0 ∧
    WittVector.teichmuller 3 ((0, 1) : ZMod 3 × ZMod 3) ≠ 0 ∧
    WittVector.teichmuller 3 ((1, 0) : ZMod 3 × ZMod 3) *
      WittVector.teichmuller 3 ((0, 1) : ZMod 3 × ZMod 3) = 0 ∧
    ¬ IsDomain (WittVector 3 (ZMod 3 × ZMod 3)) ∧
    ¬ (∃ hD : IsDomain (WittVector 3 (ZMod 3 × ZMod 3)),
      @IsDiscreteValuationRing (WittVector 3 (ZMod 3 × ZMod 3)) _ hD) := by
  have h10 : ((1, 0) : ZMod 3 × ZMod 3) ≠ 0 := by
    intro h
    exact (one_ne_zero : (1 : ZMod 3) ≠ 0) (congrArg Prod.fst h)
  have h01 : ((0, 1) : ZMod 3 × ZMod 3) ≠ 0 := by
    intro h
    exact (one_ne_zero : (1 : ZMod 3) ≠ 0) (congrArg Prod.snd h)
  have hnotField : ¬ IsField (ZMod 3 × ZMod 3) := by
    intro hF
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel h10
    exact (zero_ne_one : (0 : ZMod 3) ≠ 1) (by
      simpa using congrArg Prod.snd hb)
  have hx : WittVector.teichmuller 3 ((1, 0) : ZMod 3 × ZMod 3) ≠ 0 := by
    intro h
    apply h10
    simpa using congrArg (fun x : WittVector 3 (ZMod 3 × ZMod 3) ↦ x.coeff 0) h
  have hy : WittVector.teichmuller 3 ((0, 1) : ZMod 3 × ZMod 3) ≠ 0 := by
    intro h
    apply h01
    simpa using congrArg (fun x : WittVector 3 (ZMod 3 × ZMod 3) ↦ x.coeff 0) h
  have hxy : WittVector.teichmuller 3 ((1, 0) : ZMod 3 × ZMod 3) *
      WittVector.teichmuller 3 ((0, 1) : ZMod 3 × ZMod 3) = 0 := by
    rw [← map_mul]
    have hzero : ((1, 0) : ZMod 3 × ZMod 3) * (0, 1) = 0 :=
      Prod.ext (mul_zero _) (zero_mul _)
    rw [hzero, teichmuller_zero]
  have hnotDomain : ¬ IsDomain (WittVector 3 (ZMod 3 × ZMod 3)) := by
    intro hD
    letI : IsDomain (WittVector 3 (ZMod 3 × ZMod 3)) := hD
    exact (mul_ne_zero hx hy) hxy
  exact ⟨inferInstance, inferInstance, hnotField, hx, hy, hxy, hnotDomain,
    fun ⟨hD, _⟩ ↦ hnotDomain hD⟩


private theorem zmod_two_characteristic_separation :
    IsField (ZMod 2) ∧ PerfectRing (ZMod 2) 3 ∧ ¬ CharP (ZMod 2) 3 ∧
      ¬ IsDomain (WittVector 3 (ZMod 2)) ∧
      ¬ (∃ h : IsDomain (WittVector 3 (ZMod 2)),
        @IsDiscreteValuationRing (WittVector 3 (ZMod 2)) _ h) := by
  have hcube : ∀ x : ZMod 2, x ^ 3 = x := by decide
  have hperfect : PerfectRing (ZMod 2) 3 := by
    constructor
    constructor
    · intro x y hxy
      simpa only [hcube] using hxy
    · intro x
      exact ⟨x, hcube x⟩
  have hnotchar : ¬ CharP (ZMod 2) 3 := by
    intro h
    letI : CharP (ZMod 2) 3 := h
    exact (by decide : (3 : ZMod 2) ≠ 0) (CharP.cast_eq_zero (ZMod 2) 3)
  have hnotdomain : ¬ IsDomain (WittVector 3 (ZMod 2)) := by
    intro h
    letI : IsDomain (WittVector 3 (ZMod 2)) := h
    letI : Invertible (3 : ZMod 2) :=
      (invertibleOne : Invertible (1 : ZMod 2)).copy _ (by decide)
    let e := ghostEquiv 3 (ZMod 2)
    let f : ℕ → ZMod 2 := Pi.single 0 1
    let g : ℕ → ZMod 2 := Pi.single 1 1
    have hf : f ≠ 0 := by
      intro hf
      have hzero : (1 : ZMod 2) = 0 := by
        simpa [f] using congrFun hf 0
      exact one_ne_zero hzero
    have hg : g ≠ 0 := by
      intro hg
      have hzero : (1 : ZMod 2) = 0 := by
        simpa [g] using congrFun hg 1
      exact one_ne_zero hzero
    have hfg : f * g = 0 := by
      change Pi.single 0 (1 : ZMod 2) * g = 0
      rw [← Pi.single_mul_left]
      simp [g]
    have hmul : e.symm f * e.symm g = 0 := by
      simpa only [map_mul, map_zero] using congrArg e.symm hfg
    rcases mul_eq_zero.mp hmul with hfzero | hgzero
    · exact hf (by simpa using congrArg e hfzero)
    · exact hg (by simpa using congrArg e hgzero)
  refine ⟨Field.toIsField (ZMod 2), hperfect, hnotchar, hnotdomain, ?_⟩
  rintro ⟨h, _⟩
  exact hnotdomain h

end WittVector
