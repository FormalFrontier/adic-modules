/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.AdicCompletion.FixedPoint
import AdicModules.Topology.Algebra.PadicInt
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A nonlinear fixed-point input over the 2-adic integers

The map `x ↦ -2 - x²` preserves `(2)` in `ℤ_[2]` and gains one ideal power on
all differences between elements of `(2)`. Completeness follows from the canonical
adic topology and completeness of the 2-adic integers.

The second difference at `0, 2, 4` is nonzero, so this is not an affine input on
its domain. The identity map on the same ideal gives a cheap boundary: domain
preservation without the gain hypothesis does not imply uniqueness.

The existing results `PadicInt.isAdic_span_p` and `IsAdic.isAdicComplete_iff`
supply completeness without a new bridge or a new topology.
-/

namespace PadicInt

section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local notation "J" => (Ideal.span {(2 : ℤ_[2])})
local notation "q" => (fun x : ℤ_[2] ↦ -(2 : ℤ_[2]) - x ^ 2)

theorem two_mem_span_two : (2 : ℤ_[2]) ∈ J :=
  Ideal.subset_span (by simp)

theorem two_adic_complete : IsAdicComplete J ℤ_[2] := by
  exact (isAdic_span_p 2).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

theorem quadratic_mapsTo :
    Set.MapsTo q (J • ⊤ : Submodule ℤ_[2] ℤ_[2])
      (J • ⊤ : Submodule ℤ_[2] ℤ_[2]) := by
  intro x hx
  have hxJ : x ∈ J := by
    simpa only [SetLike.mem_coe, smul_eq_mul, Ideal.mul_top] using hx
  have hsq : x ^ 2 ∈ J := by
    simpa only [pow_two] using (J).mul_mem_left x hxJ
  have hout : q x ∈ J :=
    (J).sub_mem ((J).neg_mem two_mem_span_two) hsq
  simpa only [SetLike.mem_coe, smul_eq_mul, Ideal.mul_top] using hout

theorem quadratic_gain (n : ℕ) (x y : ℤ_[2])
    (hx : x ∈ J • (⊤ : Submodule ℤ_[2] ℤ_[2]))
    (hy : y ∈ J • (⊤ : Submodule ℤ_[2] ℤ_[2]))
    (hxy : x - y ∈ J ^ n • (⊤ : Submodule ℤ_[2] ℤ_[2])) :
    q x - q y ∈ J ^ (n + 1) • (⊤ : Submodule ℤ_[2] ℤ_[2]) := by
  have hxJ : x ∈ J := by
    simpa only [SetLike.mem_coe, smul_eq_mul, Ideal.mul_top] using hx
  have hyJ : y ∈ J := by
    simpa only [SetLike.mem_coe, smul_eq_mul, Ideal.mul_top] using hy
  have hxyJ : x - y ∈ J ^ n := by
    simpa only [SetLike.mem_coe, smul_eq_mul, Ideal.mul_top] using hxy
  have hprod : (x - y) * (x + y) ∈ J ^ (n + 1) := by
    rw [pow_succ]
    exact Ideal.mul_mem_mul hxyJ ((J).add_mem hxJ hyJ)
  have hidentity : q x - q y = -((x - y) * (x + y)) := by
    ring
  have hout : q x - q y ∈ J ^ (n + 1) := by
    rw [hidentity]
    exact (J ^ (n + 1)).neg_mem hprod
  simpa only [SetLike.mem_coe, smul_eq_mul, Ideal.mul_top] using hout

theorem quadratic_nontrivial_input :
    (2 : ℤ_[2]) ∈ J ∧ (2 : ℤ_[2]) ≠ 0 ∧ q 0 ≠ 0 := by
  refine ⟨two_mem_span_two, ?_, ?_⟩ <;> norm_num

theorem quadratic_second_difference :
    (0 : ℤ_[2]) ∈ J ∧ (2 : ℤ_[2]) ∈ J ∧ (4 : ℤ_[2]) ∈ J ∧
      q 4 + q 0 ≠ q 2 + q 2 := by
  refine ⟨(J).zero_mem, two_mem_span_two, ?_, ?_⟩
  · convert (J).add_mem two_mem_span_two two_mem_span_two using 1; norm_num
  · norm_num

theorem identity_boundary :
    Set.MapsTo (id : ℤ_[2] → ℤ_[2])
        (J • ⊤ : Submodule ℤ_[2] ℤ_[2])
        (J • ⊤ : Submodule ℤ_[2] ℤ_[2]) ∧
      ¬ ∃! x : ℤ_[2],
        x ∈ J • (⊤ : Submodule ℤ_[2] ℤ_[2]) ∧ id x = x := by
  refine ⟨fun _ hx ↦ hx, ?_⟩
  rintro ⟨x, _, huniq⟩
  have hzero : (0 : ℤ_[2]) = x := huniq 0 ⟨Submodule.zero_mem _, rfl⟩
  have htwo_mem : (2 : ℤ_[2]) ∈ J • (⊤ : Submodule ℤ_[2] ℤ_[2]) := by
    simpa only [SetLike.mem_coe, smul_eq_mul, Ideal.mul_top] using two_mem_span_two
  have htwo : (2 : ℤ_[2]) = x := huniq 2 ⟨htwo_mem, rfl⟩
  have hfalse : (0 : ℤ_[2]) = 2 := hzero.trans htwo.symm
  norm_num at hfalse

example : ∃! x : ℤ_[2], x ∈ J ∧ q x = x := by
  let : IsAdicComplete J ℤ_[2] := two_adic_complete
  simpa only [SetLike.mem_coe, smul_eq_mul, Ideal.mul_top] using
    (IsAdicComplete.existsUnique_fixedPoint J q quadratic_mapsTo quadratic_gain)

end

end PadicInt
