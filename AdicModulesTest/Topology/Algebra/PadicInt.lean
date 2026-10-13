/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Topology.Algebra.PadicInt

/-!
# P-adic integer-span clients

These clients use the standard norm topology on `ℤ_[2]`. They show that closure
adds `1` to the proper integer span of `3`, exercise the uniform inverse witness
and the generators `0`, `1` and `-1`, and check the degree-zero and zero-element
boundaries of the ideal-power basis. The linear-topology theorems refine any
zero-neighborhood to a submodule neighborhood, with no global instance added.
A further client adds `1` and the inverse of `3` by taking suprema with
positive-degree restricted ideal neighborhoods, although neither element
belongs to the original integer span.

The closure membership and the degree-zero and degree-one ideal-power boundaries
are available as named results in the `PadicInt` namespace. In the degree-one
case, the restricted ideal contains zero even though the inequality
`1 ≤ PadicInt.valuation 0` is false; the valuation membership criterion therefore
needs its nonzero hypothesis.

## References

* The neighborhood bases and integer-span results in
  `AdicModules.Topology.Algebra.PadicInt`.
* Mathlib's p-adic development by Robert Y. Lewis, Mario Carneiro and Johan
  Commelin, and its ideal-span, scalar-restriction and linear-topology APIs.
-/

open scoped Topology

namespace PadicInt

/-- In the 2-adic integers, closure adds `1` to the proper integer span of `3`. -/
public lemma closure_span_three_two_adds_one_and_span_proper :
    (1 : ℤ_[2]) ∈ closure (Submodule.span ℤ {(3 : ℤ_[2])} : Set ℤ_[2]) ∧
      (1 : ℤ_[2]) ∉ Submodule.span ℤ {(3 : ℤ_[2])} ∧
      Submodule.span ℤ {(3 : ℤ_[2])} ≠ ⊤ := by
  have h := PadicInt.int_span_three_two_proper_dense
  refine ⟨?_, PadicInt.one_notMem_int_span_three_two, h.1⟩
  rw [h.2.closure_eq]
  exact Set.mem_univ _

private lemma zero_one_neg_one_int_spans_proper :
    Submodule.span ℤ {(0 : ℤ_[2])} ≠ ⊤ ∧
      Submodule.span ℤ {(1 : ℤ_[2])} ≠ ⊤ ∧
      Submodule.span ℤ {(-1 : ℤ_[2])} ≠ ⊤ := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Int.cast_zero] using PadicInt.int_span_intCast_ne_top 2 0
  · simpa only [Int.cast_one] using PadicInt.int_span_intCast_ne_top 2 1
  · simpa only [Int.cast_neg, Int.cast_one] using PadicInt.int_span_intCast_ne_top 2 (-1)

private lemma inverse_three_notMem_int_span_one :
    PadicInt.inv (3 : ℤ_[2]) ∉ Submodule.span ℤ {(1 : ℤ_[2])} := by
  simpa using PadicInt.inv_succ_notMem_int_span_intCast 2 1

/-- The degree-zero ideal in the 2-adic ideal-power basis is top and a zero neighborhood. -/
public lemma degree_zero_ideal_is_top_and_neighborhood :
    (Ideal.span {(2 : ℤ_[2]) ^ 0} : Ideal ℤ_[2]) = ⊤ ∧
      ((Ideal.span {(2 : ℤ_[2]) ^ 0} : Ideal ℤ_[2]) : Set ℤ_[2]) ∈ 𝓝 (0 : ℤ_[2]) := by
  constructor
  · simp only [pow_zero, Ideal.span_singleton_one]
  · exact (PadicInt.hasBasis_nhds_zero_span_pow 2).mem_of_mem (i := 0) trivial

/-- The degree-one ideal in the 2-adic basis remains a zero neighborhood after restricting
scalars to `ℤ`. It contains `0` but not `1`, although `1 ≤ PadicInt.valuation 0` is false. -/
public lemma degree_one_int_basis_contains_zero_not_one :
    (((Ideal.span {(2 : ℤ_[2]) ^ 1} : Ideal ℤ_[2]).restrictScalars ℤ) : Set ℤ_[2]) ∈
        𝓝 (0 : ℤ_[2]) ∧
      (0 : ℤ_[2]) ∈ (Ideal.span {(2 : ℤ_[2]) ^ 1} : Ideal ℤ_[2]).restrictScalars ℤ ∧
      (1 : ℤ_[2]) ∉ (Ideal.span {(2 : ℤ_[2]) ^ 1} : Ideal ℤ_[2]).restrictScalars ℤ ∧
      ¬ 1 ≤ PadicInt.valuation (0 : ℤ_[2]) := by
  refine ⟨(PadicInt.hasBasis_nhds_zero_int_submodule_pow 2).mem_of_mem (i := 1) trivial,
    Submodule.zero_mem _, ?_, ?_⟩
  · change ¬ (1 : ℤ_[2]) ∈ (Ideal.span {(2 : ℤ_[2]) ^ 1} : Ideal ℤ_[2])
    rw [← Nat.cast_ofNat (R := ℤ_[2]) (n := 2),
      PadicInt.mem_span_pow_iff_le_valuation (p := 2) (1 : ℤ_[2]) one_ne_zero 1,
      PadicInt.valuation_one]
    decide
  · simp only [PadicInt.valuation_zero]
    decide

private lemma integer_submodule_neighborhood_refinement {s : Set ℤ_[2]}
    (hs : s ∈ 𝓝 (0 : ℤ_[2])) :
    ∃ N : Submodule ℤ ℤ_[2], (N : Set ℤ_[2]) ∈ 𝓝 (0 : ℤ_[2]) ∧ (N : Set ℤ_[2]) ⊆ s := by
  let := PadicInt.isLinearTopology_int 2
  exact (IsLinearTopology.hasBasis_submodule ℤ).mem_iff.mp hs

private lemma self_submodule_neighborhood_refinement {s : Set ℤ_[2]}
    (hs : s ∈ 𝓝 (0 : ℤ_[2])) :
    ∃ N : Submodule ℤ_[2] ℤ_[2], (N : Set ℤ_[2]) ∈ 𝓝 (0 : ℤ_[2]) ∧
      (N : Set ℤ_[2]) ⊆ s := by
  let := PadicInt.isLinearTopology_self 2
  exact (IsLinearTopology.hasBasis_submodule ℤ_[2]).mem_iff.mp hs

private lemma positive_degree_sup_adds_one_and_inverse_three :
    (1 : ℤ_[2]) ∉ Submodule.span ℤ {(3 : ℤ_[2])} ∧
      (1 : ℤ_[2]) ∈ Submodule.span ℤ {(3 : ℤ_[2])} ⊔
        (Ideal.span {(2 : ℤ_[2]) ^ 1} : Ideal ℤ_[2]).restrictScalars ℤ ∧
      PadicInt.inv (3 : ℤ_[2]) ∉ Submodule.span ℤ {(3 : ℤ_[2])} ∧
      PadicInt.inv (3 : ℤ_[2]) ∈ Submodule.span ℤ {(3 : ℤ_[2])} ⊔
        (Ideal.span {(2 : ℤ_[2]) ^ 2} : Ideal ℤ_[2]).restrictScalars ℤ := by
  refine ⟨PadicInt.one_notMem_int_span_three_two, ?_, ?_, ?_⟩
  · rw [PadicInt.int_span_three_two_proper_sup_pow.2 1]
    exact Submodule.mem_top
  · simpa using PadicInt.inv_succ_notMem_int_span_intCast 2 3
  · rw [PadicInt.int_span_three_two_proper_sup_pow.2 2]
    exact Submodule.mem_top

end PadicInt
