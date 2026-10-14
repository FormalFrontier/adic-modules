/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Closure of spans over a dense subsemiring

For a dense subsemiring `A` of a semiring `R` equipped with a topology, the spans
of a set `E` over `A` and over `R` have the same topological closure, provided
addition in the module is separately continuous and `r ↦ r • m` is continuous
for each `m ∈ E`.
The action of `A` is the restriction of the given `R`-action.

These are closures of sets in the module, not bundled submodule closures.
Continuity of multiplication by a fixed scalar is not coefficient continuity;
no such fixed-scalar assumption or joint scalar continuity is required here.
The generating set may be empty or infinite, and neither additive inverses nor
Hausdorffness are assumed.

## References

* Mathlib's `Continuous.range_subset_closure_image_dense` for continuous images
  of dense sets, and `AddSubmonoid.topologicalClosure` for additive closure under
  separately continuous addition.
* Mathlib's `Submodule.span_eq_closure`, `Submodule.closure_induction` and
  `Submodule.span_induction` for span generation, and `Subsemiring.module`,
  `Subsemiring.smul_def` and `Subsemiring.isScalarTower` for restriction of the
  scalar action.
-/

@[expose] public section

open Topology

universe u v

namespace Submodule

/-- Restricting scalars to a dense subsemiring does not change the closure of a span
when addition is separately continuous and scalar multiplication is continuous in
its coefficient at each generator. Both spans use the same ambient module and the
canonical restricted action of the subsemiring. -/
theorem closure_span_eq_of_dense_subsemiring
    {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M] [Module R M]
    [TopologicalSpace R] [TopologicalSpace M] [SeparatelyContinuousAdd M]
    (A : Subsemiring R) (hA : Dense (A : Set R)) (E : Set M)
    (hE : ∀ m ∈ E, Continuous (fun r : R => r • m)) :
    closure (Submodule.span A E : Set M) = closure (Submodule.span R E : Set M) := by
  let S : AddSubmonoid M := (Submodule.span A E).toAddSubmonoid.topologicalClosure
  have hS : (S : Set M) = closure (Submodule.span A E : Set M) := by
    simp only [S, AddSubmonoid.coe_topologicalClosure, Submodule.coe_toAddSubmonoid]
  have hgen (m : M) (hm : m ∈ E) (r : R) : r • m ∈ (S : Set M) := by
    rw [hS]
    refine closure_mono ?_ ((hE m hm).range_subset_closure_image_dense hA ⟨r, rfl⟩)
    rintro _ ⟨a, ha, rfl⟩
    simpa only [SetLike.mem_coe, Subsemiring.smul_def] using
      (Submodule.span A E).smul_mem (⟨a, ha⟩ : A) (Submodule.subset_span hm)
  apply Set.Subset.antisymm
  · exact closure_mono (Submodule.span_subset_span A R E)
  · refine closure_minimal ?_ isClosed_closure
    intro m hm
    -- Strengthen the induction property so that no continuity at span elements is needed.
    have hsmul : ∀ r : R, r • m ∈ S := by
      refine Submodule.span_induction
        (p := fun x _ => ∀ r : R, r • x ∈ S) ?_ ?_ ?_ ?_ hm
      · intro x hx
        exact hgen x hx
      · intro r
        simpa only [smul_zero] using S.zero_mem
      · intro x y _ _ hx hy r
        simpa only [smul_add] using S.add_mem (hx r) (hy r)
      · intro a x _ hx r
        simpa only [mul_smul] using hx (r * a)
    rw [← hS]
    simpa only [SetLike.mem_coe, one_smul] using hsmul 1

end Submodule
