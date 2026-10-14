/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic

/-!
# Empty and zero spans, and indiscrete module boundaries

For any semiring acting on an additive commutative monoid, the spans of the empty
set and of the zero singleton are the bottom submodules. Their underlying sets
are `{0}`, so their set closures are `closure {0}`. Restriction to a subsemiring
uses the same carrier and the canonical restricted action. These calculations
need no density or continuity assumptions, and the scalar and module universes
are independent. The coefficient maps at zero are continuous for independently
chosen scalar and module topologies.

A subsingleton module is a degenerate case: every span, even that of the empty
set, has underlying set `univ`, as does its closure. This is not evidence of a
nonzero generator or of a nontrivial module.

For the canonical rational self-module with the indiscrete topology, `{0}` is
dense but not closed. The nonzero element `1` belongs to the closures of the empty
and zero-generated spans, although it belongs to neither span. Addition is
separately continuous and every coefficient map is continuous. Thus neither
`closure {0} = {0}` nor closedness of the bottom submodule follows without a
separation hypothesis. The generic boundary calculations do not impose `T1Space`,
joint continuity of addition, or joint scalar continuity.

## References

* Mathlib's `Submodule.span_empty`, `Submodule.span_zero_singleton`, and
  `Submodule.bot_coe` give the algebraic zero-span calculations.
* Mathlib's subsingleton submodule instance and `closure_univ` give the
  subsingleton boundary.
* Mathlib's `dense_indiscrete`, `closure_indiscrete`, and
  `continuous_of_indiscreteTopology` give the indiscrete controls.
* Mathlib's `Subsemiring.module` and `Subsemiring.smul_def` provide canonical
  restriction of scalars; `continuousAdd_of_indiscreteTopology` supplies the
  addition instance in the rational example.
-/

@[expose] public section GeneralExamples

open Set Topology

universe u v

namespace AdicModulesTest.Span.Boundary

section General

variable {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] (A : Subsemiring R)

/-- Empty spans over the ambient semiring and its subsemiring are bottom, and
both underlying-set closures are the closure of the zero singleton. No closedness
of that singleton is asserted. -/
example :
    Submodule.span A (∅ : Set M) = ⊥ ∧
    Submodule.span R (∅ : Set M) = ⊥ ∧
    closure (Submodule.span A (∅ : Set M) : Set M) = closure ({0} : Set M) ∧
    closure (Submodule.span R (∅ : Set M) : Set M) = closure ({0} : Set M) := by
  refine ⟨Submodule.span_empty, Submodule.span_empty, ?_, ?_⟩
  · rw [Submodule.span_empty, Submodule.bot_coe]
  · rw [Submodule.span_empty, Submodule.bot_coe]

/-- Zero-generated spans are bottom for either canonical scalar action. Their
underlying-set closures are `closure {0}`, which need not equal `{0}`. -/
example :
    Submodule.span A ({0} : Set M) = ⊥ ∧
    Submodule.span R ({0} : Set M) = ⊥ ∧
    closure (Submodule.span A ({0} : Set M) : Set M) = closure ({0} : Set M) ∧
    closure (Submodule.span R ({0} : Set M) : Set M) = closure ({0} : Set M) := by
  refine ⟨Submodule.span_zero_singleton A, Submodule.span_zero_singleton R, ?_, ?_⟩
  · rw [Submodule.span_zero_singleton, Submodule.bot_coe]
  · rw [Submodule.span_zero_singleton, Submodule.bot_coe]

/-- In a subsingleton module, every generating set gives top spans and universal
underlying-set closures. The generating set is arbitrary, including the empty set. -/
example [Subsingleton M] (E : Set M) :
    Submodule.span A E = ⊤ ∧ Submodule.span R E = ⊤ ∧
    closure (Submodule.span A E : Set M) = univ ∧
    closure (Submodule.span R E : Set M) = univ := by
  have hA : Submodule.span A E = ⊤ := Subsingleton.elim _ _
  have hR : Submodule.span R E = ⊤ := Subsingleton.elim _ _
  refine ⟨hA, hR, ?_, ?_⟩
  · rw [hA, Submodule.top_coe, closure_univ]
  · rw [hR, Submodule.top_coe, closure_univ]

variable [TopologicalSpace R]

/-- Generatorwise coefficient continuity is vacuous for the empty set and is
constant-map continuity for the zero singleton, for arbitrary independent topologies. -/
example :
    (∀ m ∈ (∅ : Set M), Continuous (fun r : R => r • m)) ∧
    (∀ m ∈ ({0} : Set M), Continuous (fun r : R => r • m)) := by
  constructor
  · intro m hm
    exact False.elim hm
  · intro m hm
    obtain rfl := Set.mem_singleton_iff.mp hm
    simpa only [smul_zero] using
      (continuous_const : Continuous (fun _ : R => (0 : M)))

/-- A subsingleton module has separately continuous addition and continuous
coefficient maps at every element, for arbitrary scalar and module topologies. -/
example [Subsingleton M] :
    SeparatelyContinuousAdd M ∧ ∀ m : M, Continuous (fun r : R => r • m) := by
  exact ⟨inferInstance, fun _ => continuous_of_indiscreteTopology⟩

end General

end AdicModulesTest.Span.Boundary

end GeneralExamples

namespace AdicModulesTest.Span.Boundary.RationalIndiscrete

open Set Topology

-- The rational scalar field and its canonical self-module both have this topology.
local instance rationalTopology : TopologicalSpace ℚ := ⊤

private theorem module_nontrivial : Nontrivial ℚ := inferInstance

private theorem self_smul_eq_mul (r m : ℚ) : r • m = r * m := by
  simp only [smul_eq_mul]

private theorem restricted_smul_eq_mul (A : Subsemiring ℚ) (a : A) (m : ℚ) :
    a • m = (a : ℚ) * m := by
  rw [Subsemiring.smul_def, self_smul_eq_mul]

private theorem separately_continuous_add : SeparatelyContinuousAdd ℚ := inferInstance

private theorem coefficients_continuous (m : ℚ) :
    Continuous (fun r : ℚ => r • m) :=
  continuous_of_indiscreteTopology

private theorem generator_coefficients_continuous (E : Set ℚ) :
    ∀ m ∈ E, Continuous (fun r : ℚ => r • m) :=
  fun m _ => coefficients_continuous m

private theorem fixed_scalar_continuous (r : ℚ) :
    Continuous (fun m : ℚ => r • m) :=
  continuous_of_indiscreteTopology

private theorem subsemiring_dense (A : Subsemiring ℚ) : Dense (A : Set ℚ) :=
  dense_indiscrete ⟨0, A.zero_mem⟩

private theorem zero_closure_eq_univ : closure ({0} : Set ℚ) = univ :=
  closure_indiscrete (Set.singleton_nonempty 0)

private theorem one_mem_zero_closure : (1 : ℚ) ∈ closure ({0} : Set ℚ) := by
  rw [zero_closure_eq_univ]
  exact Set.mem_univ _

private theorem zero_singleton_not_closed : ¬ IsClosed ({0} : Set ℚ) := by
  intro h
  have hmem : (1 : ℚ) ∈ ({0} : Set ℚ) := h.closure_eq ▸ one_mem_zero_closure
  exact one_ne_zero (Set.mem_singleton_iff.mp hmem)

private theorem not_t1Space : ¬ T1Space ℚ := by
  intro h
  let : T1Space ℚ := h
  exact zero_singleton_not_closed isClosed_singleton

private theorem empty_span_closures_eq_univ (A : Subsemiring ℚ) :
    closure (Submodule.span A (∅ : Set ℚ) : Set ℚ) = univ ∧
    closure (Submodule.span ℚ (∅ : Set ℚ) : Set ℚ) = univ := by
  constructor <;> rw [Submodule.span_empty, Submodule.bot_coe, zero_closure_eq_univ]

private theorem zero_span_closures_eq_univ (A : Subsemiring ℚ) :
    closure (Submodule.span A ({0} : Set ℚ) : Set ℚ) = univ ∧
    closure (Submodule.span ℚ ({0} : Set ℚ) : Set ℚ) = univ := by
  constructor <;>
    rw [Submodule.span_zero_singleton, Submodule.bot_coe, zero_closure_eq_univ]

private theorem empty_and_zero_spans_dense (A : Subsemiring ℚ) :
    Dense (Submodule.span A (∅ : Set ℚ) : Set ℚ) ∧
    Dense (Submodule.span ℚ (∅ : Set ℚ) : Set ℚ) ∧
    Dense (Submodule.span A ({0} : Set ℚ) : Set ℚ) ∧
    Dense (Submodule.span ℚ ({0} : Set ℚ) : Set ℚ) := by
  have hE := empty_span_closures_eq_univ A
  have hZ := zero_span_closures_eq_univ A
  exact ⟨dense_iff_closure_eq.mpr hE.1, dense_iff_closure_eq.mpr hE.2,
    dense_iff_closure_eq.mpr hZ.1, dense_iff_closure_eq.mpr hZ.2⟩

private theorem one_outside_spans (A : Subsemiring ℚ) :
    (1 : ℚ) ∉ Submodule.span A (∅ : Set ℚ) ∧
    (1 : ℚ) ∉ Submodule.span ℚ (∅ : Set ℚ) ∧
    (1 : ℚ) ∉ Submodule.span A ({0} : Set ℚ) ∧
    (1 : ℚ) ∉ Submodule.span ℚ ({0} : Set ℚ) := by
  simp only [Submodule.span_empty, Submodule.span_zero_singleton, Submodule.mem_bot,
    one_ne_zero, not_false_eq_true, and_self]

private theorem one_in_span_closures (A : Subsemiring ℚ) :
    (1 : ℚ) ∈ closure (Submodule.span A (∅ : Set ℚ) : Set ℚ) ∧
    (1 : ℚ) ∈ closure (Submodule.span ℚ (∅ : Set ℚ) : Set ℚ) ∧
    (1 : ℚ) ∈ closure (Submodule.span A ({0} : Set ℚ) : Set ℚ) ∧
    (1 : ℚ) ∈ closure (Submodule.span ℚ ({0} : Set ℚ) : Set ℚ) := by
  have hE := empty_span_closures_eq_univ A
  have hZ := zero_span_closures_eq_univ A
  rw [hE.1, hE.2, hZ.1, hZ.2]
  exact ⟨Set.mem_univ _, Set.mem_univ _, Set.mem_univ _, Set.mem_univ _⟩

end AdicModulesTest.Span.Boundary.RationalIndiscrete
