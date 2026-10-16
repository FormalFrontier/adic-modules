/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Group.ZPow
public import AdicModules.Topology.Algebra.Submodule
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Tactic.NormNum

/-!
# Submodule closure clients

The neighborhood-basis formula for submodule closure is applied to the
nonnegative integers as an `ℕ`-submodule in the discrete topology, to the even
integers in the indiscrete topology, and to submodules in the canonical
`(2)`-adic integer topology.

The discrete model uses both a `Unit`-indexed basis and a proposition-indexed
basis. The indiscrete model has a nonzero proper submodule whose closure is top;
its `Bool`-indexed basis shows why the predicate selecting active indices cannot
be dropped. The ring models obtain fixed-scalar continuity from the canonical
integer action on a topological additive group,
`AddGroup.continuousConstSMul_int`.

## References

These models use Mathlib's nonnegative additive-submonoid/ℕ-submodule
correspondence, `AddGroup.continuousConstSMul_int` and discrete, indiscrete and
adic bases. The active-index closure formula comes from
`AdicModules.Topology.Algebra.Submodule`.
-/

@[expose] public section

open Filter Topology
open scoped Pointwise

namespace AdicModulesTest.SubmoduleClosure

section DiscreteIntegers

local instance : TopologicalSpace ℤ := ⊥
local instance : DiscreteTopology ℤ := discreteTopology_bot _

-- Neither group compatibility nor scalar continuity is assumed for this model.
private lemma isTopologicalAddGroup_discrete : IsTopologicalAddGroup ℤ := inferInstance
private lemma continuousConstSMul_nat_discrete : ContinuousConstSMul ℕ ℤ := inferInstance

private lemma discreteZeroBasis :
    (𝓝 (0 : ℤ)).HasBasis (fun _ : Unit ↦ True)
      (fun _ ↦ ((⊥ : Submodule ℕ ℤ) : Set ℤ)) := by
  simpa only [nhds_discrete, Submodule.bot_coe] using hasBasis_pure (0 : ℤ)

-- A proposition-valued index also gives a basis for the discrete topology.
private lemma discretePropZeroBasis : (𝓝 (0 : ℤ)).HasBasis (fun _ : True ↦ True)
    (fun _ ↦ ((⊥ : Submodule ℕ ℤ) : Set ℤ)) := by
  exact discreteZeroBasis.comp_surjective (g := fun _ : True ↦ ()) (by
    intro i
    cases i
    exact ⟨True.intro, rfl⟩)

private lemma continuous_two_nsmul_discrete :
    Continuous (fun z : ℤ ↦ (2 : ℕ) • z) := continuous_const_smul 2
private lemma continuous_neg_discrete : Continuous (fun z : ℤ ↦ -z) := continuous_neg

-- The cone is an existing additive submonoid, viewed through the canonical
-- order equivalence with `ℕ`-submodules. It is not inverse-closed.
private lemma one_mem_nonnegative : (1 : ℤ) ∈ (AddSubmonoid.nonneg ℤ).toNatSubmodule := by
  rw [← Submodule.mem_toAddSubmonoid, AddSubmonoid.toNatSubmodule_toAddSubmonoid]
  norm_num

private lemma neg_one_notMem_nonnegative : (-1 : ℤ) ∉ (AddSubmonoid.nonneg ℤ).toNatSubmodule := by
  rw [← Submodule.mem_toAddSubmonoid, AddSubmonoid.toNatSubmodule_toAddSubmonoid]
  norm_num

-- The closure formula computes the closure using the bottom submodule basis.
private lemma closure_nonnegative_eq_discrete_unit :
    (AddSubmonoid.nonneg ℤ).toNatSubmodule.topologicalClosure =
    (AddSubmonoid.nonneg ℤ).toNatSubmodule := by
  simpa only [sup_bot_eq, iInf_true, iInf_const] using
    (AddSubmonoid.nonneg ℤ).toNatSubmodule.topologicalClosure_eq_iInf_sup discreteZeroBasis

-- The same computation uses a basis indexed by the proposition `True`.
private lemma closure_nonnegative_eq_discrete_prop :
    (AddSubmonoid.nonneg ℤ).toNatSubmodule.topologicalClosure =
    (AddSubmonoid.nonneg ℤ).toNatSubmodule := by
  simpa only [sup_bot_eq, iInf_true] using
    (AddSubmonoid.nonneg ℤ).toNatSubmodule.topologicalClosure_eq_iInf_sup discretePropZeroBasis

-- The set-level formula agrees with the bundled submodule computation.
private lemma iInter_add_bot_eq_closure_nonnegative :
    (⋂ (_i : Unit) (_ : True),
      ((AddSubmonoid.nonneg ℤ).toNatSubmodule : Set ℤ) +
        ((⊥ : Submodule ℕ ℤ) : Set ℤ)) =
      closure ((AddSubmonoid.nonneg ℤ).toNatSubmodule : Set ℤ) :=
  discreteZeroBasis.iInter_add_right_eq_closure

end DiscreteIntegers

section IndiscreteIntegers

local instance : TopologicalSpace ℤ := ⊤

private lemma indiscreteTopology_int : IndiscreteTopology ℤ := inferInstance
private lemma isTopologicalAddGroup_indiscrete : IsTopologicalAddGroup ℤ := inferInstance

private lemma not_t2Space_indiscrete : ¬ T2Space ℤ := by
  intro h
  let := h
  have h01 : (0 : ℤ) = 1 := (Inseparable.all (0 : ℤ) 1).eq
  norm_num at h01

private lemma indiscreteZeroBasis :
    (𝓝 (0 : ℤ)).HasBasis (fun _ : Unit ↦ True)
      (fun _ ↦ ((⊤ : Submodule ℤ ℤ) : Set ℤ)) := by
  simpa only [nhds_top, Submodule.top_coe] using (hasBasis_top (α := ℤ))

-- An inactive index may carry a set that is not a neighborhood. Only the
-- selected indices participate in this genuine neighborhood basis.
private lemma indiscreteBoolBasis :
    (𝓝 (0 : ℤ)).HasBasis (fun i : Bool ↦ i = true)
      (fun i ↦ ((if i then ⊤ else ⊥ : Submodule ℤ ℤ) : Set ℤ)) := by
  refine indiscreteZeroBasis.to_hasBasis ?_ ?_
  · intro _ _
    exact ⟨true, rfl, by simp⟩
  · intro i hi
    subst i
    exact ⟨(), trivial, by simp⟩

-- Classify the existing model by its basis, rather than building a new bundle.
local instance : IsLinearTopology ℤ ℤ :=
  IsLinearTopology.mk_of_hasBasis ℤ indiscreteZeroBasis

-- The canonical integer action is continuous on every topological additive group.
-- Its fixed-scalar continuity requires no topology on the scalar ring.
private lemma continuous_two_zsmul_indiscrete : Continuous (fun z : ℤ ↦ (2 : ℤ) • z) := by
  let := AddGroup.continuousConstSMul_int (A := ℤ)
  exact continuous_const_smul 2

private lemma closure_bot_eq_top_indiscrete : (⊥ : Submodule ℤ ℤ).topologicalClosure = ⊤ := by
  let := AddGroup.continuousConstSMul_int (A := ℤ)
  simpa only [sup_top_eq, iInf_true, iInf_const] using
    (⊥ : Submodule ℤ ℤ).topologicalClosure_eq_iInf_sup indiscreteZeroBasis

-- The even integers form a nonzero proper submodule, not just a bottom/top case.
private lemma two_mem_span_two_and_one_notMem_span_two :
    (2 : ℤ) ∈ (Ideal.span {(2 : ℤ)} : Submodule ℤ ℤ) ∧
    (1 : ℤ) ∉ (Ideal.span {(2 : ℤ)} : Submodule ℤ ℤ) := by
  constructor
  · exact Ideal.subset_span (Set.mem_singleton _)
  · rw [Ideal.mem_span_singleton]
    norm_num

-- The active index is `true`, where the basis submodule is top.
private lemma closure_span_two_eq_top_indiscrete :
    (Ideal.span {(2 : ℤ)} : Submodule ℤ ℤ).topologicalClosure = ⊤ := by
  let := AddGroup.continuousConstSMul_int (A := ℤ)
  rw [Submodule.topologicalClosure_eq_iInf_sup _ indiscreteBoolBasis]
  apply top_unique
  refine le_iInf fun i ↦ le_iInf fun hi ↦ ?_
  subst i
  simp

-- These finite lattice computations do not use a closure theorem.
-- The valid-index infimum is top, whereas forgetting the predicate yields N.
private lemma hasBasis_indiscrete_bool_and_iInf_sup_eq_top :
    (𝓝 (0 : ℤ)).HasBasis (fun i : Bool ↦ i = true)
    (fun i ↦ ((if i then ⊤ else ⊥ : Submodule ℤ ℤ) : Set ℤ)) ∧
    (⨅ (i : Bool) (_ : i = true),
      (Ideal.span {(2 : ℤ)} : Submodule ℤ ℤ) ⊔ (if i then ⊤ else ⊥)) = ⊤ := by
  constructor
  · exact indiscreteBoolBasis
  · apply top_unique
    refine le_iInf fun i ↦ le_iInf fun hi ↦ ?_
    subst i
    simp

private lemma iInf_sup_span_two_all_bool : (⨅ i : Bool,
    (Ideal.span {(2 : ℤ)} : Submodule ℤ ℤ) ⊔ (if i then ⊤ else ⊥)) =
      (Ideal.span {(2 : ℤ)} : Submodule ℤ ℤ) := by
  apply le_antisymm
  · exact (iInf_le _ false).trans (by simp)
  · exact le_iInf fun _ ↦ le_sup_left

-- Closure genuinely adds an element to this nonzero proper submodule.
private lemma one_mem_closure_span_two_and_notMem_span_two :
    (1 : ℤ) ∈ closure ((Ideal.span {(2 : ℤ)} : Submodule ℤ ℤ) : Set ℤ) ∧
    (1 : ℤ) ∉ (Ideal.span {(2 : ℤ)} : Submodule ℤ ℤ) := by
  constructor
  · rw [closure_indiscrete ⟨0, Submodule.zero_mem _⟩]
    exact Set.mem_univ _
  · rw [Ideal.mem_span_singleton]
    norm_num

private lemma iInter_add_bot_top_eq_closure_bot :
    (⋂ (_i : Unit) (_ : True), ((⊥ : Submodule ℤ ℤ) : Set ℤ) +
      ((⊤ : Submodule ℤ ℤ) : Set ℤ)) =
      closure ((⊥ : Submodule ℤ ℤ) : Set ℤ) :=
  indiscreteZeroBasis.iInter_add_right_eq_closure

end IndiscreteIntegers

section AdicIntegers

local instance : TopologicalSpace ℤ := (Ideal.span {(2 : ℤ)}).adicTopology
local instance : IsTopologicalAddGroup ℤ :=
  (Ideal.span {(2 : ℤ)}).ringFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup
local instance : IsLinearTopology ℤ ℤ := (Ideal.span {(2 : ℤ)}).isLinearTopology

-- Consume the canonical additive group filter-basis API, not a reconstructed basis.
private lemma nhds_zero_hasBasis_ringFilterBasis_span_two : (𝓝 (0 : ℤ)).HasBasis
    (fun V : Set ℤ ↦ V ∈ (Ideal.span {(2 : ℤ)}).ringFilterBasis.toAddGroupFilterBasis)
    id :=
  (Ideal.span {(2 : ℤ)}).ringFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis

private lemma nhds_zero_hasBasis_span_two_pow : (𝓝 (0 : ℤ)).HasBasis (fun _ : ℕ ↦ True)
    (fun n ↦ (((Ideal.span {(2 : ℤ)}) ^ n : Submodule ℤ ℤ) : Set ℤ)) :=
  (Ideal.span {(2 : ℤ)}).hasBasis_nhds_zero_adic

private lemma continuous_two_zsmul_adic : Continuous (fun z : ℤ ↦ (2 : ℤ) • z) := by
  let := AddGroup.continuousConstSMul_int (A := ℤ)
  exact continuous_const_smul 2

-- The canonical powers of `(2)` specialize the closure formula to the adic topology.
private lemma closure_eq_iInf_sup_span_two_pow_adic (N : Submodule ℤ ℤ) :
    N.topologicalClosure =
      ⨅ n : ℕ, N ⊔ ((Ideal.span {(2 : ℤ)}) ^ n : Submodule ℤ ℤ) := by
  let := AddGroup.continuousConstSMul_int (A := ℤ)
  simpa only [iInf_true] using
    N.topologicalClosure_eq_iInf_sup (Ideal.span {(2 : ℤ)}).hasBasis_nhds_zero_adic

-- The first nontrivial basis element is a neighborhood, nonzero and proper.
private lemma span_two_mem_nhds_zero_adic :
    ((Ideal.span {(2 : ℤ)} : Submodule ℤ ℤ) : Set ℤ) ∈ 𝓝 (0 : ℤ) := by
  simpa using (Ideal.span {(2 : ℤ)}).hasBasis_nhds_zero_adic.mem_of_mem (i := 1) trivial

private lemma two_mem_span_two_adic : (2 : ℤ) ∈ (Ideal.span {(2 : ℤ)} : Submodule ℤ ℤ) :=
  Ideal.subset_span (Set.mem_singleton _)

private lemma one_notMem_span_two_adic : (1 : ℤ) ∉ (Ideal.span {(2 : ℤ)} : Submodule ℤ ℤ) := by
  rw [Ideal.mem_span_singleton]
  norm_num

end AdicIntegers

end AdicModulesTest.SubmoduleClosure
