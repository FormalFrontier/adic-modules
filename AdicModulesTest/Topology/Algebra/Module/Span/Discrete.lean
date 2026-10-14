/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Spans with a discrete real module factor

The rational image is a dense proper subsemiring of the usual real numbers.
The canonical real module `Fin 1 → ℝ` is given the discrete topology, without
changing the topology of the scalar field. Its rational span of the constant
unit is closed and proper, whereas its real span is the whole module.
The coefficient map at this unit is not continuous, even though addition and
multiplication by every fixed scalar are continuous.

In the product of the usual real line and this discrete module, the generator
`(1, 0)` has a continuous coefficient map. Its rational and real spans have the
same proper closure, the real first axis. The coefficient map at the second
unit is not continuous. Thus continuity at the chosen generators is strictly
weaker than continuity at every module element or joint scalar continuity.

## References

* Mathlib's `Rat.castHom`, `RingHom.rangeS` and `Rat.denseRange_cast` describe
  the rational scalar image, and `irrational_sqrt_two` witnesses its properness.
* Mathlib's `Submodule.mem_span_singleton` computes the concrete spans using
  the canonical Pi, Prod and restricted subsemiring actions. The constant
  vectors use `Function.const_injective` and `Fin.eq_zero`.
* Mathlib's `Continuous.range_subset_closure_image_dense` and `closure_minimal`
  compute the first-axis closure independently of any span-comparison theorem.
* Mathlib's discrete topology and product continuity APIs, together with
  `not_isOpen_singleton` on the usual real line, distinguish fixed-scalar
  continuity from coefficient continuity.
-/

@[expose] public section

noncomputable section

open Topology

namespace AdicModulesTest.Span.Discrete

private def rationalScalars : Subsemiring ℝ := (Rat.castHom ℝ).rangeS

private lemma rationalScalars_mem_iff (r : ℝ) :
    r ∈ rationalScalars ↔ ∃ q : ℚ, (q : ℝ) = r :=
  RingHom.mem_rangeS

private lemma rationalScalars_dense : Dense (rationalScalars : Set ℝ) := by
  exact Rat.denseRange_cast

private lemma rationalScalars_sqrt_not_mem : Real.sqrt 2 ∉ rationalScalars := by
  rw [rationalScalars_mem_iff]
  exact irrational_sqrt_two

private lemma rationalScalars_ne_top : rationalScalars ≠ ⊤ := by
  intro h
  apply rationalScalars_sqrt_not_mem
  rw [h]
  exact Subsemiring.mem_top _

private abbrev DiscreteLine := Fin 1 → ℝ

private def constantVector (r : ℝ) : DiscreteLine := fun (_ : Fin 1) ↦ r

@[simp] private lemma constantVector_apply (r : ℝ) (i : Fin 1) :
    constantVector r i = r := rfl

private lemma constantVector_zero : constantVector 0 = 0 := rfl

private lemma constantVector_injective : Function.Injective constantVector :=
  Function.const_injective

private lemma constantVector_eq (x : DiscreteLine) : constantVector (x 0) = x := by
  funext i
  exact congrArg x (Fin.eq_zero i).symm

private lemma smul_discrete_unit (r : ℝ) : r • constantVector 1 = constantVector r := by
  funext i
  exact mul_one r

private lemma smul_discrete_unit_restrict (a : rationalScalars) :
    a • constantVector 1 = constantVector (a : ℝ) := by
  rw [Subsemiring.smul_def, smul_discrete_unit]

private lemma discrete_unit_ne_zero : constantVector 1 ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h (0 : Fin 1))

section DiscreteTopology

-- Only the module function type is discrete; the scalar ℝ keeps its usual topology.
private local instance : TopologicalSpace DiscreteLine := ⊥
private local instance : DiscreteTopology DiscreteLine := discreteTopology_bot _
private local instance : ContinuousAdd DiscreteLine := ⟨continuous_of_discreteTopology⟩

private lemma discrete_add_continuous :
    Continuous (fun p : DiscreteLine × DiscreteLine ↦ p.1 + p.2) :=
  continuous_of_discreteTopology

private lemma discrete_separatelyContinuousAdd : SeparatelyContinuousAdd DiscreteLine :=
  inferInstance

private lemma discrete_fixed_smul_continuous (r : ℝ) :
    Continuous (fun x : DiscreteLine ↦ r • x) :=
  continuous_of_discreteTopology

private lemma discrete_small_span_mem_iff (x : DiscreteLine) :
    x ∈ Submodule.span rationalScalars {constantVector 1} ↔
      ∃ q : ℚ, constantVector (q : ℝ) = x := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    rw [smul_discrete_unit_restrict] at ha
    obtain ⟨q, hq⟩ := (rationalScalars_mem_iff (a : ℝ)).mp a.property
    exact ⟨q, (congrArg constantVector hq).trans ha⟩
  · rintro ⟨q, hq⟩
    let a : rationalScalars := ⟨(q : ℝ), (rationalScalars_mem_iff (q : ℝ)).mpr ⟨q, rfl⟩⟩
    exact ⟨a, (smul_discrete_unit_restrict a).trans hq⟩

private lemma discrete_real_span_eq_top :
    Submodule.span ℝ {constantVector 1} = ⊤ := by
  apply (Submodule.span_singleton_eq_top_iff ℝ (constantVector 1)).mpr
  intro x
  exact ⟨x 0, (smul_discrete_unit (x 0)).trans (constantVector_eq x)⟩

private lemma discrete_small_span_isClosed :
    IsClosed (Submodule.span rationalScalars {constantVector 1} : Set DiscreteLine) :=
  isClosed_discrete _

private lemma discrete_small_closure_eq :
    closure (Submodule.span rationalScalars {constantVector 1} : Set DiscreteLine) =
      (Submodule.span rationalScalars {constantVector 1} : Set DiscreteLine) :=
  discrete_small_span_isClosed.closure_eq

private lemma discrete_sqrt_not_mem :
    constantVector (Real.sqrt 2) ∉ Submodule.span rationalScalars {constantVector 1} := by
  intro h
  obtain ⟨q, hq⟩ := (discrete_small_span_mem_iff (constantVector (Real.sqrt 2))).mp h
  exact irrational_sqrt_two ⟨q, constantVector_injective hq⟩

private lemma discrete_sqrt_separates :
    constantVector (Real.sqrt 2) ∈ Submodule.span ℝ {constantVector 1} ∧
    constantVector (Real.sqrt 2) ∈
      closure (Submodule.span ℝ {constantVector 1} : Set DiscreteLine) ∧
    constantVector (Real.sqrt 2) ∉
      closure (Submodule.span rationalScalars {constantVector 1} : Set DiscreteLine) := by
  have hbig : constantVector (Real.sqrt 2) ∈ Submodule.span ℝ {constantVector 1} := by
    rw [discrete_real_span_eq_top]
    exact Submodule.mem_top
  refine ⟨hbig, subset_closure hbig, ?_⟩
  rw [discrete_small_closure_eq]
  exact discrete_sqrt_not_mem

private lemma discrete_small_span_ne_top :
    Submodule.span rationalScalars {constantVector 1} ≠ ⊤ := by
  intro h
  apply discrete_sqrt_not_mem
  rw [h]
  exact Submodule.mem_top

private lemma discrete_closures_ne :
    closure (Submodule.span rationalScalars {constantVector 1} : Set DiscreteLine) ≠
      closure (Submodule.span ℝ {constantVector 1} : Set DiscreteLine) := by
  intro h
  apply discrete_sqrt_separates.2.2
  rw [h]
  exact discrete_sqrt_separates.2.1

private lemma coefficient_zero_preimage :
    (fun r : ℝ ↦ r • constantVector 1) ⁻¹' ({0} : Set DiscreteLine) = {0} := by
  ext r
  simp only [Set.mem_preimage, Set.mem_singleton_iff, smul_discrete_unit]
  constructor
  · intro h
    exact congrFun h (0 : Fin 1)
  · rintro rfl
    exact constantVector_zero

private lemma coefficient_not_continuous :
    ¬ Continuous (fun r : ℝ ↦ r • constantVector 1) := by
  intro h
  have hopen := (isOpen_discrete ({0} : Set DiscreteLine)).preimage h
  rw [coefficient_zero_preimage] at hopen
  exact not_isOpen_singleton (0 : ℝ) hopen

private lemma discrete_generators_not_continuous :
    ¬ (∀ (m : DiscreteLine), m ∈ ({constantVector 1} : Set DiscreteLine) →
      Continuous (fun r : ℝ ↦ r • m)) := by
  intro h
  exact coefficient_not_continuous (h (constantVector 1) (Set.mem_singleton _))

private def firstAxisPoint (r : ℝ) : ℝ × DiscreteLine := (r, 0)

@[simp] private lemma firstAxisPoint_fst (r : ℝ) : (firstAxisPoint r).1 = r := rfl

@[simp] private lemma firstAxisPoint_snd (r : ℝ) : (firstAxisPoint r).2 = 0 := rfl

private lemma smul_firstAxisPoint (r : ℝ) :
    r • firstAxisPoint 1 = firstAxisPoint r := by
  apply Prod.ext
  · exact mul_one r
  · exact smul_zero r

private lemma smul_firstAxisPoint_restrict (a : rationalScalars) :
    a • firstAxisPoint 1 = firstAxisPoint (a : ℝ) := by
  rw [Subsemiring.smul_def, smul_firstAxisPoint]

private lemma firstAxisPoint_continuous : Continuous firstAxisPoint :=
  continuous_id.prodMk continuous_const

private lemma mixed_add_continuous :
    Continuous (fun p : (ℝ × DiscreteLine) × (ℝ × DiscreteLine) ↦ p.1 + p.2) :=
  continuous_add

private lemma mixed_separatelyContinuousAdd : SeparatelyContinuousAdd (ℝ × DiscreteLine) :=
  inferInstance

private lemma mixed_fixed_smul_continuous (r : ℝ) :
    Continuous (fun x : ℝ × DiscreteLine ↦ r • x) :=
  ((continuous_const_smul r : Continuous (fun s : ℝ ↦ r • s)).comp continuous_fst).prodMk
    ((discrete_fixed_smul_continuous r).comp continuous_snd)

private lemma mixed_generators_continuous :
    ∀ (m : ℝ × DiscreteLine), m ∈ ({firstAxisPoint 1} : Set (ℝ × DiscreteLine)) →
      Continuous (fun r : ℝ ↦ r • m) := by
  intro m hm
  have hm' : m = firstAxisPoint 1 := Set.mem_singleton_iff.mp hm
  subst m
  simpa only [smul_firstAxisPoint] using firstAxisPoint_continuous

private lemma mixed_small_span_eq_image :
    (Submodule.span rationalScalars {firstAxisPoint 1} : Set (ℝ × DiscreteLine)) =
      firstAxisPoint '' (rationalScalars : Set ℝ) := by
  ext x
  change x ∈ Submodule.span rationalScalars {firstAxisPoint 1} ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(a : ℝ), a.property, (smul_firstAxisPoint_restrict a).symm.trans ha⟩
  · rintro ⟨r, hr, hx⟩
    exact ⟨⟨r, hr⟩, (smul_firstAxisPoint_restrict ⟨r, hr⟩).trans hx⟩

private lemma mixed_small_span_mem_iff (x : ℝ × DiscreteLine) :
    x ∈ Submodule.span rationalScalars {firstAxisPoint 1} ↔
      ∃ q : ℚ, firstAxisPoint (q : ℝ) = x := by
  change x ∈ (Submodule.span rationalScalars {firstAxisPoint 1} : Set (ℝ × DiscreteLine)) ↔ _
  rw [mixed_small_span_eq_image]
  constructor
  · rintro ⟨r, hr, hx⟩
    obtain ⟨q, rfl⟩ := (rationalScalars_mem_iff r).mp hr
    exact ⟨q, hx⟩
  · rintro ⟨q, hq⟩
    exact ⟨(q : ℝ), (rationalScalars_mem_iff (q : ℝ)).mpr ⟨q, rfl⟩, hq⟩

private lemma mixed_real_span_mem_iff (x : ℝ × DiscreteLine) :
    x ∈ Submodule.span ℝ {firstAxisPoint 1} ↔ x.2 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    simpa only [smul_firstAxisPoint] using firstAxisPoint_snd r
  · intro hx
    exact ⟨x.1, (smul_firstAxisPoint x.1).trans (Prod.ext rfl hx.symm)⟩

private lemma mixed_real_span_eq_axis :
    (Submodule.span ℝ {firstAxisPoint 1} : Set (ℝ × DiscreteLine)) =
      {x : ℝ × DiscreteLine | x.2 = 0} := by
  ext x
  exact mixed_real_span_mem_iff x

private lemma mixed_axis_isClosed : IsClosed {x : ℝ × DiscreteLine | x.2 = 0} := by
  change IsClosed (Prod.snd ⁻¹' ({0} : Set DiscreteLine))
  exact (isClosed_discrete ({0} : Set DiscreteLine)).preimage continuous_snd

private lemma mixed_small_closure_eq_axis :
    closure (Submodule.span rationalScalars {firstAxisPoint 1} : Set (ℝ × DiscreteLine)) =
      {x : ℝ × DiscreteLine | x.2 = 0} := by
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ mixed_axis_isClosed
    intro x hx
    obtain ⟨q, rfl⟩ := (mixed_small_span_mem_iff x).mp hx
    exact firstAxisPoint_snd (q : ℝ)
  · intro x hx
    rw [mixed_small_span_eq_image]
    apply firstAxisPoint_continuous.range_subset_closure_image_dense rationalScalars_dense
    exact ⟨x.1, Prod.ext rfl hx.symm⟩

private lemma mixed_real_closure_eq_axis :
    closure (Submodule.span ℝ {firstAxisPoint 1} : Set (ℝ × DiscreteLine)) =
      {x : ℝ × DiscreteLine | x.2 = 0} := by
  rw [mixed_real_span_eq_axis]
  exact mixed_axis_isClosed.closure_eq

private lemma mixed_closures_eq :
    closure (Submodule.span rationalScalars {firstAxisPoint 1} : Set (ℝ × DiscreteLine)) =
      closure (Submodule.span ℝ {firstAxisPoint 1} : Set (ℝ × DiscreteLine)) := by
  rw [mixed_small_closure_eq_axis, mixed_real_closure_eq_axis]

private def secondUnit : ℝ × DiscreteLine := (0, constantVector 1)

@[simp] private lemma secondUnit_snd : secondUnit.2 = constantVector 1 := rfl

private lemma smul_secondUnit_snd (r : ℝ) : (r • secondUnit).2 = constantVector r :=
  smul_discrete_unit r

private lemma mixed_second_unit_not_mem :
    secondUnit ∉ Submodule.span ℝ {firstAxisPoint 1} := by
  intro h
  exact discrete_unit_ne_zero ((mixed_real_span_mem_iff secondUnit).mp h)

private lemma mixed_second_unit_not_mem_closures :
    secondUnit ∉ closure (Submodule.span rationalScalars {firstAxisPoint 1} :
      Set (ℝ × DiscreteLine)) ∧
    secondUnit ∉ closure (Submodule.span ℝ {firstAxisPoint 1} : Set (ℝ × DiscreteLine)) := by
  rw [mixed_small_closure_eq_axis, mixed_real_closure_eq_axis]
  exact ⟨discrete_unit_ne_zero, discrete_unit_ne_zero⟩

private lemma mixed_sqrt_not_mem :
    firstAxisPoint (Real.sqrt 2) ∉ Submodule.span rationalScalars {firstAxisPoint 1} := by
  intro h
  obtain ⟨q, hq⟩ := (mixed_small_span_mem_iff (firstAxisPoint (Real.sqrt 2))).mp h
  exact irrational_sqrt_two ⟨q, congrArg Prod.fst hq⟩

private lemma mixed_sqrt_mem_closure :
    firstAxisPoint (Real.sqrt 2) ∈
      closure (Submodule.span rationalScalars {firstAxisPoint 1} : Set (ℝ × DiscreteLine)) := by
  simpa only [mixed_small_closure_eq_axis, Set.mem_ofPred_eq] using
    firstAxisPoint_snd (Real.sqrt 2)

private lemma mixed_second_coefficient_not_continuous :
    ¬ Continuous (fun r : ℝ ↦ r • secondUnit) := by
  intro h
  apply coefficient_not_continuous
  simpa only [smul_secondUnit_snd, smul_discrete_unit] using h.snd

private lemma mixed_not_all_coefficients_continuous :
    ¬ (∀ m : ℝ × DiscreteLine, Continuous (fun r : ℝ ↦ r • m)) := by
  intro h
  exact mixed_second_coefficient_not_continuous (h secondUnit)

private lemma mixed_not_continuousSMul : ¬ ContinuousSMul ℝ (ℝ × DiscreteLine) := by
  intro h
  apply mixed_second_coefficient_not_continuous
  exact h.continuous_smul.comp
    ((continuous_id : Continuous (fun r : ℝ ↦ r)).prodMk continuous_const)

end DiscreteTopology

end AdicModulesTest.Span.Discrete
