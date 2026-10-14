/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Separation.Hausdorff

import Mathlib.Tactic.NormNum.GCD

/-!
# Indiscrete rational scalars acting on a discrete module

Equip `ℚ` with the indiscrete topology and its independent module copy
`ULift.{v} ℚ` with the discrete topology. The action and additive group on the
copy are Mathlib's `ULift` instances; its universe is independent of the scalar
universe. The range subsemiring of integer casts is dense and proper.

For the singleton consisting of the transported `1`, the integer span and the
range-subsemiring span coincide. They are closed and proper, excluding the
transported `1 / 2`, while the rational span is the whole module. Addition is
separately continuous and every fixed-scalar action is continuous. Nevertheless,
the coefficient map at this generator is not continuous: the preimage of the
open singleton `{0}` is the nonopen scalar singleton `{0}`.

Thus continuity of each fixed-scalar action does not replace continuity of the
coefficient maps at the selected generators in a dense-subsemiring span-closure
statement. This is a rational-ring example, not a restriction on the generality
of such a statement.

## References

* Mathlib's `ULift` algebra and module transport by Kim Morrison, integer-module
  interfaces by Nathaniel Thomas and collaborators, singleton-span interfaces
  by Johannes Hölzl and collaborators, and topology interfaces by Yury
  Kudryashov and collaborators supply the constructions and proof APIs.
-/

universe v

namespace Rat.IndiscreteScalar

private abbrev RationalCopy : Type v := ULift.{v} ℚ
private abbrev integerScalars : Subsemiring ℚ := (Int.castRingHom ℚ).rangeS

local instance : TopologicalSpace ℚ := ⊤
local instance : TopologicalSpace RationalCopy.{v} := ⊥
local instance : DiscreteTopology RationalCopy.{v} := discreteTopology_bot RationalCopy.{v}

@[expose] public section

private lemma smul_up_one (r : ℚ) :
    r • (ULift.up (1 : ℚ) : RationalCopy.{v}) = ULift.up r := by
  apply ULift.ext
  change r * 1 = r
  exact mul_one r

private lemma integerScalar_smul_up_one (a : integerScalars) :
    a • (ULift.up (1 : ℚ) : RationalCopy.{v}) = ULift.up (a : ℚ) := by
  rw [Subsemiring.smul_def, smul_up_one]

private lemma int_smul_up_one (z : ℤ) :
    z • (ULift.up (1 : ℚ) : RationalCopy.{v}) = ULift.up (z : ℚ) := by
  rw [← Int.cast_smul_eq_zsmul ℚ z, smul_up_one]

private lemma half_ne_intCast (z : ℤ) : (1 / 2 : ℚ) ≠ (z : ℚ) := by
  intro h
  have hden := congrArg Rat.den h
  norm_num [Rat.den_intCast] at hden

private lemma half_notMem_integerScalars : (1 / 2 : ℚ) ∉ integerScalars := by
  intro h
  obtain ⟨z, hz⟩ := RingHom.mem_rangeS.mp h
  exact half_ne_intCast z hz.symm

private lemma integerScalars_ne_top : integerScalars ≠ ⊤ := by
  intro h
  apply half_notMem_integerScalars
  rw [h]
  trivial

private lemma integerScalars_dense : Dense (integerScalars : Set ℚ) :=
  dense_indiscrete ⟨0, (Int.castRingHom ℚ).rangeS.zero_mem⟩

private lemma integer_span_eq_subsemiring_span :
    (Submodule.span ℤ ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) : Set RationalCopy.{v}) =
      (Submodule.span integerScalars ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) :
        Set RationalCopy.{v}) := by
  ext x
  change x ∈ Submodule.span ℤ ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) ↔
    x ∈ Submodule.span integerScalars ({ULift.up (1 : ℚ)} : Set RationalCopy.{v})
  simp only [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨⟨(z : ℚ), RingHom.mem_rangeS.mpr ⟨z, rfl⟩⟩, ?_⟩
    simpa only [integerScalar_smul_up_one, int_smul_up_one] using hz
  · rintro ⟨a, ha⟩
    obtain ⟨z, hz⟩ := RingHom.mem_rangeS.mp a.property
    refine ⟨z, ?_⟩
    rw [int_smul_up_one, show (z : ℚ) = (a : ℚ) from hz]
    simpa only [integerScalar_smul_up_one] using ha

private lemma half_notMem_integer_span :
    (ULift.up (1 / 2 : ℚ) : RationalCopy.{v}) ∉
      Submodule.span ℤ ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) := by
  intro h
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp h
  rw [int_smul_up_one] at hz
  exact half_ne_intCast z (congrArg ULift.down hz).symm

private lemma rational_span_eq_univ :
    (Submodule.span ℚ ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) :
      Set RationalCopy.{v}) = Set.univ := by
  rw [Submodule.span_singleton_eq_range]
  apply Set.range_eq_univ.mpr
  rintro ⟨q⟩
  exact ⟨q, smul_up_one q⟩

private lemma coefficient_preimage_zero :
    (fun r : ℚ => r • (ULift.up (1 : ℚ) : RationalCopy.{v})) ⁻¹'
      ({0} : Set RationalCopy.{v}) =
      ({0} : Set ℚ) := by
  ext r
  simp only [Set.mem_preimage, Set.mem_singleton_iff, smul_up_one]
  constructor
  · intro h
    exact congrArg ULift.down h
  · intro h
    subst r
    rfl

private lemma scalar_zero_not_open : ¬ IsOpen ({0} : Set ℚ) := by
  intro hopen
  rcases (IndiscreteTopology.isOpen_iff _).mp hopen with h | h
  · have hzero : (0 : ℚ) ∈ (∅ : Set ℚ) := h ▸ Set.mem_singleton (0 : ℚ)
    exact hzero
  · have hone : (1 : ℚ) ∈ ({0} : Set ℚ) := h.symm ▸ Set.mem_univ _
    exact one_ne_zero (Set.mem_singleton_iff.mp hone)

/-- The canonical integer-cast range is a dense proper subsemiring of the
indiscrete rationals; `1 / 2` witnesses its properness. -/
private theorem integerScalars_dense_proper :
    Dense (integerScalars : Set ℚ) ∧ integerScalars ≠ ⊤ ∧ (1 / 2 : ℚ) ∉ integerScalars :=
  ⟨integerScalars_dense, integerScalars_ne_top, half_notMem_integerScalars⟩

/-- The independent discrete module is Hausdorff and has disjoint open
neighborhoods of the transported `0` and `1`. In particular, it is not
subsingleton. -/
private theorem zero_one_open_disjoint :
    T2Space RationalCopy.{v} ∧ IsOpen ({0} : Set RationalCopy.{v}) ∧
      IsOpen ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) ∧
      Disjoint ({0} : Set RationalCopy.{v}) {ULift.up (1 : ℚ)} := by
  refine ⟨inferInstance, isOpen_discrete _, isOpen_discrete _,
    Set.disjoint_singleton.mpr ?_⟩
  intro h
  exact zero_ne_one (congrArg ULift.down h)

/-- Addition on the discrete module is separately continuous, and every map
obtained by fixing a rational scalar is continuous. Neither assertion supplies
continuity in the coefficient variable. -/
private theorem separatelyContinuousAdd_and_fixed_smul :
    SeparatelyContinuousAdd RationalCopy.{v} ∧
      ∀ r : ℚ, Continuous (fun x : RationalCopy.{v} => r • x) :=
  ⟨inferInstance, fun _ => continuous_of_discreteTopology⟩

/-- The integer and integer-range-subsemiring spans of the transported `1`
coincide and are closed. The transported `1 / 2` belongs to neither span. -/
private theorem integer_and_subsemiring_spans_closed_proper :
    (Submodule.span ℤ ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) : Set RationalCopy.{v}) =
        (Submodule.span integerScalars ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) :
          Set RationalCopy.{v}) ∧
      IsClosed (Submodule.span ℤ ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) :
        Set RationalCopy.{v}) ∧
      IsClosed (Submodule.span integerScalars ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) :
        Set RationalCopy.{v}) ∧
      (ULift.up (1 / 2 : ℚ) : RationalCopy.{v}) ∉
        Submodule.span ℤ ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) ∧
      (ULift.up (1 / 2 : ℚ) : RationalCopy.{v}) ∉
        Submodule.span integerScalars ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) := by
  refine ⟨integer_span_eq_subsemiring_span, isClosed_discrete _, isClosed_discrete _,
    half_notMem_integer_span, ?_⟩
  rw [← SetLike.mem_coe, ← integer_span_eq_subsemiring_span]
  exact half_notMem_integer_span

/-- The integer-range-subsemiring span remains a proper integer span after
closure, whereas the rational span and its closure are the whole module. -/
private theorem subsemiring_and_rational_span_closures :
    closure (Submodule.span integerScalars ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) :
      Set RationalCopy.{v}) =
        (Submodule.span ℤ ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) : Set RationalCopy.{v}) ∧
      (Submodule.span ℚ ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) :
        Set RationalCopy.{v}) = Set.univ ∧
      closure (Submodule.span ℚ ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) :
        Set RationalCopy.{v}) = Set.univ ∧
      closure (Submodule.span integerScalars ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) :
        Set RationalCopy.{v}) ≠
        closure (Submodule.span ℚ ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}) :
          Set RationalCopy.{v}) := by
  simp only [closure_discrete]
  refine ⟨integer_span_eq_subsemiring_span.symm, rational_span_eq_univ,
    rational_span_eq_univ, ?_⟩
  intro h
  apply half_notMem_integer_span
  rw [← SetLike.mem_coe, integer_span_eq_subsemiring_span, h, rational_span_eq_univ]
  trivial

/-- Coefficient evaluation at the selected generator is not continuous from
indiscrete rational scalars to the discrete module. Its zero fiber is `{0}`,
which is not open in the scalar topology. -/
private theorem coefficient_not_continuous :
    ¬ Continuous (fun r : ℚ => r • (ULift.up (1 : ℚ) : RationalCopy.{v})) := by
  intro h
  have hopen := (isOpen_discrete ({0} : Set RationalCopy.{v})).preimage h
  rw [coefficient_preimage_zero] at hopen
  exact scalar_zero_not_open hopen

/-- The generatorwise coefficient-continuity hypothesis fails for the
singleton of the transported `1`, despite continuity of every fixed-scalar
map and separate continuity of addition. -/
private theorem selected_coefficient_continuity_fails :
    ¬ (∀ m ∈ ({ULift.up (1 : ℚ)} : Set RationalCopy.{v}),
      Continuous (fun r : ℚ => r • m)) := by
  intro h
  exact coefficient_not_continuous (h _ (Set.mem_singleton _))

end

end Rat.IndiscreteScalar
