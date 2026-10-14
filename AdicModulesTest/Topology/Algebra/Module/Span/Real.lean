/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Topology.Algebra.Module.Span

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Rational and integer scalar spans in real modules

In the usual real plane, the span of the first coordinate vector over the rational
image is the rational first axis. Its closure is the proper real first axis, which
is also the real span. The second coordinate vector stays outside this closure,
whereas the first coordinate vector multiplied by `√2` belongs to the closure but
not to the rational span.

For the usual real line, the span of `1` over the integer image is closed and
proper, although the real span is the whole line. The coefficient map at `1` is
continuous, but the integer image is not dense; `1 / 2` separates the two closures.
All scalar actions are the canonical restrictions of real scalar multiplication.

## References

* Mathlib's `Submodule.mem_span_singleton` and `Submodule.span_singleton_eq_range`
  for the canonical singleton-span calculations.
* Mathlib's `Rat.denseRange_cast` and
  `Continuous.range_subset_closure_image_dense` for rational approximation.
* Mathlib's `continuous_pi`, `continuous_apply` and `isClosed_eq` for the usual
  product topology and the closed coordinate axis.
* Mathlib's `irrational_sqrt_two` and `Int.isClosedEmbedding_coe_real` for the
  strict rational enlargement and the closed integer image.
-/

@[expose] public section

open Set Topology

private abbrev Plane := Fin 2 → ℝ

private noncomputable def e₀ : Plane := Pi.single 0 1

private noncomputable def e₁ : Plane := Pi.single 1 1

private noncomputable abbrev rationalScalars : Subsemiring ℝ := (Rat.castHom ℝ).rangeS

private noncomputable abbrev integerScalars : Subsemiring ℝ := (Int.castRingHom ℝ).rangeS

private theorem rationalScalars_carrier :
    (rationalScalars : Set ℝ) = Set.range (fun q : ℚ => (q : ℝ)) := rfl

private theorem integerScalars_carrier :
    (integerScalars : Set ℝ) = Set.range (fun z : ℤ => (z : ℝ)) := rfl

private theorem rationalScalars_dense : Dense (rationalScalars : Set ℝ) := by
  rw [rationalScalars_carrier]
  exact Rat.denseRange_cast

private theorem sqrt_two_not_mem_rationalScalars : Real.sqrt 2 ∉ rationalScalars := by
  change Real.sqrt 2 ∉ (rationalScalars : Set ℝ)
  rw [rationalScalars_carrier]
  exact irrational_sqrt_two

private theorem rationalScalars_ne_top : rationalScalars ≠ ⊤ := by
  intro h
  apply sqrt_two_not_mem_rationalScalars
  rw [h]
  trivial

private theorem plane_separatelyContinuousAdd : SeparatelyContinuousAdd Plane := inferInstance

private theorem e₀_ne_zero : e₀ ≠ 0 := by
  intro h
  have h₀ := congr_fun h 0
  simp [e₀] at h₀

private theorem smul_e₀_eq_iff (r : ℝ) (x : Plane) :
    r • e₀ = x ↔ x 0 = r ∧ x 1 = 0 := by
  constructor
  · intro h
    constructor
    · simpa [e₀, smul_eq_mul] using (congr_fun h 0).symm
    · simpa [e₀, smul_eq_mul] using (congr_fun h 1).symm
  · rintro ⟨h₀, h₁⟩
    exact funext <| Fin.forall_fin_two.mpr
      ⟨by simpa [e₀, smul_eq_mul] using h₀.symm,
        by simpa [e₀, smul_eq_mul] using h₁.symm⟩

private theorem coefficient_continuous_e₀ : Continuous (fun r : ℝ => r • e₀) := by
  apply continuous_pi
  intro i
  simpa only [Pi.smul_apply, smul_eq_mul] using continuous_mul_const (e₀ i)

private theorem coefficient_continuous_on_e₀ :
    ∀ m ∈ ({e₀} : Set Plane), Continuous (fun r : ℝ => r • m) := by
  intro m hm
  obtain rfl := Set.mem_singleton_iff.mp hm
  exact coefficient_continuous_e₀

private theorem mem_rational_span_iff (x : Plane) :
    x ∈ Submodule.span rationalScalars {e₀} ↔ x 0 ∈ rationalScalars ∧ x 1 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    have hx := (smul_e₀_eq_iff (a : ℝ) x).mp ha
    exact ⟨hx.1.symm ▸ a.property, hx.2⟩
  · rintro ⟨h₀, h₁⟩
    refine ⟨⟨x 0, h₀⟩, ?_⟩
    exact (smul_e₀_eq_iff (x 0) x).mpr ⟨rfl, h₁⟩

private theorem mem_real_span_iff (x : Plane) :
    x ∈ Submodule.span ℝ {e₀} ↔ x 1 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, hr⟩
    exact ((smul_e₀_eq_iff r x).mp hr).2
  · intro hx
    exact ⟨x 0, (smul_e₀_eq_iff (x 0) x).mpr ⟨rfl, hx⟩⟩

private theorem rational_span_eq_image :
    (Submodule.span rationalScalars {e₀} : Set Plane) =
      (fun r : ℝ => r • e₀) '' (rationalScalars : Set ℝ) := by
  rw [Submodule.span_singleton_eq_range]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(a : ℝ), a.property, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩

private theorem real_span_eq_axis :
    (Submodule.span ℝ {e₀} : Set Plane) = {x : Plane | x 1 = 0} :=
  Set.ext mem_real_span_iff

private theorem real_span_closed : IsClosed (Submodule.span ℝ {e₀} : Set Plane) := by
  rw [real_span_eq_axis]
  exact isClosed_eq (continuous_apply 1) continuous_const

private theorem rational_span_closure :
    closure (Submodule.span rationalScalars {e₀} : Set Plane) =
      (Submodule.span ℝ {e₀} : Set Plane) := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ real_span_closed
    intro x hx
    exact (mem_real_span_iff x).mpr ((mem_rational_span_iff x).mp hx).2
  · have h := coefficient_continuous_e₀.range_subset_closure_image_dense rationalScalars_dense
    rw [← rational_span_eq_image] at h
    rw [Submodule.span_singleton_eq_range]
    exact h

private theorem rational_span_closure_eq_axis :
    closure (Submodule.span rationalScalars {e₀} : Set Plane) = {x : Plane | x 1 = 0} :=
  rational_span_closure.trans real_span_eq_axis

private theorem rational_axis_two_closures :
    closure (Submodule.span rationalScalars {e₀} : Set Plane) =
      closure (Submodule.span ℝ {e₀} : Set Plane) := by
  rw [rational_span_closure, real_span_closed.closure_eq]

private theorem e₁_not_mem_real_span : e₁ ∉ Submodule.span ℝ {e₀} := by
  intro h
  have h₁ := (mem_real_span_iff e₁).mp h
  simp [e₁] at h₁

private theorem e₁_not_mem_real_span_closure :
    e₁ ∉ closure (Submodule.span ℝ {e₀} : Set Plane) := by
  rw [real_span_closed.closure_eq]
  exact e₁_not_mem_real_span

private theorem e₁_not_mem_rational_span_closure :
    e₁ ∉ closure (Submodule.span rationalScalars {e₀} : Set Plane) := by
  rw [rational_span_closure]
  exact e₁_not_mem_real_span

private theorem rational_span_closure_ne_univ :
    closure (Submodule.span rationalScalars {e₀} : Set Plane) ≠ Set.univ := by
  intro h
  apply e₁_not_mem_rational_span_closure
  rw [h]
  trivial

private theorem sqrt_two_smul_mem_closure :
    Real.sqrt 2 • e₀ ∈ closure (Submodule.span rationalScalars {e₀} : Set Plane) := by
  rw [rational_span_closure]
  exact Submodule.mem_span_singleton.mpr ⟨Real.sqrt 2, rfl⟩

private theorem sqrt_two_smul_not_mem_rational_span :
    Real.sqrt 2 • e₀ ∉ Submodule.span rationalScalars {e₀} := by
  intro h
  apply sqrt_two_not_mem_rationalScalars
  simpa [e₀, smul_eq_mul] using ((mem_rational_span_iff _).mp h).1

private theorem rational_span_ne_closure :
    (Submodule.span rationalScalars {e₀} : Set Plane) ≠
      closure (Submodule.span rationalScalars {e₀} : Set Plane) := by
  intro h
  apply sqrt_two_smul_not_mem_rational_span
  change Real.sqrt 2 • e₀ ∈ (Submodule.span rationalScalars {e₀} : Set Plane)
  rw [h]
  exact sqrt_two_smul_mem_closure

private theorem rational_axis_closure :
    closure (Submodule.span rationalScalars {e₀} : Set Plane) = {x : Plane | x 1 = 0} ∧
      e₁ ∉ closure (Submodule.span rationalScalars {e₀} : Set Plane) := by
  have h := Submodule.closure_span_eq_of_dense_subsemiring
    rationalScalars rationalScalars_dense ({e₀} : Set Plane) coefficient_continuous_on_e₀
  refine ⟨h.trans (real_span_closed.closure_eq.trans real_span_eq_axis), ?_⟩
  rw [h]
  exact e₁_not_mem_real_span_closure

private theorem real_separatelyContinuousAdd : SeparatelyContinuousAdd ℝ := inferInstance

private theorem coefficient_continuous_on_one :
    ∀ m ∈ ({1} : Set ℝ), Continuous (fun r : ℝ => r • m) := by
  intro m hm
  obtain rfl := Set.mem_singleton_iff.mp hm
  simpa only [smul_eq_mul, mul_one] using (continuous_id' : Continuous (fun r : ℝ => r))

private theorem integer_span_eq_carrier :
    (Submodule.span integerScalars ({1} : Set ℝ) : Set ℝ) = (integerScalars : Set ℝ) := by
  rw [Submodule.span_singleton_eq_range]
  ext x
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (a : ℝ) = x := by
      simpa only [Subsemiring.smul_def, smul_eq_mul, mul_one] using ha
    exact ha' ▸ a.property
  · intro hx
    exact ⟨⟨x, hx⟩, by simp [Subsemiring.smul_def, smul_eq_mul]⟩

private theorem integerScalars_closed : IsClosed (integerScalars : Set ℝ) := by
  rw [integerScalars_carrier]
  exact Int.isClosedEmbedding_coe_real.isClosed_range

private theorem half_not_mem_integerScalars : (1 / 2 : ℝ) ∉ integerScalars := by
  change (1 / 2 : ℝ) ∉ (integerScalars : Set ℝ)
  rw [integerScalars_carrier]
  rintro ⟨z, hz⟩
  change (z : ℝ) = 1 / 2 at hz
  have hzpos : (0 : ℝ) < z := by rw [hz]; norm_num
  have hzlt : (z : ℝ) < 1 := by rw [hz]; norm_num
  have hzpos' : (0 : ℤ) < z := Int.cast_pos.mp hzpos
  have hzlt' : z < (1 : ℤ) := by exact_mod_cast hzlt
  omega

private theorem integerScalars_ne_top : integerScalars ≠ ⊤ := by
  intro h
  apply half_not_mem_integerScalars
  rw [h]
  trivial

private theorem integerScalars_not_dense : ¬ Dense (integerScalars : Set ℝ) := by
  intro h
  have hhalf := h (1 / 2)
  rw [integerScalars_closed.closure_eq] at hhalf
  exact half_not_mem_integerScalars hhalf

private theorem integer_span_closure :
    closure (Submodule.span integerScalars ({1} : Set ℝ) : Set ℝ) =
      (integerScalars : Set ℝ) := by
  rw [integer_span_eq_carrier]
  exact integerScalars_closed.closure_eq

private theorem real_span_one_eq_top : Submodule.span ℝ ({1} : Set ℝ) = ⊤ :=
  (Submodule.span_singleton_eq_top_iff ℝ (1 : ℝ)).mpr
    (fun x => ⟨x, by simp [smul_eq_mul]⟩)

private theorem real_span_one_closure :
    closure (Submodule.span ℝ ({1} : Set ℝ) : Set ℝ) = Set.univ := by
  rw [real_span_one_eq_top]
  simp

private theorem half_mem_real_span_one : (1 / 2 : ℝ) ∈ Submodule.span ℝ ({1} : Set ℝ) := by
  rw [real_span_one_eq_top]
  trivial

private theorem half_mem_real_span_one_closure :
    (1 / 2 : ℝ) ∈ closure (Submodule.span ℝ ({1} : Set ℝ) : Set ℝ) :=
  subset_closure half_mem_real_span_one

private theorem half_not_mem_integer_span_closure :
    (1 / 2 : ℝ) ∉ closure (Submodule.span integerScalars ({1} : Set ℝ) : Set ℝ) := by
  rw [integer_span_closure]
  exact half_not_mem_integerScalars

private theorem integer_span_closure_ne_univ :
    closure (Submodule.span integerScalars ({1} : Set ℝ) : Set ℝ) ≠ Set.univ := by
  intro h
  apply half_not_mem_integer_span_closure
  rw [h]
  trivial

private theorem integer_axis_two_closures_ne :
    closure (Submodule.span integerScalars ({1} : Set ℝ) : Set ℝ) ≠
      closure (Submodule.span ℝ ({1} : Set ℝ) : Set ℝ) := by
  intro h
  apply half_not_mem_integer_span_closure
  rw [h]
  exact half_mem_real_span_one_closure
