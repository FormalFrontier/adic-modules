/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Topology.Algebra.PadicInt
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Continuous

/-!
# Integer and self-scalar singleton spans in the p-adic integers

The canonical integer casts are dense in the norm topology of `ℤ_[p]`, for a
prime `p`. On this same carrier, with its canonical self-action and integer
action, the integer and self-scalar spans of any singleton have equal set
closures. The examples apply Mathlib's continuous-image closure theorem directly
rather than using a general comparison theorem for spans.

The generator `1`, and more generally any unit, gives two whole closures. The
nonzero nonunit `p` instead gives the closed proper ideal `p ℤ_[p]`, described
by the norm bound `‖z‖ ≤ p⁻¹`; it contains `p` and excludes `1`. The zero
generator gives the closed singleton `{0}` in this normed ring. Thus equality
of the two closures does not imply that either closure is the whole ring.

The integer-cast subsemiring uses the canonical restricted self-action. Its
singleton span has the same set carrier as the canonical integer span. The
ideal-power neighborhoods and shifted norm balls below use the existing norm
topology, without defining a new topology, action, or filtration.

## Implementation notes

The arbitrary-generator application uses `Submodule.span_singleton_eq_range`,
`closure_image_closure`, `DenseRange.closure_range`, and
`Int.cast_smul_eq_zsmul`. Unit density is supplied by
`PadicInt.dense_int_span_of_isUnit`. Closedness for the particular ideal
`p ℤ_[p]` follows from `PadicInt.norm_le_pow_iff_mem_span_pow` at degree one
and the closed norm sublevel set. No claim about properness for all generators
is made. Closedness of `{0}` uses the Hausdorff norm topology here; a zero
singleton need not be closed in an arbitrary topological module.

## References

* Mathlib's p-adic development by Robert Y. Lewis, Mario Carneiro and Johan
  Commelin, in `NumberTheory/Padics/PadicIntegers` and
  `NumberTheory/Padics/RingHoms`.
* Mathlib's singleton-span, integer-module, continuous-image closure, ideal,
  and norm-topology APIs supply the formalization approach.
* The neighborhood bases and unit-density results in
  `AdicModules.Topology.Algebra.PadicInt`.
-/

@[expose] public section

open scoped Topology

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

-- The dense subsemiring is proper, while the coefficient map is continuous at every
-- generator in this particular normed self-module.
example :
    Dense (((Int.castRingHom ℤ_[p]).rangeS : Subsemiring ℤ_[p]) : Set ℤ_[p]) ∧
      (Int.castRingHom ℤ_[p]).rangeS ≠ ⊤ ∧
      SeparatelyContinuousAdd ℤ_[p] ∧
      ∀ x : ℤ_[p], Continuous (fun r : ℤ_[p] => r • x) := by
  refine ⟨?_, ?_, inferInstance, ?_⟩
  · change Dense (Set.range (Int.cast : ℤ → ℤ_[p]))
    exact denseRange_intCast
  · intro htop
    apply int_span_intCast_ne_top p 1
    apply (Submodule.span_singleton_eq_top_iff ℤ (1 : ℤ_[p])).mpr
    intro y
    have hy : y ∈ (Int.castRingHom ℤ_[p]).rangeS := by
      rw [htop]
      exact Set.mem_univ y
    obtain ⟨z, hz⟩ := RingHom.mem_rangeS.mp hy
    refine ⟨z, ?_⟩
    simpa only [Int.coe_castRingHom, Int.smul_one_eq_cast] using hz
  · intro x
    simpa only [smul_eq_mul] using continuous_mul_const x

-- No unit or nonzero premise is used in this direct singleton application.
example (x : ℤ_[p]) :
    closure (Submodule.span ℤ {x} : Set ℤ_[p]) =
        closure (Submodule.span ℤ_[p] {x} : Set ℤ_[p]) ∧
      closure (Submodule.span (Int.castRingHom ℤ_[p]).rangeS {x} : Set ℤ_[p]) =
        closure (Submodule.span ℤ_[p] {x} : Set ℤ_[p]) := by
  let f : ℤ_[p] → ℤ_[p] := fun r => r • x
  have hf : Continuous f := by
    simpa only [f, smul_eq_mul] using continuous_mul_const x
  have hsmall : (Submodule.span ℤ {x} : Set ℤ_[p]) =
      f '' Set.range (Int.cast : ℤ → ℤ_[p]) := by
    rw [Submodule.span_singleton_eq_range, ← Set.range_comp]
    congr 1
  have hlarge : (Submodule.span ℤ_[p] {x} : Set ℤ_[p]) = f '' Set.univ := by
    rw [Submodule.span_singleton_eq_range, Set.image_univ]
  have hclosure : closure (Submodule.span ℤ {x} : Set ℤ_[p]) =
      closure (Submodule.span ℤ_[p] {x} : Set ℤ_[p]) := by
    calc
      closure (Submodule.span ℤ {x} : Set ℤ_[p]) =
          closure (f '' Set.range (Int.cast : ℤ → ℤ_[p])) := congrArg closure hsmall
      _ = closure (f '' closure (Set.range (Int.cast : ℤ → ℤ_[p]))) :=
        (closure_image_closure hf).symm
      _ = closure (f '' Set.univ) := by rw [denseRange_intCast.closure_range]
      _ = closure (Submodule.span ℤ_[p] {x} : Set ℤ_[p]) := congrArg closure hlarge.symm
  have hrestricted :
      (Submodule.span (Int.castRingHom ℤ_[p]).rangeS {x} : Set ℤ_[p]) =
        f '' Set.range (Int.cast : ℤ → ℤ_[p]) := by
    rw [Submodule.span_singleton_eq_range]
    change Set.range (fun a : (Int.castRingHom ℤ_[p]).rangeS => a • x) =
      f '' (((Int.castRingHom ℤ_[p]).rangeS : Subsemiring ℤ_[p]) : Set ℤ_[p])
    ext y
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨(a : ℤ_[p]), a.property, by simpa only [f, Subsemiring.smul_def] using ha⟩
    · rintro ⟨a, ha, hay⟩
      exact ⟨⟨a, ha⟩, by simpa only [f, Subsemiring.smul_def] using hay⟩
  refine ⟨hclosure, ?_⟩
  rw [hrestricted, ← hsmall]
  exact hclosure

/-- A p-adic unit is nonzero, has norm one, and gives whole integer and self-scalar
span closures. Unit density uses the existing p-adic integer-span theorem. -/
theorem int_span_isUnit_closures {x : ℤ_[p]} (hx : IsUnit x) :
    x ≠ 0 ∧ ‖x‖ = 1 ∧
      closure (Submodule.span ℤ {x} : Set ℤ_[p]) = Set.univ ∧
      closure (Submodule.span ℤ_[p] {x} : Set ℤ_[p]) = Set.univ := by
  refine ⟨hx.ne_zero, isUnit_iff.mp hx, (dense_int_span_of_isUnit hx).closure_eq, ?_⟩
  have hspan : Submodule.span ℤ_[p] {x} = ⊤ := Ideal.span_singleton_eq_top.mpr hx
  rw [hspan, Submodule.top_coe, closure_univ]

/-- The generator `1` is nonzero and gives whole integer and self-scalar span closures. -/
theorem int_span_one_closures :
    (1 : ℤ_[p]) ≠ 0 ∧
      closure (Submodule.span ℤ ({1} : Set ℤ_[p]) : Set ℤ_[p]) = Set.univ ∧
      closure (Submodule.span ℤ_[p] ({1} : Set ℤ_[p]) : Set ℤ_[p]) = Set.univ := by
  have h := int_span_isUnit_closures (p := p) (x := 1) isUnit_one
  exact ⟨h.1, h.2.2⟩

private lemma prime_span_eq_norm_sublevel :
    ((Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) : Set ℤ_[p]) =
      {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ)⁻¹} := by
  ext z
  simpa only [SetLike.mem_coe, Set.mem_ofPred_eq, pow_one, zpow_neg, zpow_natCast] using
    (norm_le_pow_iff_mem_span_pow z 1).symm

/-- The ideal generated by `p` is closed and proper in the norm topology. -/
theorem prime_span_closed_proper :
    IsClosed (((Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) : Set ℤ_[p])) ∧
      (Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) ≠ ⊤ := by
  constructor
  · rw [prime_span_eq_norm_sublevel]
    exact isClosed_le continuous_norm continuous_const
  · exact Ideal.span_singleton_ne_top (mem_nonunits_iff.mp p_nonunit)

-- The ideal-level closure API agrees with the set-level closedness assertion.
example : (Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]).closure =
    Ideal.span {(p : ℤ_[p])} := by
  exact Ideal.closure_eq_of_isClosed _ prime_span_closed_proper.1

/-- Both singleton span closures for the nonunit `p` are the norm sublevel set
`‖z‖ ≤ p⁻¹`. The integer closure is obtained directly from dense integer casts. -/
theorem int_span_prime_closures :
    closure (Submodule.span ℤ {(p : ℤ_[p])} : Set ℤ_[p]) =
        {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ)⁻¹} ∧
      closure (Submodule.span ℤ_[p] {(p : ℤ_[p])} : Set ℤ_[p]) =
        {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ)⁻¹} := by
  let f : ℤ_[p] → ℤ_[p] := fun r => r • (p : ℤ_[p])
  have hf : Continuous f := by
    simpa only [f, smul_eq_mul] using continuous_mul_const (p : ℤ_[p])
  have hsmall : (Submodule.span ℤ {(p : ℤ_[p])} : Set ℤ_[p]) =
      f '' Set.range (Int.cast : ℤ → ℤ_[p]) := by
    rw [Submodule.span_singleton_eq_range, ← Set.range_comp]
    congr 1
  have hlarge : (Submodule.span ℤ_[p] {(p : ℤ_[p])} : Set ℤ_[p]) =
      f '' Set.univ := by
    rw [Submodule.span_singleton_eq_range, Set.image_univ]
  have hcomparison : closure (Submodule.span ℤ {(p : ℤ_[p])} : Set ℤ_[p]) =
      closure (Submodule.span ℤ_[p] {(p : ℤ_[p])} : Set ℤ_[p]) := by
    calc
      closure (Submodule.span ℤ {(p : ℤ_[p])} : Set ℤ_[p]) =
          closure (f '' Set.range (Int.cast : ℤ → ℤ_[p])) := congrArg closure hsmall
      _ = closure (f '' closure (Set.range (Int.cast : ℤ → ℤ_[p]))) :=
        (closure_image_closure hf).symm
      _ = closure (f '' Set.univ) := by rw [denseRange_intCast.closure_range]
      _ = closure (Submodule.span ℤ_[p] {(p : ℤ_[p])} : Set ℤ_[p]) :=
        congrArg closure hlarge.symm
  have hself : closure (Submodule.span ℤ_[p] {(p : ℤ_[p])} : Set ℤ_[p]) =
      {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ)⁻¹} :=
    (prime_span_closed_proper (p := p)).1.closure_eq.trans
      (prime_span_eq_norm_sublevel (p := p))
  exact ⟨hcomparison.trans hself, hself⟩

/-- The nonzero nonunit `p` lies in its integer-span closure, whereas `1` does not.
Consequently this common closure is genuinely proper. -/
theorem prime_int_span_closure_controls :
    (p : ℤ_[p]) ≠ 0 ∧ ¬ IsUnit (p : ℤ_[p]) ∧
      ‖(p : ℤ_[p])‖ = (p : ℝ)⁻¹ ∧
      (p : ℤ_[p]) ∈ closure (Submodule.span ℤ {(p : ℤ_[p])} : Set ℤ_[p]) ∧
      (1 : ℤ_[p]) ∉ closure (Submodule.span ℤ {(p : ℤ_[p])} : Set ℤ_[p]) ∧
      closure (Submodule.span ℤ {(p : ℤ_[p])} : Set ℤ_[p]) ≠ Set.univ := by
  have hp : (1 : ℝ) < (p : ℝ) := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hone : (1 : ℤ_[p]) ∉ closure
      (Submodule.span ℤ {(p : ℤ_[p])} : Set ℤ_[p]) := by
    rw [(int_span_prime_closures (p := p)).1]
    change ¬ ‖(1 : ℤ_[p])‖ ≤ (p : ℝ)⁻¹
    rw [norm_one]
    exact not_le_of_gt (inv_lt_one_of_one_lt₀ hp)
  refine ⟨NeZero.ne _, mem_nonunits_iff.mp p_nonunit, norm_p,
    subset_closure (Submodule.mem_span_singleton_self _), hone, ?_⟩
  intro htop
  apply hone
  rw [htop]
  exact Set.mem_univ _

/-- The 2-adic generator `2` gives equal proper closures; it is nonzero and not a unit,
and its closure excludes `1`. -/
theorem int_span_two_closure_controls :
    (2 : ℤ_[2]) ≠ 0 ∧ ¬ IsUnit (2 : ℤ_[2]) ∧
      closure (Submodule.span ℤ {(2 : ℤ_[2])} : Set ℤ_[2]) =
        closure (Submodule.span ℤ_[2] {(2 : ℤ_[2])} : Set ℤ_[2]) ∧
      (1 : ℤ_[2]) ∉ closure (Submodule.span ℤ {(2 : ℤ_[2])} : Set ℤ_[2]) ∧
      closure (Submodule.span ℤ {(2 : ℤ_[2])} : Set ℤ_[2]) ≠ Set.univ := by
  have h := prime_int_span_closure_controls (p := 2)
  have hc := int_span_prime_closures (p := 2)
  exact ⟨h.1, h.2.1, hc.1.trans hc.2.symm, h.2.2.2.2⟩

/-- In the p-adic norm topology the zero generator gives `{0}` for both closures,
and `1` is outside the integer-span closure. -/
theorem int_span_zero_closures :
    closure (Submodule.span ℤ ({0} : Set ℤ_[p]) : Set ℤ_[p]) = ({0} : Set ℤ_[p]) ∧
      closure (Submodule.span ℤ_[p] ({0} : Set ℤ_[p]) : Set ℤ_[p]) = ({0} : Set ℤ_[p]) ∧
      (1 : ℤ_[p]) ∉ closure (Submodule.span ℤ ({0} : Set ℤ_[p]) : Set ℤ_[p]) := by
  have hzero : closure (Submodule.span ℤ ({0} : Set ℤ_[p]) : Set ℤ_[p]) =
      ({0} : Set ℤ_[p]) := by
    rw [Submodule.span_zero_singleton, Submodule.bot_coe, closure_singleton]
  refine ⟨hzero, ?_, ?_⟩
  · rw [Submodule.span_zero_singleton, Submodule.bot_coe, closure_singleton]
  · rw [hzero, Set.mem_singleton_iff]
    exact one_ne_zero

-- All degrees, including zero, use the existing ideal-power filtration and norm topology.
example (n : ℕ) :
    (((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) : Set ℤ_[p])) ∈ 𝓝 (0 : ℤ_[p]) ∧
      (0 : ℤ_[p]) ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) := by
  exact ⟨(hasBasis_nhds_zero_span_pow p).mem_of_mem (i := n) trivial, Submodule.zero_mem _⟩

-- These shifted balls test the canonical topology away from the zero base point as well.
example (z : ℤ_[p]) (n : ℕ) :
    {y : ℤ_[p] | ‖y - z‖ ≤ (p : ℝ) ^ (-(n : ℤ))} ∈ 𝓝 z := by
  have hp0 : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hball : {y : ℤ_[p] | ‖y - z‖ ≤ (p : ℝ) ^ (-(n : ℤ))} =
      Metric.closedBall z ((p : ℝ) ^ (-(n : ℤ))) := by
    ext y
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm]
  rw [hball]
  exact Metric.closedBall_mem_nhds z (zpow_pos hp0 _)

end PadicInt
