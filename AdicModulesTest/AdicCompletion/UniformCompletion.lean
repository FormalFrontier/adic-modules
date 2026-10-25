/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.PadicInt

/-!
# Integer-adic uniform completion inputs

The source uses the canonical module uniformity for `(2) ⊆ ℤ`, with both the
uniformity and its topology explicitly installed. The target retains its norm
uniformity, complete separated topology, and original integer scalar action.
The extension of the integer cast detects the canonical completion image
of `1`; this does not assume that the source is separated or that its map into
the completion is injective. The zero and unit ideals give the boundary
neighborhood computations, including the non-separated unit-ideal source.

## References

Mathlib's uniform completion extension and adic neighborhood bases, together
with `PadicInt.uniformContinuous_intCast_adic` for the original norm target.
-/

@[expose] public section

open Filter UniformSpace

section TwoAdic

/-- The original norm-topology target is complete, separated and nonzero, with
its original uniformly continuous integer scalar action. -/
example :
    CompleteSpace ℤ_[2] ∧ T0Space ℤ_[2] ∧ UniformContinuousConstSMul ℤ ℤ_[2] ∧
      @ContinuousSMul ℤ ℤ_[2] (inferInstance : SMul ℤ ℤ_[2])
        (Ideal.span {(2 : ℤ)}).adicTopology (inferInstance : TopologicalSpace ℤ_[2]) ∧
      PadicInt.intCastAdicCLM 2 1 ≠ 0 := by
  exact ⟨inferInstance, inferInstance, inferInstance, PadicInt.continuousSMul_int_adic 2,
    by simp⟩

/-- The canonical completion image of `1` is independently detected by the
extension of integer casting into the original norm-topology p-adic integers. -/
example :
    @Completion.coe' ℤ ((Ideal.span {(2 : ℤ)}).adicModuleUniformSpace ℤ) 1 ≠
      (0 : @Completion ℤ ((Ideal.span {(2 : ℤ)}).adicModuleUniformSpace ℤ)) := by
  let : UniformSpace ℤ := (Ideal.span {(2 : ℤ)}).adicModuleUniformSpace ℤ
  let : TopologicalSpace ℤ :=
    ((Ideal.span {(2 : ℤ)}).adicModuleUniformSpace ℤ).toTopologicalSpace
  intro h
  have h' : ((1 : ℤ) : Completion ℤ) = ((0 : ℤ) : Completion ℤ) := by
    simpa only [Completion.coe_zero] using h
  have he := congrArg (Completion.extension (Int.castRingHom ℤ_[2])) h'
  exact one_ne_zero (by
    simpa only [Completion.extension_coe (PadicInt.uniformContinuous_intCast_adic 2),
      map_one, map_zero] using he)

end TwoAdic

/-- The zero-ideal source has the expected discrete neighborhood at zero. -/
example : @nhds ℤ ((⊥ : Ideal ℤ).adicModuleUniformSpace ℤ).toTopologicalSpace 0 =
    pure 0 := by
  rw [Ideal.adicModuleUniformSpace_self_toTopologicalSpace]
  ext s
  rw [(⊥ : Ideal ℤ).hasBasis_nhds_zero_adic.mem_iff, Filter.mem_pure]
  constructor
  · rintro ⟨n, _, hn⟩
    exact hn (Ideal.zero_mem _)
  · intro hs
    refine ⟨1, trivial, ?_⟩
    simpa using hs

/-- The unit-ideal source is allowed: every zero-neighborhood is the whole ring. -/
example : @nhds ℤ ((⊤ : Ideal ℤ).adicModuleUniformSpace ℤ).toTopologicalSpace 0 =
    (⊤ : Filter ℤ) := by
  rw [Ideal.adicModuleUniformSpace_self_toTopologicalSpace]
  ext s
  rw [(⊤ : Ideal ℤ).hasBasis_nhds_zero_adic.mem_iff]
  simp [Ideal.top_pow]
