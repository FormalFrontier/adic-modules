/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Int.Basic

/-!
# Nonzero integer coefficient reduction

The pure tensor `1 ⊗ 1` for the ideal `(4)` remains nonzero after coefficient
reduction to `(2)` and application of Mathlib's quotient–tensor equivalence.
The computation uses only the stock maps and characteristic equations, independently
of the general naturality theorem. A zero module map gives the zero tensor.

## References

The independent reduction calculation uses Mathlib's `quotTensorEquivQuotSMul`,
tensor-map characteristic equations and integer coefficient quotients. The final
square applies the simultaneous naturality law in
`AdicModules.LinearAlgebra.TensorProduct.Quotient`.
-/

open scoped TensorProduct

namespace TensorProduct

private theorem four_le_two : Ideal.span {(4 : ℤ)} ≤ Ideal.span {(2 : ℤ)} :=
  Ideal.span_singleton_le_span_singleton.mpr (by decide)

private theorem one_mod_two_ne_zero :
    (Submodule.Quotient.mk (1 : ℤ) :
      ℤ ⧸ (Ideal.span {(2 : ℤ)} • (⊤ : Submodule ℤ ℤ))) ≠ 0 := by
  intro h
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp h
  change (1 : ℤ) ∈ (Ideal.span {(2 : ℤ)} • (⊤ : Ideal ℤ)) at hmem
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton] at hmem
  exact (by decide : ¬ (2 : ℤ) ∣ 1) hmem

private theorem reduction_one_tmul :
    quotTensorEquivQuotSMul ℤ (Ideal.span {(2 : ℤ)})
        (TensorProduct.map (Ideal.Quotient.factorₐ ℤ four_le_two).toLinearMap
          (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
          (1 ⊗ₜ[ℤ] 1)) =
      (Submodule.Quotient.mk (1 : ℤ) :
        ℤ ⧸ (Ideal.span {(2 : ℤ)} • (⊤ : Submodule ℤ ℤ))) := by
  simpa only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one,
    LinearMap.id_apply] using
    quotTensorEquivQuotSMul_mk_one_tmul (Ideal.span {(2 : ℤ)}) (1 : ℤ)

private theorem reduction_one_tmul_ne_zero :
    quotTensorEquivQuotSMul ℤ (Ideal.span {(2 : ℤ)})
        (TensorProduct.map (Ideal.Quotient.factorₐ ℤ four_le_two).toLinearMap
          (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
          (1 ⊗ₜ[ℤ] 1)) ≠ 0 := by
  rw [reduction_one_tmul]
  exact one_mod_two_ne_zero

private theorem one_tmul_mod_four_ne_zero :
    (1 ⊗ₜ[ℤ] 1 : (ℤ ⧸ Ideal.span {(4 : ℤ)}) ⊗[ℤ] ℤ) ≠ 0 := by
  intro h
  apply reduction_one_tmul_ne_zero
  rw [h, map_zero, map_zero]

private theorem reduction_zero_module_map :
    TensorProduct.map (Ideal.Quotient.factorₐ ℤ four_le_two).toLinearMap
        (0 : ℤ →ₗ[ℤ] ℤ) (1 ⊗ₜ[ℤ] 1) = 0 := by
  simp

/-- Coefficient reduction from `(4)` to `(2)` sends the nonzero integer pure tensor
`1 ⊗ 1` to an element with nonzero image under Mathlib's quotient–tensor equivalence;
replacing the module identity by the zero map kills that tensor. -/
public theorem integer_quotient_tensor_reduction_nonzero :
    ∃ h : Ideal.span {(4 : ℤ)} ≤ Ideal.span {(2 : ℤ)},
      (1 ⊗ₜ[ℤ] 1 : (ℤ ⧸ Ideal.span {(4 : ℤ)}) ⊗[ℤ] ℤ) ≠ 0 ∧
        quotTensorEquivQuotSMul ℤ (Ideal.span {(2 : ℤ)})
            (TensorProduct.map (Ideal.Quotient.factorₐ ℤ h).toLinearMap
              (LinearMap.id : ℤ →ₗ[ℤ] ℤ) (1 ⊗ₜ[ℤ] 1)) ≠ 0 ∧
        TensorProduct.map (Ideal.Quotient.factorₐ ℤ h).toLinearMap
            (0 : ℤ →ₗ[ℤ] ℤ) (1 ⊗ₜ[ℤ] 1) = 0 :=
  ⟨four_le_two, one_tmul_mod_four_ne_zero, reduction_one_tmul_ne_zero,
    reduction_zero_module_map⟩

/-- The naturality square commutes on the same nonzero integer tensor used above. -/
private theorem integer_quotient_tensor_reduction_commutes_nonzero :
    quotTensorEquivQuotSMul ℤ (Ideal.span {(2 : ℤ)})
        (TensorProduct.map (Ideal.Quotient.factorₐ ℤ four_le_two).toLinearMap
          (LinearMap.id : ℤ →ₗ[ℤ] ℤ) (1 ⊗ₜ[ℤ] 1)) =
      Submodule.mapQ
        (Ideal.span {(4 : ℤ)} • (⊤ : Submodule ℤ ℤ))
        (Ideal.span {(2 : ℤ)} • (⊤ : Submodule ℤ ℤ))
        (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
        ((Submodule.smul_mono_left four_le_two).trans
          (Submodule.smul_top_le_comap_smul_top (Ideal.span {(2 : ℤ)}) LinearMap.id))
        (quotTensorEquivQuotSMul ℤ (Ideal.span {(4 : ℤ)}) (1 ⊗ₜ[ℤ] 1)) ∧
      (1 ⊗ₜ[ℤ] 1 : (ℤ ⧸ Ideal.span {(4 : ℤ)}) ⊗[ℤ] ℤ) ≠ 0 ∧
      quotTensorEquivQuotSMul ℤ (Ideal.span {(2 : ℤ)})
        (TensorProduct.map (Ideal.Quotient.factorₐ ℤ four_le_two).toLinearMap
          (LinearMap.id : ℤ →ₗ[ℤ] ℤ) (1 ⊗ₜ[ℤ] 1)) ≠ 0 := by
  obtain ⟨h, hin, hout, _⟩ := integer_quotient_tensor_reduction_nonzero
  refine ⟨?_, hin, hout⟩
  exact LinearMap.congr_fun
    (quotTensorEquivQuotSMul_naturality four_le_two (LinearMap.id : ℤ →ₗ[ℤ] ℤ))
    (1 ⊗ₜ[ℤ] 1)

end TensorProduct
