/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Naturality of the quotient–tensor equivalence

The equivalence `TensorProduct.quotTensorEquivQuotSMul` commutes simultaneously with
an inclusion of ideals and a linear map of modules. The quotient map on modules is
`Submodule.mapQ`; its well-definedness follows from linearity and the ideal inclusion.

For a principal ideal, the equivalence agrees, after the representative-preserving
quotient transport, with the inverse of `QuotSMulTop.equivQuotTensor`. Thus fixed-ideal
module-map naturality extends Mathlib's `QuotSMulTop.equivQuotTensor_naturality`.

## References

This extends Mathlib's quotient–tensor formalization by Antoine Chambert-Loir and
Jujian Zhang and its principal-reduction naturality API by Brendan Murphy. All
quotients, tensor maps and equivalences are the existing Mathlib constructions.
-/

@[expose] public section

universe u v w

namespace TensorProduct

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The quotient–tensor equivalence commutes with enlarging the ideal and applying
an arbitrary linear map. The module quotient map is induced by linearity alone.
For fixed principal ideals, this extends Mathlib's
`QuotSMulTop.equivQuotTensor_naturality`, in the opposite equivalence orientation. -/
theorem quotTensorEquivQuotSMul_naturality {I J : Ideal R} (hIJ : I ≤ J) (f : M →ₗ[R] N) :
    (quotTensorEquivQuotSMul N J).toLinearMap ∘ₗ
        TensorProduct.map (Ideal.Quotient.factorₐ R hIJ).toLinearMap f =
      Submodule.mapQ (I • (⊤ : Submodule R M)) (J • (⊤ : Submodule R N)) f
          ((Submodule.smul_mono_left hIJ).trans
            (Submodule.smul_top_le_comap_smul_top J f)) ∘ₗ
        (quotTensorEquivQuotSMul M I).toLinearMap := by
  apply TensorProduct.ext'
  intro x m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
    Ideal.Quotient.factorₐ_apply_mk, LinearEquiv.coe_coe,
    quotTensorEquivQuotSMul_mk_tmul, Submodule.mapQ_apply, map_smul]

/-- For a principal ideal, Mathlib's quotient–tensor equivalence is the inverse
of `QuotSMulTop.equivQuotTensor`, after identifying the two module quotients by
`Submodule.ideal_span_singleton_smul`. The identification preserves representatives. -/
theorem quotTensorEquivQuotSMul_span_singleton (r : R) :
    quotTensorEquivQuotSMul M (Ideal.span {r}) ≪≫ₗ
        Submodule.quotEquivOfEq _ _
          (Submodule.ideal_span_singleton_smul r (⊤ : Submodule R M)) =
      (QuotSMulTop.equivQuotTensor r M).symm := by
  apply LinearEquiv.symm_bijective.injective
  ext x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

end TensorProduct
