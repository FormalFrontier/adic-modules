/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
/-
The finite-linear-combination argument is adapted from Mathlib:
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Kernels of adic reduction under finite generation of a power

For an ideal `I` of a commutative ring `R` and an `R`-module `M`, finite generation of the
single power `I ^ n` identifies the kernel of `AdicCompletion.eval I M n` with
`(I ^ n) • ⊤` in `Submodule R (AdicCompletion I M)`. The exponent may be zero, and the ring
and module may lie in independent universes.

## References

Bingyu Xia's `AdicCompletion.pow_smul_top_eq_ker_eval` in Mathlib's
`RingTheory/AdicCompletion/Completeness.lean` assumes `I.FG`. The proof here adapts its
finite-linear-combination argument to use finite generation only of `I ^ n`: completion
preserves the surjection onto `I ^ n • ⊤`, and finite direct sums commute with completion.
-/

@[expose] public section

universe u v

namespace AdicCompletion

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]

open Submodule Finsupp

/-- Finite linear combinations commute with completion after identifying finitely supported
families with a direct sum. -/
private lemma lsum_smul_comp_finsuppLEquivDirectSum_symm (I : Ideal R)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (f : ι → R) :
    ((lsum (AdicCompletion I R))
      fun i ↦ ((algebraMap R (AdicCompletion I R)) (f i) • .id :
        AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I M)) ∘ₗ
      (finsuppLEquivDirectSum (AdicCompletion I R) (AdicCompletion I M) ι).symm.toLinearMap =
    (map I (lsum R fun i ↦ f i • .id) ∘ₗ
      map I (finsuppLEquivDirectSum R M ι).symm.toLinearMap) ∘ₗ
      (sumEquivOfFintype I (fun _ : ι ↦ M)) := by
  ext
  simp only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, LinearMap.coe_comp,
    coe_lsum, LinearMap.coe_smul, LinearMap.id_coe, LinearEquiv.coe_coe, Function.comp_apply,
    finsuppLEquivDirectSum_symm_lof, Pi.smul_apply, id_eq, smul_zero, sum_single_index, smul_eval,
    mapQ_eq_factor, factor_eq_factor, of_apply, mkQ_apply, Ideal.Quotient.mk_eq_mk, mk_apply_coe,
    sumEquivOfFintype_apply, sum_lof, map_mk, AdicCauchySequence.map_apply_coe, map_smul]
  rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

/-- If `I ^ n` is finitely generated, its scalar multiple of the whole completed module is
exactly the kernel of evaluation at `n`. This replaces the hypothesis `I.FG` in Mathlib's
`AdicCompletion.pow_smul_top_eq_ker_eval` by finite generation of the single power, following
its finite-linear-combination proof. -/
theorem pow_smul_top_eq_ker_eval_of_fg_pow {n : ℕ} (h : (I ^ n).FG) :
    (I ^ n) • (⊤ : Submodule R (AdicCompletion I M)) = (AdicCompletion.eval I M n).ker := by
  classical
  refine le_antisymm (pow_smul_top_le_ker_eval ..) ?_
  rcases h with ⟨s, hs⟩
  simp only [← hs, span_smul_eq]
  rw [← restrictScalars_top R (AdicCompletion I R) (AdicCompletion I M),
    ← restrictScalars_image_smul_eq (R := AdicCompletion I R),
    ← restrictScalars_range_ofPowSMul_eq_ker_eval, restrictScalars_le,
    image_smul_top_eq_range_lsum]
  simp only [SetLike.coe_sort_coe]
  rw [← LinearMap.range_comp_of_range_eq_top
      (f := (finsuppLEquivDirectSum ..).symm.toLinearMap) _ (by simp),
    lsum_smul_comp_finsuppLEquivDirectSum_symm,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _ <|
      Function.RightInverse.surjective (g := map I (finsuppLEquivDirectSum R M s)) (fun _ ↦ by
        simp [← LinearMap.comp_apply, map_comp]))]
  rintro _ ⟨x, rfl⟩
  let f : (s →₀ M) →ₗ[R] M := lsum R fun i : s ↦ i.val • (LinearMap.id : M →ₗ[R] M)
  have hfRange : f.range = I ^ n • (⊤ : Submodule R M) := by
    rw [← hs, span_smul_eq, smul_top_eq_range_lsum]
    rfl
  have hf : ∀ x, f x ∈ I ^ n • (⊤ : Submodule R M) := by
    intro x
    rw [← hfRange]
    exact LinearMap.mem_range_self f x
  have : Function.Surjective (f.codRestrict (I ^ n • ⊤) hf) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict, hfRange]
    simp
  rcases map_surjective I this x with ⟨x, rfl⟩
  exact ⟨x, by rw [← LinearMap.comp_apply, map_comp, LinearMap.subtype_comp_codRestrict]⟩

end AdicCompletion
