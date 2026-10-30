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

import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Kernels under adic completion and reduction

For an ideal `I` of a commutative ring `R` and an `R`-module `M`, finite generation of the
single power `I ^ n` identifies the kernel of `AdicCompletion.eval I M n` with
`(I ^ n) • ⊤` in `Submodule R (AdicCompletion I M)`. The exponent may be zero, and the ring
and module may lie in independent universes.

Finite generation of one positive power additionally gives this equality at every degree,
without assuming `I.FG`. The proof lifts a higher coordinate to the original module and
applies the fixed-stage equality to the residual.

For any ideal, completion of the kernel of an original split surjection is canonically
isomorphic to the kernel of the completed map, linearly over the completed ring. The forward
map is completion of the original kernel inclusion, and the inverse is completion of the
original split projector restricted to the completed kernel.
No finiteness of the original modules, finite generation of the ideal, Noetherianity,
projectivity, flatness, separatedness or completeness is required.

## Implementation notes

The split-kernel comparison uses the canonical completed-ring actions and the raw inverse-limit
completion, without an action of the completed ring on either original module. It transports
original split identities, rather than assuming exactness of completion for arbitrary maps.
The ring and the two original modules may lie in independent universes.

## References

Bingyu Xia's `AdicCompletion.pow_smul_top_eq_ker_eval` in Mathlib's
`RingTheory/AdicCompletion/Completeness.lean` assumes `I.FG`. The proof here adapts its
finite-linear-combination argument to use finite generation only of `I ^ n`: completion
preserves the surjection onto `I ^ n • ⊤`, and finite direct sums commute with completion.

The split-kernel comparison reuses Mathlib's completion formalizations by Kenny Lau, Judith
Ludwig, Christian Merten and Jiedong Jiang, the exact-sequence splitting formalization by
Antoine Chambert-Loir, and the submodule-equivalence API by Johannes Hölzl, Mario Carneiro,
Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis and Heather Macbeth. Its original-projector
approach also follows the Projective Modules and Stable Range formalizations by Formal
Frontier Agents, including Prism and Iris.
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

section SplitSurjection

universe w

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Completing the original split identities gives a left inverse to the completed kernel
inclusion and identifies its range with the completed-map kernel. -/
private theorem map_ker_subtype_leftInverse_range
    (I : Ideal R) (f : M →ₗ[R] N) (r : N →ₗ[R] M)
    (h : f.comp r = LinearMap.id) :
    let E0 : M ≃ₗ[R] (LinearMap.ker f × N) :=
      ((LinearMap.exact_subtype_ker_map f).splitSurjectiveEquiv
        (Submodule.injective_subtype (LinearMap.ker f)) ⟨r, h⟩).1
    let P : M →ₗ[R] LinearMap.ker f :=
      (LinearMap.fst R (LinearMap.ker f) N).comp E0.toLinearMap
    Function.LeftInverse (map I P) (map I (LinearMap.ker f).subtype) ∧
      LinearMap.range (map I (LinearMap.ker f).subtype) = LinearMap.ker (map I f) := by
  let e := (LinearMap.exact_subtype_ker_map f).splitSurjectiveEquiv
    (Submodule.injective_subtype (LinearMap.ker f)) ⟨r, h⟩
  let E0 : M ≃ₗ[R] (LinearMap.ker f × N) := e.1
  let P : M →ₗ[R] LinearMap.ker f :=
    (LinearMap.fst R (LinearMap.ker f) N).comp E0.toLinearMap
  change Function.LeftInverse (map I P) (map I (LinearMap.ker f).subtype) ∧ _
  -- This splitting has inverse `(k, n) ↦ ↑k + r n`.
  have hinv : E0.symm.toLinearMap =
      (LinearMap.ker f).subtype.comp (LinearMap.fst R (LinearMap.ker f) N) +
        r.comp (LinearMap.snd R (LinearMap.ker f) N) := rfl
  have hP : (LinearMap.ker f).subtype.comp P = LinearMap.id - r.comp f := by
    apply LinearMap.ext
    intro x
    change (P x : M) = x - r (f x)
    apply eq_sub_iff_add_eq.mpr
    have hsecond : f x = (E0 x).2 := LinearMap.congr_fun e.2.2 x
    calc
      (P x : M) + r (f x) = E0.symm (E0 x) := by
        rw [hsecond]
        exact (LinearMap.congr_fun hinv (E0 x)).symm
      _ = x := E0.symm_apply_apply x
  have hPi : P.comp (LinearMap.ker f).subtype = LinearMap.id := by
    apply LinearMap.ext
    intro k
    apply Subtype.ext
    change (P (k : M) : M) = (k : M)
    have hk := LinearMap.congr_fun hP (k : M)
    change (P (k : M) : M) = (k : M) - r (f (k : M)) at hk
    simpa only [LinearMap.map_coe_ker, _root_.map_zero, sub_zero] using hk
  have hQJ : (map I P).comp (map I (LinearMap.ker f).subtype) = LinearMap.id := by
    rw [map_comp, hPi, map_id]
  have hJQ : (map I (LinearMap.ker f).subtype).comp (map I P) =
      LinearMap.id - (map I r).comp (map I f) := by
    rw [map_comp, hP, _root_.map_sub, map_id, ← map_comp]
  have hFJ : (map I f).comp (map I (LinearMap.ker f).subtype) = 0 := by
    rw [map_comp, LinearMap.comp_ker_subtype, map_zero]
  refine ⟨fun x ↦ LinearMap.congr_fun hQJ x, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr (LinearMap.congr_fun hFJ x)
  · intro z hz
    refine ⟨map I P z, ?_⟩
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.mem_ker.mp hz, _root_.map_zero, sub_zero] using LinearMap.congr_fun hJQ z

/-- Completion identifies the original kernel of a split surjection with the kernel of the
completed map, over the completed ring. The forward map is the completion of the original
kernel inclusion; the supplied original section constructs its inverse. -/
noncomputable def kerEquivOfRightInverse
    (I : Ideal R) (f : M →ₗ[R] N) (r : N →ₗ[R] M)
    (h : f.comp r = LinearMap.id) :
    AdicCompletion I (LinearMap.ker f) ≃ₗ[AdicCompletion I R]
      LinearMap.ker (map I f) :=
  let E0 : M ≃ₗ[R] (LinearMap.ker f × N) :=
    ((LinearMap.exact_subtype_ker_map f).splitSurjectiveEquiv
      (Submodule.injective_subtype (LinearMap.ker f)) ⟨r, h⟩).1
  let P : M →ₗ[R] LinearMap.ker f :=
    (LinearMap.fst R (LinearMap.ker f) N).comp E0.toLinearMap
  (LinearEquiv.ofLeftInverse (f := map I (LinearMap.ker f).subtype) (g := map I P) (by
    exact (map_ker_subtype_leftInverse_range I f r h).1)).trans
    (LinearEquiv.ofEq _ _ (by
      exact (map_ker_subtype_leftInverse_range I f r h).2))

/-- The split-kernel equivalence has the completed original kernel inclusion as its whole
underlying map into the completed source. -/
theorem subtype_comp_kerEquivOfRightInverse
    (I : Ideal R) (f : M →ₗ[R] N) (r : N →ₗ[R] M)
    (h : f.comp r = LinearMap.id) :
    (LinearMap.ker (map I f)).subtype.comp
      (kerEquivOfRightInverse I f r h).toLinearMap =
    map I (LinearMap.ker f).subtype := by
  apply LinearMap.ext
  intro z
  rfl

/-- Coercing the split-kernel equivalence to the completed source gives the completed original
kernel inclusion. -/
@[simp]
theorem coe_kerEquivOfRightInverse_apply
    (I : Ideal R) (f : M →ₗ[R] N) (r : N →ₗ[R] M)
    (h : f.comp r = LinearMap.id)
    (z : AdicCompletion I (LinearMap.ker f)) :
    ((kerEquivOfRightInverse I f r h z : LinearMap.ker (map I f)) :
      AdicCompletion I M) = map I (LinearMap.ker f).subtype z :=
  LinearMap.congr_fun (subtype_comp_kerEquivOfRightInverse I f r h) z

/-- On an original kernel element, the split-kernel equivalence agrees with the canonical
map from the original source into its completion. -/
theorem coe_kerEquivOfRightInverse_of
    (I : Ideal R) (f : M →ₗ[R] N) (r : N →ₗ[R] M)
    (h : f.comp r = LinearMap.id) (k : LinearMap.ker f) :
    ((kerEquivOfRightInverse I f r h (of I (LinearMap.ker f) k) :
      LinearMap.ker (map I f)) : AdicCompletion I M) = of I M (k : M) := by
  rw [coe_kerEquivOfRightInverse_apply, map_of]
  rfl

/-- The inverse split-kernel equivalence is completion of the original split projector,
restricted to the completed-map kernel. The projector is the first coordinate of Mathlib's
original splitting equivalence. -/
theorem kerEquivOfRightInverse_symm_toLinearMap
    (I : Ideal R) (f : M →ₗ[R] N) (r : N →ₗ[R] M)
    (h : f.comp r = LinearMap.id) :
    let E0 : M ≃ₗ[R] (LinearMap.ker f × N) :=
      ((LinearMap.exact_subtype_ker_map f).splitSurjectiveEquiv
        (Submodule.injective_subtype (LinearMap.ker f)) ⟨r, h⟩).1
    let P : M →ₗ[R] LinearMap.ker f :=
      (LinearMap.fst R (LinearMap.ker f) N).comp E0.toLinearMap
    (kerEquivOfRightInverse I f r h).symm.toLinearMap =
      (map I P).comp (LinearMap.ker (map I f)).subtype := by
  dsimp only
  apply LinearMap.ext
  intro z
  rfl

end SplitSurjection

/-- A finitely generated positive ideal power identifies every ideal-power submodule of the
completion with the kernel of its evaluation map. -/
theorem pow_smul_top_eq_ker_eval_of_fg_pos_pow
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) :
    (I ^ k) • (⊤ : Submodule R (AdicCompletion I M)) =
      (AdicCompletion.eval I M k).ker := by
  refine le_antisymm (pow_smul_top_le_ker_eval ..) ?_
  intro z hz
  -- Work at a higher finitely generated power, not at the possibly non-finitely generated `I ^ k`.
  let m := n * (k + 1)
  have hkm : k ≤ m :=
    (Nat.le_succ k).trans (Nat.le_mul_of_pos_left (k + 1) hn)
  have hfg : (I ^ m).FG := by
    simpa only [m, pow_mul] using (Ideal.FG.pow (n := k + 1) hI)
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective
    (I ^ m • (⊤ : Submodule R M)) (eval I M m z)
  have hak : Submodule.mkQ (I ^ k • (⊤ : Submodule R M)) a = 0 := by
    calc
      _ = transitionMap I M hkm (Submodule.mkQ (I ^ m • (⊤ : Submodule R M)) a) :=
        (Submodule.factor_mk (Submodule.pow_smul_top_le I M hkm) a).symm
      _ = transitionMap I M hkm (eval I M m z) := by rw [ha]
      _ = eval I M k z := transitionMap_comp_eval_apply I M hkm z
      _ = 0 := LinearMap.mem_ker.mp hz
  have hamem : a ∈ I ^ k • (⊤ : Submodule R M) :=
    (Submodule.Quotient.mk_eq_zero _).mp hak
  have hoa : of I M a ∈ I ^ k • (⊤ : Submodule R (AdicCompletion I M)) :=
    (Submodule.smul_top_le_comap_smul_top (I ^ k) (of I M)) hamem
  have hres : z - of I M a ∈ I ^ m • (⊤ : Submodule R (AdicCompletion I M)) := by
    rw [pow_smul_top_eq_ker_eval_of_fg_pow hfg, LinearMap.mem_ker,
      map_sub, eval_of, ha, sub_self]
  have hresk := Submodule.pow_smul_top_le I (AdicCompletion I M) hkm hres
  simpa only [sub_add_cancel] using Submodule.add_mem _ hresk hoa

end AdicCompletion
