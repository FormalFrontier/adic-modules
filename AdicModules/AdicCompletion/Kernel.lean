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
public import AdicModules.Ideal.Cotangent

import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Finsupp.Span
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Kernels under adic completion and reduction

For an ideal `I` of a commutative ring `R` and an `R`-module `M`, finite generation of the
single power `I ^ n` identifies the kernel of `AdicCompletion.eval I M n` with
`(I ^ n) • ⊤` in `Submodule R (AdicCompletion I M)`. The exponent may be zero, and the ring
and module may lie in independent universes.

Finiteness of the stock cotangent module of one positive ideal power `I ^ p` over `R ⧸ I ^ p`
gives this equality at every degree, without assuming finite generation of any original ideal
power. Finite original cotangent and finite generation of a positive original power are special
cases. A finitely generated ideal `H` whose action on `M`, together with `I ^ (n + 1) • ⊤`,
generates `I ^ n • ⊤` already computes the evaluation kernel at `n`. In particular, it suffices
that `H` generates `I ^ n` modulo `I ^ (n + 1)` as ideals.
Applying this to auxiliary powers gives cofinally many stages;
lifting a higher coordinate to the original module then descends the equality to any lower stage.
Neither the original module nor its first quotient nor its completion is assumed finite.

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
finite-linear-combination argument to a finitely generated coefficient ideal whose action generates
`I ^ n • ⊤` modulo `I ^ (n + 1) • ⊤`. The original coefficient map need only be surjective after
the first reduction of `I ^ n • ⊤`; Mathlib's first-reduction surjectivity theorem and finite
direct-sum comparison then compute its completed range. The single-power finite-generation theorem
is a specialization of this argument.

The cotangent argument uses Mathlib's ideal cotangent formalization by Andrew Yang and the
span-modulo-square bridge in `AdicModules.Ideal.Cotangent`. The positive-power argument
applies the same bridge to `I ^ p` and reuses the higher-coordinate lifting argument for descent.

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

/-- A finite coefficient family whose map is onto the first target reduction computes
an evaluation kernel after completion. -/
private theorem span_smul_top_eq_ker_eval_of_mkQ_comp_surjective
    {n : ℕ} {ι : Type*} [Finite ι] (a : ι → R)
    (f : (ι →₀ M) →ₗ[R] ↥(I ^ n • (⊤ : Submodule R M)))
    (hfactor : (I ^ n • (⊤ : Submodule R M)).subtype.comp f =
      lsum R (fun i : ι => a i • (LinearMap.id : M →ₗ[R] M)))
    (hmodI : Function.Surjective
      ((I • (⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M)))).mkQ.comp f)) :
    (Ideal.span (Set.range a)) • (⊤ : Submodule R (AdicCompletion I M)) =
      (eval I M n).ker := by
  classical
  let := Fintype.ofFinite ι
  let g₀ : (ι →₀ M) →ₗ[R] M :=
    lsum R (fun i : ι => a i • (LinearMap.id : M →ₗ[R] M))
  let g : (ι →₀ AdicCompletion I M) →ₗ[AdicCompletion I R] AdicCompletion I M :=
    lsum (AdicCompletion I R) (fun i : ι =>
      algebraMap R (AdicCompletion I R) (a i) •
        (LinearMap.id : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I M))
  have hspan : (Ideal.span (Set.range a)) •
      (⊤ : Submodule R (AdicCompletion I M)) = g.range.restrictScalars R := by
    rw [span_smul_eq,
      ← restrictScalars_top R (AdicCompletion I R) (AdicCompletion I M),
      ← restrictScalars_image_smul_eq (R := AdicCompletion I R), ← Set.range_comp]
    apply congrArg (fun P : Submodule (AdicCompletion I R) (AdicCompletion I M) =>
      P.restrictScalars R)
    simpa only [g, Function.comp_def, LinearMap.range_id] using
      (range_lsum_smul
        (LinearMap.id : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I M)
        ((algebraMap R (AdicCompletion I R)) ∘ a)).symm
  have hsum : Function.Surjective
      (map I (finsuppLEquivDirectSum R M ι).symm.toLinearMap) :=
    Function.RightInverse.surjective (g := map I (finsuppLEquivDirectSum R M ι))
      (fun _ ↦ by simp [← LinearMap.comp_apply, map_comp])
  have hg : g.range = (map I g₀).range := by
    dsimp only [g, g₀]
    rw [← LinearMap.range_comp_of_range_eq_top
        (f := (finsuppLEquivDirectSum (AdicCompletion I R)
          (AdicCompletion I M) ι).symm.toLinearMap) _ (by simp),
      lsum_smul_comp_finsuppLEquivDirectSum_symm,
      LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
      LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top_of_surjective _ hsum)]
  have hsurj : Function.Surjective (map I f) :=
    map_surjective_of_mkQ_comp_surjective hmodI
  have hfactor' : (I ^ n • (⊤ : Submodule R M)).subtype.comp f = g₀ := hfactor
  have hcompleted : (map I g₀).range = (ofPowSMul I M n).range := by
    calc
      (map I g₀).range =
          ((map I (I ^ n • (⊤ : Submodule R M)).subtype).comp (map I f)).range := by
        rw [map_comp, hfactor']
      _ = (ofPowSMul I M n).range :=
        LinearMap.range_comp_of_range_eq_top _
          (LinearMap.range_eq_top_of_surjective _ hsurj)
  calc
    (Ideal.span (Set.range a)) • (⊤ : Submodule R (AdicCompletion I M)) =
        g.range.restrictScalars R := hspan
    _ = (map I g₀).range.restrictScalars R := by rw [hg]
    _ = (ofPowSMul I M n).range.restrictScalars R := by rw [hcompleted]
    _ = (eval I M n).ker := restrictScalars_range_ofPowSMul_eq_ker_eval I

/-- A finitely generated coefficient ideal whose action generates an original power submodule
modulo the next power submodule computes the completed evaluation kernel. -/
theorem smul_top_eq_ker_eval_of_fg_sup_pow_smul
    (I H : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (hH : H.FG)
    (hpow : (H • (⊤ : Submodule R M)) ⊔
      (I ^ (n + 1) • (⊤ : Submodule R M)) = I ^ n • (⊤ : Submodule R M)) :
    H • (⊤ : Submodule R (AdicCompletion I M)) =
      (AdicCompletion.eval I M n).ker := by
  classical
  have hModuleSup : H • (⊤ : Submodule R M) ≤ I ^ n • ⊤ :=
    le_sup_left.trans hpow.le
  obtain ⟨k, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hH
  rw [Ideal.submodule_span_eq] at ha
  let N : Submodule R M := I ^ n • ⊤
  let f₀ : (Fin k →₀ M) →ₗ[R] M :=
    lsum R (fun i : Fin k => a i • (LinearMap.id : M →ₗ[R] M))
  have hfRange : f₀.range = H • (⊤ : Submodule R M) := by
    dsimp only [f₀]
    rw [range_lsum_smul, LinearMap.range_id, ← span_smul_eq, ha]
  have hf : ∀ x, f₀ x ∈ N := by
    intro x
    exact hModuleSup (hfRange ▸ LinearMap.mem_range_self f₀ x)
  let f : (Fin k →₀ M) →ₗ[R] N := f₀.codRestrict N hf
  have hfactor : N.subtype.comp f = f₀ :=
    LinearMap.subtype_comp_codRestrict _ _ _
  have hfr : f.range.map N.subtype = H • (⊤ : Submodule R M) := by
    rw [← LinearMap.range_comp, hfactor, hfRange]
  have hsmul : (I • (⊤ : Submodule R N)).map N.subtype =
      I ^ (n + 1) • (⊤ : Submodule R M) := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
    dsimp only [N]
    rw [← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_succ']
  have hsup : I • (⊤ : Submodule R N) ⊔ f.range = ⊤ := by
    apply Submodule.map_injective_of_injective N.injective_subtype
    rw [Submodule.map_sup, hsmul, hfr, Submodule.map_subtype_top]
    change I ^ (n + 1) • (⊤ : Submodule R M) ⊔ H • ⊤ = I ^ n • ⊤
    rw [sup_comm, hpow]
  have hmodI : Function.Surjective ((I • (⊤ : Submodule R N)).mkQ.comp f) := by
    apply LinearMap.range_eq_top.mp
    rw [LinearMap.range_comp, Submodule.map_mkQ_eq_top]
    exact hsup
  have heq := span_smul_top_eq_ker_eval_of_mkQ_comp_surjective
    (I := I) (M := M) (n := n) a f hfactor hmodI
  simpa only [ha] using heq

/-- A finitely generated ideal generating an original power modulo the next power computes its
completed evaluation kernel. -/
theorem smul_top_eq_ker_eval_of_fg_sup_pow
    (I H : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (hH : H.FG) (hpow : H ⊔ I ^ (n + 1) = I ^ n) :
    H • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker := by
  apply smul_top_eq_ker_eval_of_fg_sup_pow_smul I H M n hH
  simpa only [Submodule.sup_smul] using
    congrArg (fun J : Ideal R => J • (⊤ : Submodule R M)) hpow

/-- If `I ^ n` is finitely generated, its scalar multiple of the whole completed module is
exactly the kernel of evaluation at `n`. This replaces the hypothesis `I.FG` in Mathlib's
`AdicCompletion.pow_smul_top_eq_ker_eval` by finite generation of the single power, following
its finite-linear-combination proof. -/
theorem pow_smul_top_eq_ker_eval_of_fg_pow {n : ℕ} (h : (I ^ n).FG) :
    (I ^ n) • (⊤ : Submodule R (AdicCompletion I M)) = (AdicCompletion.eval I M n).ker := by
  exact smul_top_eq_ker_eval_of_fg_sup_pow I (I ^ n) M n h
    (sup_eq_left.mpr (Ideal.pow_le_pow_right (Nat.le_succ n)))

/-- An ideal congruence modulo the square gives the corresponding congruence at every degree. -/
private theorem pow_eq_sup_next (I H : Ideal R) (hI : I = H ⊔ I ^ 2) (n : ℕ) :
    I ^ n = H ^ n ⊔ I ^ (n + 1) := by
  have hHI : H ≤ I := le_sup_left.trans hI.ge
  refine le_antisymm ?_
    (sup_le (Ideal.pow_right_mono hHI n) (Ideal.pow_le_pow_right (Nat.le_succ n)))
  induction n with
  | zero => simp
  | succ n ih =>
    have hnext : H ^ n * I ^ 2 ≤ I ^ (n + 2) := by
      calc
        H ^ n * I ^ 2 ≤ I ^ n * I ^ 2 :=
          Ideal.mul_mono_left (Ideal.pow_right_mono hHI n)
        _ = I ^ (n + 2) := (pow_add I n 2).symm
    have hHI' : H ^ n * I ≤ H ^ (n + 1) ⊔ I ^ (n + 2) := by
      calc
        H ^ n * I = H ^ n * (H ⊔ I ^ 2) :=
          congrArg (fun K : Ideal R => H ^ n * K) hI
        _ = H ^ n * H ⊔ H ^ n * I ^ 2 := Ideal.mul_sup _ _ _
        _ ≤ H ^ (n + 1) ⊔ I ^ (n + 2) :=
          sup_le_sup (le_of_eq (pow_succ H n).symm) hnext
    calc
      I ^ (n + 1) = I ^ n * I := pow_succ I n
      _ ≤ (H ^ n ⊔ I ^ (n + 1)) * I := Ideal.mul_mono_left ih
      _ = H ^ n * I ⊔ I ^ (n + 1) * I := Ideal.sup_mul _ _ _
      _ ≤ H ^ (n + 1) ⊔ I ^ (n + 2) := sup_le hHI' (by
        rw [← pow_succ]
        exact le_sup_right)

/-- An evaluation-kernel equality descends from a higher precision. -/
theorem pow_smul_top_eq_ker_eval_of_le
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    {m n : ℕ} (hnm : n ≤ m)
    (hm : (I ^ m) • (⊤ : Submodule R (AdicCompletion I M)) =
      (eval I M m).ker) :
    (I ^ n) • (⊤ : Submodule R (AdicCompletion I M)) =
      (eval I M n).ker := by
  refine le_antisymm (pow_smul_top_le_ker_eval ..) ?_
  intro z hz
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective
    (I ^ m • (⊤ : Submodule R M)) (eval I M m z)
  have han : Submodule.mkQ (I ^ n • (⊤ : Submodule R M)) a = 0 := by
    calc
      _ = transitionMap I M hnm (Submodule.mkQ (I ^ m • (⊤ : Submodule R M)) a) :=
        (Submodule.factor_mk (Submodule.pow_smul_top_le I M hnm) a).symm
      _ = transitionMap I M hnm (eval I M m z) := by rw [ha]
      _ = eval I M n z := transitionMap_comp_eval_apply I M hnm z
      _ = 0 := LinearMap.mem_ker.mp hz
  have hamem : a ∈ I ^ n • (⊤ : Submodule R M) :=
    (Submodule.Quotient.mk_eq_zero _).mp han
  have hoa : of I M a ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I M)) :=
    (Submodule.smul_top_le_comap_smul_top (I ^ n) (of I M)) hamem
  have hres : z - of I M a ∈ I ^ m • (⊤ : Submodule R (AdicCompletion I M)) := by
    rw [hm, LinearMap.mem_ker, map_sub, eval_of, ha, sub_self]
  have hresn := Submodule.pow_smul_top_le I (AdicCompletion I M) hnm hres
  simpa only [sub_add_cancel] using Submodule.add_mem _ hresn hoa

/-- Finite cotangent of a positive ideal power identifies every evaluation kernel. -/
theorem pow_smul_top_eq_ker_eval_of_finite_cotangent_pow
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    {p : ℕ} (hp : 0 < p)
    [Module.Finite (R ⧸ I ^ p) (I ^ p).Cotangent] (n : ℕ) :
    (I ^ n) • (⊤ : Submodule R (AdicCompletion I M)) =
      (eval I M n).ker := by
  classical
  obtain ⟨r, v, hv⟩ := Ideal.exists_fin_span_toCotangent_eq_top (I ^ p)
  let H : Ideal R := Ideal.span (Set.range (fun i : Fin r => (v i : R)))
  have hP : I ^ p = H ⊔ (I ^ p) ^ 2 :=
    Ideal.eq_span_sup_sq_of_span_toCotangent_eq_top (I ^ p) v hv
  have hHI : H ≤ I ^ p := le_sup_left.trans hP.ge
  have hH : H.FG := Submodule.fg_span (Set.finite_range _)
  -- Only the auxiliary powers `H ^ k` are required to be finitely generated.
  have hcofinal (k : ℕ) :
      (I ^ (p * k)) • (⊤ : Submodule R (AdicCompletion I M)) =
        (eval I M (p * k)).ker := by
    have hHpow : H ^ k ≤ I ^ (p * k) := by
      rw [pow_mul]
      exact Ideal.pow_right_mono hHI k
    have hnext : (I ^ p) ^ (k + 1) ≤ I ^ (p * k + 1) := by
      rw [← pow_mul]
      apply Ideal.pow_le_pow_right
      rw [Nat.mul_succ]
      exact Nat.add_le_add_left (Nat.succ_le_of_lt hp) (p * k)
    have hpow : H ^ k ⊔ I ^ (p * k + 1) = I ^ (p * k) := by
      refine le_antisymm
        (sup_le hHpow (Ideal.pow_le_pow_right (Nat.le_succ (p * k)))) ?_
      calc
        I ^ (p * k) = (I ^ p) ^ k := pow_mul I p k
        _ = H ^ k ⊔ (I ^ p) ^ (k + 1) := pow_eq_sup_next (I ^ p) H hP k
        _ ≤ H ^ k ⊔ I ^ (p * k + 1) := sup_le_sup le_rfl hnext
    have hstage := smul_top_eq_ker_eval_of_fg_sup_pow I (H ^ k) M (p * k) hH.pow hpow
    refine le_antisymm (pow_smul_top_le_ker_eval (I := I) (M := M) (p * k)) ?_
    rw [← hstage]
    exact Submodule.smul_mono_left hHpow
  exact pow_smul_top_eq_ker_eval_of_le I M
    ((Nat.le_succ n).trans (Nat.le_mul_of_pos_left (n + 1) hp)) (hcofinal (n + 1))

/-- Finite cotangent identifies the ideal-power filtration on every completed module
with the kernels of evaluation. -/
theorem pow_smul_top_eq_ker_eval_of_finite_cotangent
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite (R ⧸ I) I.Cotangent] (n : ℕ) :
    (I ^ n) • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker := by
  let : Module.Finite (R ⧸ I ^ 1) (I ^ 1).Cotangent := by
    rw [pow_one]
    infer_instance
  exact pow_smul_top_eq_ker_eval_of_finite_cotangent_pow I M (p := 1) Nat.zero_lt_one n

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
  let : Module.Finite (R ⧸ I ^ n) (I ^ n).Cotangent :=
    Ideal.finite_cotangent_of_fg (I ^ n) hI
  exact pow_smul_top_eq_ker_eval_of_finite_cotangent_pow I M hn k

end AdicCompletion
