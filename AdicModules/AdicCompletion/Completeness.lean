/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
/-
The diagonal completeness argument is adapted from Mathlib:
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import AdicModules.Ideal.Cotangent

import AdicModules.AdicCompletion.Kernel
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose

set_option warningAsError true

/-!
# Adic separation, completeness and sums of ideals

Hausdorffness transfers along injective linear maps. Every linear map takes the
intrinsic ideal-power filtration into the target filtration; target Hausdorffness
and injectivity then give source Hausdorffness. No strictness or closed-image
condition is required.

Projective modules over an `I`-Hausdorff coefficient ring are `I`-Hausdorff,
without finite-generation or completeness assumptions.

Equality of the intrinsic ideal-power filtration with the evaluation kernels makes
`AdicCompletion I M` intrinsically `I`-adically complete for its original `R`-module
structure. Finite generation of a positive power of `I` supplies this equality.
The all-stage evaluation-kernel identity turns the compatible diagonal family of a Cauchy
sequence into an intrinsic limit. Finiteness of the cotangent of one positive original ideal
power over its quotient ring also gives intrinsic completeness, for the extended ideal acting
on every completed module. In particular, finite original cotangent suffices.

Precompleteness for two arbitrary ideals implies precompleteness for their sum.
The proof splits successive differences of an even subsequence into two sequences
of increasingly small terms, then applies precompleteness to their finite partial sums.
It does not require finite generation or Hausdorffness.

Precompleteness descends along surjective linear maps. Consequently, the
Hausdorffification of a precomplete module is adically complete.
A module annihilated by one power of an ideal is complete for that ideal;
`IsAdicComplete.of_pow_smul_top_eq_bot` applies directly to the original module.

Completeness for an arbitrary ideal implies completeness for every principal
subideal. Finite coefficient tails provide the principal-power witnesses; ambient
Hausdorffness identifies their scalar multiples with the original limit.
Precompleteness for a finite family of ideals implies precompleteness for their sum.

* `IsPrecomplete.span_finset` gives precompleteness for a finitely generated ideal
  from precompleteness for the principal ideals of its chosen generators.
* `isAdicComplete_span_finset_iff` characterizes completeness for that ideal by
  completeness for those principal ideals, assuming Hausdorffness for the whole ideal.

## References

* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Exercise 0.7.4, for the motivating finite family of principal ideals.
* Mathlib's adic completeness API by Kenny Lau, Judith Ludwig, Christian Merten
  and Jiedong Jiang, and its submodule congruence API by Kenny Lau, provide
  the predicates and zero-submodule congruence criterion used here.
* Mathlib's `Module.forall_dual_apply_eq_zero_iff` supplies separation by dual maps
  for projective modules of arbitrary rank.
* Bingyu Xia's `AdicCompletion.isAdicComplete` in Mathlib's
  `RingTheory/AdicCompletion/Completeness.lean` supplies the diagonal completeness argument;
  here equality of the intrinsic filtration with the evaluation kernels suffices.
  Finite generation of one positive ideal power supplies this equality.
* The finite-cotangent conclusion uses Mathlib's original cotangent module and the shared
  finite-coefficient kernel argument in `AdicModules.AdicCompletion.Kernel`.
-/

@[expose] public section

universe u v
universe uR uM uN

/-- A module admitting an injective linear map into an adically Hausdorff module
is adically Hausdorff for the same ideal. -/
theorem IsHausdorff.of_injective
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    [IsHausdorff I N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    IsHausdorff I M := by
  constructor
  intro x hx
  apply hf
  rw [map_zero]
  apply (inferInstance : IsHausdorff I N).haus
  intro n
  simpa only [map_zero] using
    ((hx n).map f).mono
      (Submodule.map_le_iff_le_comap.mpr
        (Submodule.smul_top_le_comap_smul_top (I ^ n) f))

namespace AdicCompletion

/-- Evaluation kernels equal to the intrinsic filtration give intrinsic completeness.
This follows Bingyu Xia's diagonal completeness argument. -/
theorem isAdicComplete_of_pow_smul_top_eq_ker_eval
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M]
    (h : ∀ n : ℕ,
      (I ^ n) • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker) :
    IsAdicComplete I (AdicCompletion I M) := by
  refine { toIsHausdorff := inferInstance, toIsPrecomplete := ⟨?_⟩ }
  intro x hx
  let L : AdicCompletion I M := {
    val k := (x k).val k
    property {a b} hab := by
      rw [transitionMap_comp_eval_apply]
      have hmem := pow_smul_top_le_ker_eval (M := M) I a (SModEq.sub_mem.mp (hx hab))
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hmem
      exact hmem.symm
  }
  refine ⟨L, fun k => ?_⟩
  rw [SModEq.sub_mem, h k, LinearMap.mem_ker, map_sub, sub_eq_zero]
  rfl

/-- The adic completion is complete for its ideal-power filtration if a positive power of the
ideal is finitely generated. This generalizes Mathlib's `AdicCompletion.isAdicComplete`,
following Bingyu Xia's diagonal completeness argument. -/
theorem isAdicComplete_of_fg_pow
    {R : Type u} [CommRing R] {I : Ideal R}
    {M : Type v} [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) :
    IsAdicComplete I (AdicCompletion I M) :=
  isAdicComplete_of_pow_smul_top_eq_ker_eval I M
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI)

/-- A positive power with finite cotangent makes every completed module complete
for the canonically extended ideal. -/
theorem isAdicComplete_map_of_finite_cotangent_pow
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M]
    {p : ℕ} (hp : 0 < p)
    [Module.Finite (R ⧸ I ^ p) (I ^ p).Cotangent] :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R)))
      (AdicCompletion I M) :=
  (IsAdicComplete.map_algebraMap_iff I (AdicCompletion I M)).mpr
    (isAdicComplete_of_pow_smul_top_eq_ker_eval I M
      (pow_smul_top_eq_ker_eval_of_finite_cotangent_pow I M hp))

/-- Finite cotangent makes every completed module complete for the extended ideal. -/
theorem isAdicComplete_map_of_finite_cotangent
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite (R ⧸ I) I.Cotangent] :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R)))
      (AdicCompletion I M) := by
  let : Module.Finite (R ⧸ I ^ 1) (I ^ 1).Cotangent := by
    rw [pow_one]
    infer_instance
  exact isAdicComplete_map_of_finite_cotangent_pow I M (p := 1) Nat.zero_lt_one

end AdicCompletion

/-- A projective module over an adically Hausdorff coefficient ring is adically Hausdorff. -/
theorem IsHausdorff.of_projective
    {R : Type uR} [CommRing R] (I : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] [Module.Projective R M] [IsHausdorff I R] :
    IsHausdorff I M := by
  constructor
  intro x hx
  apply (Module.forall_dual_apply_eq_zero_iff R x).mp
  intro φ
  apply IsHausdorff.haus ‹IsHausdorff I R› (φ x)
  intro n
  rw [SModEq.sub_mem, sub_zero]
  exact Submodule.smul_top_le_comap_smul_top (I ^ n) φ
    (by simpa only [SModEq.sub_mem, sub_zero] using hx n)

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

namespace IsPrecomplete

private theorem sum_range_cauchy {I : Ideal R} {a : ℕ → M}
    (ha : ∀ n, a n ∈ (I ^ n • ⊤ : Submodule R M)) :
    ∀ {m n}, m ≤ n →
      (∑ k ∈ Finset.range m, a k) ≡ (∑ k ∈ Finset.range n, a k)
        [SMOD (I ^ m • ⊤ : Submodule R M)] := by
  intro m n hmn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => exact SModEq.rfl
  | succ d hd =>
    rw [Nat.add_succ, Finset.sum_range_succ]
    have hmem : a (m + d) ∈ (I ^ m • ⊤ : Submodule R M) :=
      Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_add_right m d)) le_rfl (ha _)
    have hz : (0 : M) ≡ a (m + d) [SMOD (I ^ m • ⊤ : Submodule R M)] :=
      (SModEq.sub_mem.mpr (by simpa only [sub_zero] using hmem) :
        a (m + d) ≡ 0 [SMOD (I ^ m • ⊤ : Submodule R M)]).symm
    exact hd.trans (by simpa only [add_zero] using (SModEq.refl _).add hz)

/-- Precompleteness for two ideals implies precompleteness for their sum, without
finite-generation or separatedness assumptions. This gives the binary precompleteness
implication underlying Fujiwara–Kato, *Foundations of Rigid Geometry I*, Exercise 0.7.4. -/
theorem sup {I J : Ideal R} (hI : IsPrecomplete I M) (hJ : IsPrecomplete J M) :
    IsPrecomplete (I ⊔ J) M := by
  classical
  constructor
  intro f hf
  have hsplit (n : ℕ) :
      ∃ a ∈ (I ^ n • ⊤ : Submodule R M),
        ∃ b ∈ (J ^ n • ⊤ : Submodule R M), a + b = f (2 * (n + 1)) - f (2 * n) := by
    have hd : f (2 * (n + 1)) - f (2 * n) ∈
        ((I ⊔ J) ^ (n + n) • ⊤ : Submodule R M) := by
      simpa only [two_mul] using
        SModEq.sub_mem.mp (hf (Nat.mul_le_mul_left 2 (Nat.le_succ n))).symm
    have hmem := Submodule.smul_mono
      (Ideal.sup_pow_add_le_pow_sup_pow (I := I) (J := J) (n := n) (m := n)) le_rfl hd
    rw [Submodule.sup_smul] at hmem
    exact Submodule.mem_sup.mp hmem
  choose a ha b hb hab using hsplit
  obtain ⟨x, hx⟩ := hI.prec (sum_range_cauchy ha)
  obtain ⟨y, hy⟩ := hJ.prec (sum_range_cauchy hb)
  refine ⟨f 0 + (x + y), fun n => ?_⟩
  have htel : (∑ k ∈ Finset.range n, a k) + (∑ k ∈ Finset.range n, b k) =
      f (2 * n) - f 0 := by
    calc
      _ = ∑ k ∈ Finset.range n, (a k + b k) := Finset.sum_add_distrib.symm
      _ = ∑ k ∈ Finset.range n, (f (2 * (k + 1)) - f (2 * k)) :=
        Finset.sum_congr rfl (fun k _ => hab k)
      _ = f (2 * n) - f 0 := by
        simpa only [mul_zero] using Finset.sum_range_sub (fun k => f (2 * k)) n
  have hsum :
      (∑ k ∈ Finset.range n, a k) + (∑ k ∈ Finset.range n, b k) ≡ x + y
        [SMOD ((I ⊔ J) ^ n • ⊤ : Submodule R M)] :=
    ((hx n).mono (Submodule.smul_mono (pow_le_pow_left' le_sup_left n) le_rfl)).add
      ((hy n).mono (Submodule.smul_mono (pow_le_pow_left' le_sup_right n) le_rfl))
  have heven : f (2 * n) ≡ f 0 + (x + y)
      [SMOD ((I ⊔ J) ^ n • ⊤ : Submodule R M)] := by
    have h := (SModEq.refl (f 0)).add hsum
    have heq : f 0 + ((∑ k ∈ Finset.range n, a k) + (∑ k ∈ Finset.range n, b k)) =
        f (2 * n) := by
      rw [htel]
      abel
    rwa [heq] at h
  exact (hf (by simpa only [two_mul] using Nat.le_add_right n n)).trans heven

end IsPrecomplete

universe w

/-- Precompleteness descends along a surjective linear map. -/
theorem IsPrecomplete.of_surjective {I : Ideal R} {N : Type w}
    [AddCommGroup N] [Module R N] [IsPrecomplete I M] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : IsPrecomplete I N := by
  apply AdicCompletion.of_surjective_iff.mp
  intro x
  obtain ⟨y, hy⟩ := AdicCompletion.map_surjective_of_mkQ_comp_surjective
    (I := I) (f := f)
    ((Submodule.mkQ_surjective (I • ⊤ : Submodule R N)).comp hf) x
  obtain ⟨m, hm⟩ := AdicCompletion.of_surjective I M y
  exact ⟨f m, by rw [← AdicCompletion.map_of I f m, hm, hy]⟩

namespace Hausdorffification

/-- The Hausdorffification of a precomplete module is adically complete. -/
instance (I : Ideal R) [IsPrecomplete I M] : IsAdicComplete I (Hausdorffification I M) where
  toIsHausdorff := inferInstance
  toIsPrecomplete :=
    IsPrecomplete.of_surjective (of I M) (Submodule.mkQ_surjective _)

end Hausdorffification

namespace IsAdicComplete

/-- A module annihilated by one power of an ideal is complete for that ideal,
including annihilation at exponent zero. -/
theorem of_pow_smul_top_eq_bot {I : Ideal R} {n : ℕ}
    (h : (I ^ n • ⊤ : Submodule R M) = ⊥) : IsAdicComplete I M := by
  refine { toIsHausdorff := ⟨?_⟩, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    simpa only [h, SModEq.bot] using hx n
  · intro f hf
    refine ⟨f n, fun k => ?_⟩
    rcases le_total k n with hkn | hnk
    · exact hf hkn
    · have heq : f n = f k := by
        simpa only [h, SModEq.bot] using hf hnk
      rw [heq]

open scoped Pointwise

private theorem mem_span_singleton_pow_smul_top {a : R} {n : ℕ} {x : M} :
    x ∈ ((Ideal.span {a}) ^ n • ⊤ : Submodule R M) ↔ ∃ m : M, a ^ n • m = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

private theorem smul_sum_range_eq_sub {a : R} {f m : ℕ → M}
    (hm : ∀ n, a ^ n • m n = f (n + 1) - f n) (k n : ℕ) :
    a ^ k • (∑ j ∈ Finset.range n, a ^ j • m (k + j)) = f (k + n) - f k := by
  calc
    _ = ∑ j ∈ Finset.range n, a ^ (k + j) • m (k + j) := by
      simp only [Finset.smul_sum, pow_add, mul_smul]
    _ = ∑ j ∈ Finset.range n, (f ((k + j) + 1) - f (k + j)) :=
      Finset.sum_congr rfl (fun j _ => hm (k + j))
    _ = f (k + n) - f k := by
      simpa only [Nat.add_zero, Nat.add_assoc] using
        Finset.sum_range_sub (fun j => f (k + j)) n

/-- Completeness for an ideal implies completeness for each principal subideal,
without finite-generation assumptions. This gives the principal transfer implication
underlying Fujiwara–Kato, *Foundations of Rigid Geometry I*, Exercise 0.7.4. -/
theorem span_singleton {I : Ideal R} {a : R} (ha : a ∈ I) [IsAdicComplete I M] :
    IsAdicComplete (Ideal.span {a}) M := by
  classical
  have hJI : Ideal.span {a} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr ha
  have hpow (n : ℕ) :
      ((Ideal.span {a}) ^ n • ⊤ : Submodule R M) ≤ (I ^ n • ⊤ : Submodule R M) :=
    Submodule.smul_mono (pow_le_pow_left' hJI n) le_rfl
  refine { toIsHausdorff := ⟨?_⟩, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    exact (inferInstance : IsHausdorff I M).haus x (fun n => (hx n).mono (hpow n))
  · intro f hf
    have hd (n : ℕ) : ∃ m : M, a ^ n • m = f (n + 1) - f n :=
      mem_span_singleton_pow_smul_top.mp (SModEq.sub_mem.mp (hf (Nat.le_succ n)).symm)
    choose m hm using hd
    obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete I M).prec
      (fun {p q} hpq => (hf hpq).mono (hpow p))
    refine ⟨L, fun k => ?_⟩
    have htail (n : ℕ) : a ^ n • m (k + n) ∈ (I ^ n • ⊤ : Submodule R M) :=
      Submodule.smul_mem_smul (Ideal.pow_mem_pow ha n) (Submodule.mem_top)
    obtain ⟨v, hv⟩ := (inferInstance : IsPrecomplete I M).prec
      (IsPrecomplete.sum_range_cauchy htail)
    have hzero : L - f k - a ^ k • v = 0 := by
      apply (inferInstance : IsHausdorff I M).haus
      intro p
      apply SModEq.sub_mem.mpr
      simp only [sub_zero]
      have hfirst : L - f (k + p) ∈ (I ^ p • ⊤ : Submodule R M) :=
        Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_add_left p k)) le_rfl
          (SModEq.sub_mem.mp (hL (k + p)).symm)
      have hsecond : a ^ k • (v - ∑ j ∈ Finset.range p, a ^ j • m (k + j)) ∈
          (I ^ p • ⊤ : Submodule R M) :=
        Submodule.smul_mem _ _ (SModEq.sub_mem.mp (hv p).symm)
      have heq : L - f k - a ^ k • v =
          (L - f (k + p)) - a ^ k • (v - ∑ j ∈ Finset.range p, a ^ j • m (k + j)) := by
        rw [smul_sub, smul_sum_range_eq_sub hm k p]
        abel
      rw [heq]
      exact Submodule.sub_mem _ hfirst hsecond
    have hmem : L - f k ∈ ((Ideal.span {a}) ^ k • ⊤ : Submodule R M) :=
      mem_span_singleton_pow_smul_top.mpr ⟨v, (sub_eq_zero.mp hzero).symm⟩
    exact (SModEq.sub_mem.mpr hmem).symm

end IsAdicComplete

universe w₁

namespace IsPrecomplete

variable {ι : Type w₁}

/-- Precompleteness for every ideal in a finite family implies precompleteness for their sum. -/
theorem finset_sup (J : ι → Ideal R) (s : Finset ι)
    (h : ∀ i ∈ s, IsPrecomplete (J i) M) : IsPrecomplete (s.sup J) M := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa only [Finset.sup_empty] using (IsPrecomplete.bot (R := R) (M := M))
  · intro i t _ ih h
    rw [Finset.sup_insert]
    exact (h i (Finset.mem_insert_self i t)).sup
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Precompleteness for the principal ideals generated by the members of a finite set
implies precompleteness for the ideal generated by that set. -/
theorem span_finset (s : Finset R) (h : ∀ a ∈ s, IsPrecomplete (Ideal.span {a}) M) :
    IsPrecomplete (Ideal.span (s : Set R)) M := by
  classical
  have hsup := IsPrecomplete.finset_sup (fun a : R => Ideal.span {a}) s h
  rw [Finset.sup_eq_iSup] at hsup
  change IsPrecomplete (Submodule.span R (s : Set R)) M
  rw [Submodule.span_eq_iSup_of_singleton_spans]
  exact hsup

end IsPrecomplete

/-- For a module Hausdorff with respect to the ideal generated by a finite set,
completeness for that ideal is equivalent to completeness for the principal ideals
generated by the members of the set. -/
theorem isAdicComplete_span_finset_iff (s : Finset R)
    [IsHausdorff (Ideal.span (s : Set R)) M] :
    IsAdicComplete (Ideal.span (s : Set R)) M ↔
      ∀ a ∈ s, IsAdicComplete (Ideal.span {a}) M := by
  constructor
  · intro h a ha
    have := h
    exact IsAdicComplete.span_singleton (M := M) (Ideal.subset_span ha)
  · intro h
    have hpre : ∀ a ∈ s, IsPrecomplete (Ideal.span {a}) M := by
      intro a ha
      have := h a ha
      infer_instance
    exact { toIsHausdorff := inferInstance
            toIsPrecomplete := IsPrecomplete.span_finset s hpre }
