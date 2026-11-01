/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

The Cauchy-sequence argument follows the Mathlib formalization:
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of that formalization: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.RingTheory.AdicCompletion.Exactness
public import AdicModules.AdicCompletion.LinearMap

import Mathlib.Algebra.Module.Submodule.Equiv
import AdicModules.AdicCompletion.RestrictScalars
import AdicModules.AdicCompletion.TensorProduct
import CoherentModules.RingTheory.Filtration
import CoherentModules.RingTheory.Noetherian
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Images, injectivity and exactness of adic completion

For every ideal, adic completion preserves injectivity of an original linear map
whose original target is Noetherian over the original ring. The original ring need
not be Noetherian, and the ring, source and target universes are independent.

For an arbitrary original map `f : M →ₗ[R] N` with original Noetherian target,
`rangeEquivOfIsNoetherianTarget` identifies completion of the original `f.range`,
with its intrinsic original-ideal filtration, with the range of `map I f` over
`AdicCompletion I R`. Its forward map is completion of the original inclusion.
The source need not be Noetherian or finite, and `f` need not be injective.
The characteristic laws describe all completed range elements, original elements,
and the completed range-restriction square, using the canonical completed actions.

Adic completion also preserves middle exactness of an original right-surjective
exact pair whose original middle module is Noetherian. The original first source
is arbitrary and the first map need not be injective. The ring and all three module
universes are independent.

Adic completion also preserves middle exactness when the topology induced on the
range of the first map is cofinal with its intrinsic adic topology. Neither
injectivity of the first map nor finiteness or Noetherian hypotheses are required
for this range-cofinality criterion.

## Implementation notes

For injectivity, the quotient by the original target's annihilator is Noetherian.
Over this quotient, the existing finite-module tensor comparisons and flatness of
the completed ring give injectivity. Naturality of the existing restriction-of-scalars
comparison returns to the original ideal and the canonical completed map.

The image equivalence uses this injectivity criterion only for the original range
inclusion. The unconditional `range_map_range_subtype` gives its range and hence
surjectivity of its codomain restriction. Mathlib's `LinearEquiv.ofBijective`
then supplies the equivalence and its choice-based inverse; no quotient of the
completed source or new completed-map construction is involved.

The range-cofinality proof uses the existing Cauchy-sequence and completion maps.
At each step, cofinality allows a change of a chosen lift by an element in the
required ideal power. The change need not equal the difference of the original lifts, so the
first map need not be injective. No intrinsic adic completeness of a completion
is assumed.

For a Noetherian original middle module, module Artin–Rees supplies range
cofinality, without imposing a quotient scalar action on the first source.

## References

The construction follows the Cauchy-sequence proof of `AdicCompletion.map_exact`
by Judith Ludwig and Christian Merten in
`Mathlib.RingTheory.AdicCompletion.Exactness`. Pointwise range cofinality replaces
its Artin–Rees bound, and chosen small changes replace its use of injectivity.
The injectivity criterion reuses their canonical tensor comparison, its naturality
and flatness of Noetherian ring completions from
`Mathlib.RingTheory.AdicCompletion.AsTensorProduct`, together with CoherentModules'
annihilator-quotient Noetherianity theorem and the independent-universe tensor and
restriction-of-scalars APIs of this library. The image comparison also uses
Ludwig and Merten's all-ideal completion-surjectivity theorem and Mathlib's
generic range, codomain-restriction and linear-equivalence APIs.

The Noetherian-middle criterion uses CoherentModules' module Artin–Rees theorem,
which generalizes Andrew Yang's formalization in `Mathlib.RingTheory.Filtration`.
-/

@[expose] public section

universe uR uP uN uM

namespace AdicCompletion

open LinearMap

private theorem map_injective_of_finite_of_isNoetherian
    {R : Type uR} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N : Type uN} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (map I f) := by
  have ht : Function.Injective
      (TensorProduct.AlgebraTensorModule.map
        (LinearMap.id : AdicCompletion I R →ₗ[AdicCompletion I R] AdicCompletion I R) f) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := AdicCompletion I R) f hf
  intro x y hxy
  obtain ⟨a, rfl⟩ := (ofTensorProduct_bijective I M).2 x
  obtain ⟨b, rfl⟩ := (ofTensorProduct_bijective I M).2 y
  apply congrArg (ofTensorProduct I M)
  apply ht
  apply (ofTensorProduct_bijective I N).1
  exact (LinearMap.congr_fun (ofTensorProduct_naturality I f) a).symm.trans
    (hxy.trans (LinearMap.congr_fun (ofTensorProduct_naturality I f) b))

/-- Completion preserves injectivity of a linear map whose original target is
Noetherian over the original ring, for every ideal. No Noetherianity of the original
ring, finite generation of the ideal, source finiteness, flatness, separation or
completeness is assumed.

This generalizes Mathlib's `AdicCompletion.map_injective`, formalized by Judith Ludwig
and Christian Merten, to arbitrary original rings and independent ring, source and
target universes. The proof passes to the quotient by the target's annihilator and
uses the existing tensor comparison and restriction-of-scalars naturality. -/
theorem map_injective_of_isNoetherian_target
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    [IsNoetherian R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (AdicCompletion.map I f) := by
  have : IsNoetherian R M := isNoetherian_of_injective f hf
  let K := Module.annihilator R N
  let B := R ⧸ K
  have hM : Module.IsTorsionBySet R M K :=
    (Module.isTorsionBySet_iff_subset_annihilator R M).mpr
      (f.annihilator_le_of_injective hf)
  let : Module B M := hM.module
  let : Module B N := Module.quotientAnnihilator
  let : IsScalarTower R B M := hM.isScalarTower
  let : IsScalarTower R B N := (Module.isTorsionBySet_annihilator R N).isScalarTower
  have : IsNoetherianRing B := isNoetherianRing_quotient_annihilator N
  have : Module.Finite B M := Module.Finite.of_restrictScalars_finite R B M
  have : Module.Finite B N := Module.Finite.of_restrictScalars_finite R B N
  let fB : M →ₗ[B] N :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro b m
        refine Quotient.inductionOn' b (fun r => ?_)
        change f (Ideal.Quotient.mk K r • m) = Ideal.Quotient.mk K r • f m
        rw [hM.mk_smul, (Module.isTorsionBySet_annihilator R N).mk_smul]
        exact f.map_smul r m }
  have hfB : fB.restrictScalars R = f := by
    ext m
    rfl
  let J := I.map (algebraMap R B)
  have hJ : Function.Injective (map J fB) :=
    map_injective_of_finite_of_isNoetherian J fB hf
  intro x y hxy
  apply (restrictScalarsSemilinearMap_bijective (S := B) I M).1
  apply hJ
  rw [← hfB] at hxy
  simpa only [restrictScalarsSemilinearMap_map] using
    congrArg (restrictScalarsSemilinearMap (S := B) I N) hxy

/-- The completion of the original range is the range of the completed map
when the original target is Noetherian over the original coefficient ring.
The forward map is completion of the original range inclusion. -/
noncomputable def rangeEquivOfIsNoetherianTarget
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    [IsNoetherian R N]
    (f : M →ₗ[R] N) :
    AdicCompletion I (LinearMap.range f) ≃ₗ[AdicCompletion I R]
      LinearMap.range (AdicCompletion.map I f) :=
  LinearEquiv.ofBijective
    ((AdicCompletion.map I f.range.subtype).codRestrict
      (LinearMap.range (AdicCompletion.map I f))
      (fun z ↦ (AdicCompletion.range_map_range_subtype I f).le
        (LinearMap.mem_range_self _ z)))
    (by
      constructor
      · intro x y hxy
        apply map_injective_of_isNoetherian_target I f.range.subtype
          (Submodule.injective_subtype f.range)
        exact congrArg Subtype.val hxy
      · intro y
        have hy : (y : AdicCompletion I N) ∈
            LinearMap.range (AdicCompletion.map I f.range.subtype) :=
          (AdicCompletion.range_map_range_subtype I f).ge y.property
        obtain ⟨x, hx⟩ := hy
        exact ⟨x, Subtype.ext hx⟩)

section RangeEquiv

variable {R : Type uR} [CommRing R] (I : Ideal R)
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]
variable [IsNoetherian R N] (f : M →ₗ[R] N)

/-- In the ambient completion, the image equivalence is completion of the
original range inclusion. -/
@[simp]
theorem coe_rangeEquivOfIsNoetherianTarget_apply
    (z : AdicCompletion I (LinearMap.range f)) :
    (rangeEquivOfIsNoetherianTarget I f z : AdicCompletion I N) =
      AdicCompletion.map I f.range.subtype z := by
  simp only [rangeEquivOfIsNoetherianTarget, LinearEquiv.ofBijective_apply,
    LinearMap.codRestrict_apply]

/-- An original range element maps to its canonical image in the target completion. -/
theorem coe_rangeEquivOfIsNoetherianTarget_apply_of
    (y : LinearMap.range f) :
    (rangeEquivOfIsNoetherianTarget I f
      (AdicCompletion.of I (LinearMap.range f) y) : AdicCompletion I N) =
      AdicCompletion.of I N (y : N) := by
  rw [coe_rangeEquivOfIsNoetherianTarget_apply, AdicCompletion.map_of]
  rfl

/-- The image equivalence identifies the completed original range factorization
with the range factorization of the completed map. -/
@[simp]
theorem rangeEquivOfIsNoetherianTarget_map_rangeRestrict
    (x : AdicCompletion I M) :
    rangeEquivOfIsNoetherianTarget I f
        (AdicCompletion.map I f.rangeRestrict x) =
      (AdicCompletion.map I f).rangeRestrict x := by
  apply Subtype.ext
  rw [coe_rangeEquivOfIsNoetherianTarget_apply, AdicCompletion.map_comp_apply,
    LinearMap.subtype_comp_rangeRestrict]
  rfl

end RangeEquiv

variable {R : Type uR} [CommRing R] {I : Ideal R}
variable {P : Type uP} [AddCommGroup P] [Module R P]
variable {N : Type uN} [AddCommGroup N] [Module R N]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {f : P →ₗ[R] N} {g : N →ₗ[R] M}

private theorem exists_cofinal_indices
    (hcofinal : ∀ k : ℕ, ∃ l : ℕ,
      f.range ⊓ (I ^ l • ⊤ : Submodule R N) ≤ I ^ k • f.range) :
    ∃ e : ℕ → ℕ, (∀ n, n ≤ e n) ∧ (∀ n, e n ≤ e (n + 1)) ∧
      ∀ n, f.range ⊓ (I ^ e n • ⊤ : Submodule R N) ≤ I ^ n • f.range := by
  classical
  choose l hl using hcofinal
  let e : ℕ → ℕ := Nat.rec (l 0) (fun n m ↦ max (m + 1) (l (n + 1)))
  have hl_e (n : ℕ) : l n ≤ e n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_right _ _
  have he_step (n : ℕ) : e n ≤ e (n + 1) :=
    (Nat.le_succ (e n)).trans (le_max_left _ _)
  have he_bound (n : ℕ) : n ≤ e n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact (Nat.succ_le_succ ih).trans (le_max_left _ _)
  refine ⟨e, he_bound, he_step, fun n z hz ↦ ?_⟩
  exact hl n ⟨hz.1,
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (hl_e n))) hz.2⟩

private theorem exists_exact_approximation
    (hExact : Function.Exact f g) (hg : Function.Surjective g)
    (x : AdicCauchySequence I N)
    (hker : ∀ n : ℕ, g (x n) ∈ (I ^ n • ⊤ : Submodule R M)) (n : ℕ) :
    ∃ y : P, f y - x n ∈ (I ^ n • ⊤ : Submodule R N) := by
  have hmem : g (x n) ∈ Submodule.map g (I ^ n • ⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, range_eq_top.mpr hg]
    exact hker n
  obtain ⟨d, hdmem, hd⟩ := hmem
  obtain ⟨y, hy⟩ := (hExact (x n - d)).mp (by simp [hd])
  refine ⟨y, ?_⟩
  simpa [hy] using (Submodule.neg_mem _ hdmem)

/-- A small change of a lift, not necessarily the difference of two chosen lifts. -/
private noncomputable def exactLiftDelta
    (e : ℕ → ℕ) (he : ∀ n, e n ≤ e (n + 1))
    (hcofinal : ∀ n, f.range ⊓ (I ^ e n • ⊤ : Submodule R N) ≤ I ^ n • f.range)
    (x : AdicCauchySequence I N) {n : ℕ} {y p : P}
    (hy : f y - x (e (n + 1)) ∈ (I ^ e (n + 1) • ⊤ : Submodule R N))
    (hp : f p - x (e n) ∈ (I ^ e n • ⊤ : Submodule R N)) :
    {δ : (I ^ n • ⊤ : Submodule R P) |
      f (p + δ) - x (e (n + 1)) ∈ (I ^ e (n + 1) • ⊤ : Submodule R N)} := by
  have hx : x (e (n + 1)) - x (e n) ∈ (I ^ e n • ⊤ : Submodule R N) := by
    rw [← Submodule.Quotient.eq]
    exact AdicCauchySequence.mk_eq_mk (he n) x
  have hy' : f y - x (e (n + 1)) ∈ (I ^ e n • ⊤ : Submodule R N) :=
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (he n))) hy
  have hdiff : f (y - p) ∈ (I ^ e n • ⊤ : Submodule R N) := by
    rw [map_sub]
    convert Submodule.sub_mem _ (Submodule.add_mem _ hy' hx) hp using 1 ; abel
  have hmem : f (y - p) ∈ Submodule.map f (I ^ n • ⊤ : Submodule R P) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact hcofinal n ⟨⟨y - p, rfl⟩, hdiff⟩
  refine ⟨⟨hmem.choose, hmem.choose_spec.1⟩, ?_⟩
  have hδ : f hmem.choose = f (y - p) := hmem.choose_spec.2
  have hfy : f (p + hmem.choose) = f y := by
    rw [map_add, hδ, map_sub]
    abel
  change f (p + hmem.choose) - x (e (n + 1)) ∈
    (I ^ e (n + 1) • ⊤ : Submodule R N)
  simpa only [hfy] using hy

/-- Successive approximations whose changes have the prescribed intrinsic precision. -/
private noncomputable def exactLift
    (hExact : Function.Exact f g) (hg : Function.Surjective g)
    (e : ℕ → ℕ) (he : ∀ n, e n ≤ e (n + 1))
    (hcofinal : ∀ n, f.range ⊓ (I ^ e n • ⊤ : Submodule R N) ≤ I ^ n • f.range)
    (x : AdicCauchySequence I N)
    (hker : ∀ n : ℕ, g (x n) ∈ (I ^ n • ⊤ : Submodule R M)) :
    (n : ℕ) → {p : P | f p - x (e n) ∈ (I ^ e n • ⊤ : Submodule R N)}
  | .zero =>
      let h := exists_exact_approximation hExact hg x hker (e 0)
      ⟨h.choose, h.choose_spec⟩
  | .succ n =>
      let h := exists_exact_approximation hExact hg x hker (e (n + 1))
      let p := exactLift hExact hg e he hcofinal x hker n
      let δ := exactLiftDelta e he hcofinal x h.choose_spec p.property
      ⟨(p : P) + (δ.val : P), δ.property⟩

/-- Adic completion preserves middle exactness if the induced adic filtration on
`f.range` is cofinal with the intrinsic filtration `I ^ k • f.range`.

This generalizes Mathlib's `AdicCompletion.map_exact`: range cofinality replaces
its Noetherian and finiteness assumptions, and the first map need not be injective.
Cofinality ensures that successive lifts can be corrected by intrinsically small
elements; it is not an intrinsic completeness assumption on the completed modules. -/
theorem map_exact_of_range_cofinal
    (hExact : Function.Exact f g) (hg : Function.Surjective g)
    (hcofinal : ∀ k : ℕ, ∃ l : ℕ,
      f.range ⊓ (I ^ l • ⊤ : Submodule R N) ≤ I ^ k • f.range) :
    Function.Exact (map I f) (map I g) := by
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ (fun z ↦ ?_)
  · rw [map_comp, hExact.linearMap_comp_eq_zero, AdicCompletion.map_zero]
  · apply AdicCompletion.induction_on I N z (fun b ↦ ?_)
    intro hz
    obtain ⟨e, he_bound, he_step, he_cofinal⟩ := exists_cofinal_indices hcofinal
    have hb (n : ℕ) : g (b n) ∈ (I ^ n • ⊤ : Submodule R M) := by
      simpa using congrArg (fun z ↦ z.val n) hz
    let a := exactLift hExact hg e he_step he_cofinal b hb
    refine ⟨AdicCompletion.mk I P (AdicCauchySequence.mk I P (fun n ↦ (a n : P)) ?_), ?_⟩
    · intro n
      apply SModEq.symm
      simp [a, exactLift, SModEq]
    · ext n
      suffices h : Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (f (a n)) =
          Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (b (e n)) by
        simp [h, AdicCauchySequence.mk_eq_mk (he_bound n)]
      rw [Submodule.Quotient.eq]
      exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (he_bound n))) (a n).property

/-- Adic completion preserves middle exactness of a right-surjective exact pair
whose original middle module is Noetherian over the original scalar ring.

The ideal and original first source are arbitrary; the first map need not be
injective. All completed maps and actions are the canonical ones. No
Noetherianity of the original ring, finite generation of the ideal, source
finiteness, flatness, faithfulness, separation or completeness is assumed.

This generalizes Mathlib's `AdicCompletion.map_exact`, formalized by Judith
Ludwig and Christian Merten, using module Artin–Rees and the range-cofinality
criterion. -/
theorem map_exact_of_isNoetherian_middle
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    {P : Type uP} [AddCommGroup P] [Module R P]
    [IsNoetherian R N]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hExact : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) := by
  apply map_exact_of_range_cofinal hExact hg
  intro k
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul_of_isNoetherian I f.range
  refine ⟨k + c, ?_⟩
  rw [inf_comm, hc (k + c) (Nat.le_add_left c k), Nat.add_sub_cancel]
  exact smul_mono_right _ inf_le_right

end AdicCompletion
