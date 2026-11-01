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
import CoherentModules.RingTheory.Filtration

/-!
# Images, injectivity and exactness of adic completion

Pointwise cofinality of the induced and intrinsic ideal-power filtrations makes
completion of a submodule inclusion injective, by
`map_subtype_injective_of_cofinal` in `AdicModules.AdicCompletion.LinearMap`.
For every ideal, module Artin–Rees supplies this cofinality for a Noetherian
original target. Thus completion preserves injectivity of an original linear map
with such a target. The original ring need not be Noetherian, and the ring,
source and target universes are independent.

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

If the induced ideal-power filtration on each of the two original ranges is
pointwise cofinal with its intrinsic filtration, `map_exact_of_ranges_cofinal`
preserves middle exactness without injectivity or surjectivity of either map.
No finiteness or Noetherian hypothesis is required, and all four universes are
independent. If both the original middle and target modules are Noetherian over
the original ring, module Artin–Rees supplies the two bounds. The original first
source remains arbitrary.

For an original map `g : N →ₗ[R] P` between Noetherian original modules,
`kerEquivOfIsNoetherian` identifies intrinsic completion of its original kernel
with the kernel of `map I g`, linearly over `AdicCompletion I R`. Its forward map
is the completed original kernel inclusion. The inverse is characterized by its
ambient inclusion equation and gives the kernel universal property for maps from
arbitrary modules over the completed ring. The comparison agrees with
`kerEquivOfRightInverse` whenever original split data are also supplied.

For a right-surjective original exact pair, cofinality on the first range alone
suffices for middle exactness. Neither injectivity of the first map nor finiteness
or Noetherian hypotheses are required for this range-cofinality criterion.

## Implementation notes

For injectivity, module Artin–Rees supplies the pointwise cofinality bound for
the original range in its Noetherian ambient target. The subtype criterion gives
injectivity of the completed range inclusion. Completion of
`LinearEquiv.ofInjective` identifies the original source completion with completion
of that original range; functoriality recovers the canonical completed map.

The image equivalence uses this injectivity criterion only for the original range
inclusion. The unconditional `range_map_range_subtype` gives its range and hence
surjectivity of its codomain restriction. Mathlib's `LinearEquiv.ofBijective`
then supplies the equivalence and its choice-based inverse; no quotient of the
completed source or new completed-map construction is involved. The resulting
Noetherian-target comparison agrees as a whole equivalence with
`rangeEquivOfRangeCofinal` for every proof of the pointwise cofinality bound.

The range-cofinality proof uses the existing Cauchy-sequence and completion maps.
At each step, cofinality allows a change of a chosen lift by an element in the
required ideal power. The change need not equal the difference of the original lifts, so the
first map need not be injective. No intrinsic adic completeness of a completion
is assumed.

For a possibly nonsurjective last map, factor it through its original range.
The right-surjective criterion uses cofinality on the first range, and the subtype
injectivity criterion uses the separate bound on the second range. Mathlib's
exactness-under-injective-postcomposition and completion-functoriality APIs then
recover the canonical completed pair. For Noetherian original middle and target
modules, module Artin–Rees supplies the two bounds separately, without imposing
a quotient scalar action on the first source.

The kernel comparison completes the ambient-element-preserving equivalence
between the original kernel and the range of its inclusion, then composes the
existing original-image equivalence with the range-to-kernel equality supplied
by Noetherian-pair exactness. Only stock equivalence composition and submodule
transport are used; no new comparison map or kernel-lift construction is needed.

## References

The construction follows the Cauchy-sequence proof of `AdicCompletion.map_exact`
by Judith Ludwig and Christian Merten in
`Mathlib.RingTheory.AdicCompletion.Exactness`. Pointwise range cofinality replaces
its Artin–Rees bound, and chosen small changes replace its use of injectivity.
The Noetherian-target injectivity criterion uses the pointwise subtype criterion
from `AdicModules.AdicCompletion.LinearMap`, completion functoriality and Mathlib's
`LinearEquiv.ofInjective`. Its cofinality bound comes from CoherentModules' module
Artin–Rees theorem, generalizing Andrew Yang's formalization in
`Mathlib.RingTheory.Filtration`. The image comparison also uses Ludwig and Merten's
all-ideal completion-surjectivity theorem and Mathlib's generic range,
codomain-restriction and linear-equivalence APIs.

The Noetherian-middle criterion uses CoherentModules' module Artin–Rees theorem,
which generalizes Andrew Yang's formalization in `Mathlib.RingTheory.Filtration`.
The two-range criterion also uses Mathlib's original range factorization,
the pointwise subtype criterion from `AdicModules.AdicCompletion.LinearMap`,
and Antoine Chambert-Loir's exactness-under-injective-postcomposition API in
`Mathlib.Algebra.Exact.Basic`. Module Artin–Rees supplies both bounds for the
Noetherian-pair specialization.

The original-kernel comparison also reuses the original-image comparison above
and Mathlib's submodule linear equivalences and codomain restrictions, with the
canonical completed-module actions.
-/

@[expose] public section

universe uR uP uN uM

namespace AdicCompletion

open LinearMap

/-- Completion preserves injectivity of a linear map whose original target is
Noetherian over the original ring, for every ideal. No Noetherianity of the original
ring, finite generation of the ideal, source finiteness, flatness, separation or
completeness is assumed.

This generalizes Mathlib's `AdicCompletion.map_injective`, formalized by Judith Ludwig
and Christian Merten, to arbitrary original rings and independent ring, source and
target universes. Module Artin–Rees supplies pointwise cofinality for the original
range inclusion, and completion of `LinearEquiv.ofInjective` gives the result for
the original map. -/
theorem map_injective_of_isNoetherian_target
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    [IsNoetherian R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (AdicCompletion.map I f) := by
  have hcofinal : ∀ n : ℕ, ∃ m : ℕ,
      f.range ⊓ (I ^ m • (⊤ : Submodule R N)) ≤ I ^ n • f.range := by
    intro n
    obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul_of_isNoetherian I f.range
    refine ⟨n + c, ?_⟩
    rw [inf_comm, hc (n + c) (Nat.le_add_left c n), Nat.add_sub_cancel]
    exact smul_mono_right _ inf_le_right
  have hfactor : (map I f.range.subtype).comp
      (congr I (LinearEquiv.ofInjective f hf)).toLinearMap = map I f := by
    have h : f.range.subtype.comp (LinearEquiv.ofInjective f hf).toLinearMap = f := by
      ext x
      exact LinearEquiv.ofInjective_apply f (h := hf) x
    change (map I f.range.subtype).comp
      (map I (LinearEquiv.ofInjective f hf).toLinearMap) = map I f
    rw [map_comp, h]
  rw [← hfactor]
  exact (map_subtype_injective_of_cofinal I f.range hcofinal).comp
    (congr I (LinearEquiv.ofInjective f hf)).injective

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

/-- The Noetherian-target image comparison agrees with the pointwise-cofinal
comparison for any proof of the induced-filtration bound. -/
theorem rangeEquivOfIsNoetherianTarget_eq_rangeEquivOfRangeCofinal
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {P : Type uP} [AddCommGroup P] [Module R P]
    [IsNoetherian R P] (f : M →ₗ[R] P)
    (hcofinal : ∀ n : ℕ, ∃ m : ℕ,
      f.range ⊓ (I ^ m • (⊤ : Submodule R P)) ≤ I ^ n • f.range) :
    rangeEquivOfIsNoetherianTarget I f =
      rangeEquivOfRangeCofinal I f hcofinal := by
  apply LinearEquiv.ext
  intro z
  apply Subtype.ext
  rw [coe_rangeEquivOfIsNoetherianTarget_apply, coe_rangeEquivOfRangeCofinal_apply]

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

/-- Adic completion preserves middle exactness when the induced ideal-power
filtrations on both original ranges are pointwise cofinal with their intrinsic
adic filtrations.

The two bounds are independent. Neither map needs to be injective or surjective,
and no finiteness, Noetherianity, flatness, separation or completeness hypothesis
is required. The ring and all three module universes are independent; the completed
maps and actions are the canonical ones.

This extends `map_exact_of_range_cofinal`, which follows Judith Ludwig and
Christian Merten's Cauchy-sequence proof, by factoring the last original map
through its range and using injectivity of the completed range inclusion. -/
theorem map_exact_of_ranges_cofinal
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    {P : Type uP} [AddCommGroup P] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hExact : Function.Exact f g)
    (hfcofinal : ∀ n : ℕ, ∃ m : ℕ,
      f.range ⊓ (I ^ m • (⊤ : Submodule R N)) ≤ I ^ n • f.range)
    (hgcofinal : ∀ n : ℕ, ∃ m : ℕ,
      g.range ⊓ (I ^ m • (⊤ : Submodule R P)) ≤ I ^ n • g.range) :
    Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) := by
  have hExactQ : Function.Exact f g.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    exact hExact.linearMap_ker_eq
  have hCompleted : Function.Exact (map I f) (map I g.rangeRestrict) :=
    map_exact_of_range_cofinal hExactQ (LinearMap.surjective_rangeRestrict g) hfcofinal
  have hi : Function.Injective (map I g.range.subtype) :=
    map_subtype_injective_of_cofinal I g.range hgcofinal
  simpa only [← LinearMap.coe_comp, map_comp, LinearMap.subtype_comp_rangeRestrict] using
    hCompleted.comp_injective (map I g.range.subtype) hi (_root_.map_zero _)

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

/-- Adic completion preserves middle exactness of a pair whose original middle
and target modules are Noetherian over the original scalar ring.

The ideal and original first source are arbitrary; the first map need not be
injective and the last map need not be surjective. All completed maps and actions
are the canonical ones. No Noetherianity of the original ring, finite generation
of the ideal, source finiteness, flatness, faithfulness, separation or completeness
is assumed.

This extends the middle-exactness result of Mathlib's `AdicCompletion.map_exact`,
formalized by Judith Ludwig and Christian Merten. Module Artin–Rees supplies both
bounds for `map_exact_of_ranges_cofinal`. -/
theorem map_exact_of_isNoetherian
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    {P : Type uP} [AddCommGroup P] [Module R P]
    [IsNoetherian R N] [IsNoetherian R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hExact : Function.Exact f g) :
    Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) := by
  apply map_exact_of_ranges_cofinal I hExact
  · intro n
    obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul_of_isNoetherian I f.range
    refine ⟨n + c, ?_⟩
    rw [inf_comm, hc (n + c) (Nat.le_add_left c n), Nat.add_sub_cancel]
    exact smul_mono_right _ inf_le_right
  · intro n
    obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul_of_isNoetherian I g.range
    refine ⟨n + c, ?_⟩
    rw [inf_comm, hc (n + c) (Nat.le_add_left c n), Nat.add_sub_cancel]
    exact smul_mono_right _ inf_le_right

/-- Completion of the original kernel is the kernel of the completed map when
both original modules are Noetherian over the original coefficient ring.
The forward map is completion of the original kernel inclusion. -/
noncomputable def kerEquivOfIsNoetherian
    {R : Type uR} [CommRing R] (I : Ideal R)
    {N : Type uN} [AddCommGroup N] [Module R N]
    {P : Type uP} [AddCommGroup P] [Module R P]
    [IsNoetherian R N] [IsNoetherian R P]
    (g : N →ₗ[R] P) :
    AdicCompletion I (LinearMap.ker g) ≃ₗ[AdicCompletion I R]
      LinearMap.ker (AdicCompletion.map I g) := by
  let K := LinearMap.ker g
  let s := K.subtype
  let eK := LinearEquiv.ofEq K (LinearMap.range s) (Submodule.range_subtype K).symm
  let J := map I s
  let L := LinearMap.ker (map I g)
  have hRange : LinearMap.range J = L :=
    (map_exact_of_isNoetherian I (LinearMap.exact_subtype_ker_map g)).linearMap_ker_eq.symm
  exact (congr I eK).trans
    ((rangeEquivOfIsNoetherianTarget I s).trans
      (LinearEquiv.ofEq (LinearMap.range J) L hRange))

section KerEquiv

variable (I : Ideal R) [IsNoetherian R N] [IsNoetherian R P] (g : N →ₗ[R] P)

/-- The whole ambient forward map is completion of the original kernel inclusion. -/
theorem subtype_comp_kerEquivOfIsNoetherian :
    (LinearMap.ker (map I g)).subtype.comp (kerEquivOfIsNoetherian I g).toLinearMap =
      map I (LinearMap.ker g).subtype := by
  let K := LinearMap.ker g
  let eK := LinearEquiv.ofEq K (LinearMap.range K.subtype)
    (Submodule.range_subtype K).symm
  have hs : (LinearMap.range K.subtype).subtype.comp eK.toLinearMap = K.subtype := by
    apply LinearMap.ext
    intro k
    rfl
  apply LinearMap.ext
  intro z
  change (kerEquivOfIsNoetherian I g z : AdicCompletion I N) =
    map I (LinearMap.ker g).subtype z
  simpa only [kerEquivOfIsNoetherian, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, coe_rangeEquivOfIsNoetherianTarget_apply,
    congr_apply, map_comp_apply] using
      congrArg (fun t : K →ₗ[R] N ↦ map I t z) hs

/-- Coercing any completed original-kernel element gives its completed inclusion. -/
@[simp]
theorem coe_kerEquivOfIsNoetherian_apply (z : AdicCompletion I (LinearMap.ker g)) :
    (kerEquivOfIsNoetherian I g z : AdicCompletion I N) =
      map I (LinearMap.ker g).subtype z :=
  LinearMap.congr_fun (subtype_comp_kerEquivOfIsNoetherian I g) z

/-- The forward map is the codomain restriction of the completed kernel inclusion,
independently of the proof of kernel membership. -/
theorem kerEquivOfIsNoetherian_toLinearMap_eq_codRestrict
    (hmem : ∀ z : AdicCompletion I (LinearMap.ker g),
      map I (LinearMap.ker g).subtype z ∈ LinearMap.ker (map I g)) :
    (kerEquivOfIsNoetherian I g).toLinearMap =
      (map I (LinearMap.ker g).subtype).codRestrict (LinearMap.ker (map I g)) hmem := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact coe_kerEquivOfIsNoetherian_apply I g z

/-- An original kernel element maps to its canonical image in the ambient completion. -/
theorem coe_kerEquivOfIsNoetherian_of (k : LinearMap.ker g) :
    (kerEquivOfIsNoetherian I g (of I (LinearMap.ker g) k) : AdicCompletion I N) =
      of I N (k : N) := by
  rw [coe_kerEquivOfIsNoetherian_apply, map_of]
  rfl

/-- The inverse sends a completed-map kernel element to its unique completed
original-kernel preimage under the completed inclusion. -/
@[simp]
theorem map_ker_subtype_kerEquivOfIsNoetherian_symm_apply
    (y : LinearMap.ker (map I g)) :
    map I (LinearMap.ker g).subtype ((kerEquivOfIsNoetherian I g).symm y) =
      (y : AdicCompletion I N) := by
  rw [← coe_kerEquivOfIsNoetherian_apply, LinearEquiv.apply_symm_apply]

/-- The inverse recovers every completed original-kernel element from its
completed inclusion. Kernel membership follows from completion functoriality. -/
@[simp]
theorem kerEquivOfIsNoetherian_symm_apply_map_ker_subtype
    (z : AdicCompletion I (LinearMap.ker g)) :
    (kerEquivOfIsNoetherian I g).symm
      ⟨map I (LinearMap.ker g).subtype z, by
        have hzero : (map I g).comp (map I (LinearMap.ker g).subtype) = 0 := by
          rw [map_comp, LinearMap.comp_ker_subtype, AdicCompletion.map_zero]
        exact LinearMap.mem_ker.mpr (LinearMap.congr_fun hzero z)⟩ = z := by
  apply (kerEquivOfIsNoetherian I g).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (coe_kerEquivOfIsNoetherian_apply I g z).symm

/-- The whole inverse map is a right inverse to the completed kernel inclusion
on the completed-map kernel. -/
theorem map_ker_subtype_comp_kerEquivOfIsNoetherian_symm :
    (map I (LinearMap.ker g).subtype).comp (kerEquivOfIsNoetherian I g).symm.toLinearMap =
      (LinearMap.ker (map I g)).subtype := by
  apply LinearMap.ext
  intro y
  exact map_ker_subtype_kerEquivOfIsNoetherian_symm_apply I g y

/-- The inverse is uniquely characterized by its whole ambient inclusion equation. -/
theorem kerEquivOfIsNoetherian_symm_toLinearMap_eq_iff
    (v : LinearMap.ker (map I g) →ₗ[AdicCompletion I R]
      AdicCompletion I (LinearMap.ker g)) :
    v = (kerEquivOfIsNoetherian I g).symm.toLinearMap ↔
      (map I (LinearMap.ker g).subtype).comp v = (LinearMap.ker (map I g)).subtype := by
  constructor
  · rintro rfl
    exact map_ker_subtype_comp_kerEquivOfIsNoetherian_symm I g
  · intro hv
    apply LinearMap.ext
    intro y
    apply (kerEquivOfIsNoetherian I g).injective
    apply Subtype.ext
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      coe_kerEquivOfIsNoetherian_apply]
    exact LinearMap.congr_fun hv y

/-- The inverse recovers the canonical completed class of an original kernel element. -/
theorem kerEquivOfIsNoetherian_symm_of (k : LinearMap.ker g) :
    (kerEquivOfIsNoetherian I g).symm
      ⟨of I N (k : N), by
        rw [LinearMap.mem_ker, map_of, LinearMap.mem_ker.mp k.property, _root_.map_zero]⟩ =
      of I (LinearMap.ker g) k := by
  apply (kerEquivOfIsNoetherian I g).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (coe_kerEquivOfIsNoetherian_of I g k).symm

/-- On an original split surjection, the Noetherian-kernel comparison agrees
with the split-kernel comparison as a whole linear equivalence. -/
theorem kerEquivOfIsNoetherian_eq_kerEquivOfRightInverse
    (r : P →ₗ[R] N) (h : g.comp r = LinearMap.id) :
    kerEquivOfIsNoetherian I g = kerEquivOfRightInverse I g r h := by
  apply LinearEquiv.ext
  intro z
  apply Subtype.ext
  rw [coe_kerEquivOfIsNoetherian_apply, coe_kerEquivOfRightInverse_apply]

universe uX

/-- Every completed-ring-linear map annihilated by the completed map factors
uniquely through completion of the original kernel. The factor is the inverse
kernel comparison composed with the stock codomain restriction. The source is
an arbitrary module over the completed ring. -/
theorem kerEquivOfIsNoetherian_existsUnique
    {X : Type uX} [AddCommMonoid X] [Module (AdicCompletion I R) X]
    (u : X →ₗ[AdicCompletion I R] AdicCompletion I N)
    (hu : (map I g).comp u = 0) :
    ∃! v : X →ₗ[AdicCompletion I R] AdicCompletion I (LinearMap.ker g),
      (map I (LinearMap.ker g).subtype).comp v = u := by
  have hmem : ∀ x, u x ∈ LinearMap.ker (map I g) :=
    fun x ↦ LinearMap.mem_ker.mpr (LinearMap.congr_fun hu x)
  refine ⟨(kerEquivOfIsNoetherian I g).symm.toLinearMap.comp
    (u.codRestrict (LinearMap.ker (map I g)) hmem), ?_, ?_⟩
  · change (map I (LinearMap.ker g).subtype).comp
        ((kerEquivOfIsNoetherian I g).symm.toLinearMap.comp
          (u.codRestrict (LinearMap.ker (map I g)) hmem)) = u
    rw [← LinearMap.comp_assoc, map_ker_subtype_comp_kerEquivOfIsNoetherian_symm,
      LinearMap.subtype_comp_codRestrict]
  · intro v hv
    apply LinearMap.ext
    intro x
    apply (kerEquivOfIsNoetherian I g).injective
    apply Subtype.ext
    calc
      (kerEquivOfIsNoetherian I g (v x) : AdicCompletion I N) =
          map I (LinearMap.ker g).subtype (v x) :=
        coe_kerEquivOfIsNoetherian_apply I g (v x)
      _ = u x := LinearMap.congr_fun hv x
      _ = (kerEquivOfIsNoetherian I g
          (((kerEquivOfIsNoetherian I g).symm.toLinearMap.comp
            (u.codRestrict (LinearMap.ker (map I g)) hmem)) x) : AdicCompletion I N) := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply]

end KerEquiv

end AdicCompletion
