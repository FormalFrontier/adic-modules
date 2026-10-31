/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.LinearAlgebra.Quotient.Coefficients
public import AdicModules.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherian ideal-power quotients of modules

For an ideal `I` of a commutative ring and any module `M`, the quotient
`M / Iⁿ M`, for each `n ≥ 2`, is Noetherian if and only if `M / I M` is
Noetherian and the image of `I M` in `M / I² M` is finitely generated.
All Noetherianity and finite generation in the statement are over the
original ring. There is no Noetherian coefficient-ring hypothesis, and
neither `I` nor `M` is required to be finitely generated.

The finitely generated image supplies one finite coefficient ideal `J ≤ I`
with `J M + I² M = I M`. Propagation of this equality identifies each
original increment with the image of finitely many copies of `M / I M`.
Thus the increments are Noetherian by a surjection from a Noetherian module,
not merely because of finite generation. The result follows by exact
extensions along the original precision maps.

## Canonical quotient coefficients

The stock `R / I^q`-module action on `M / I^q M` agrees with its original
`R`-action along the quotient map, as expressed by
`Module.Quotient.mk_smul_mk`. The identity semilinear map
`(Module.isTorsionBySet_quotient_ideal_smul M (I ^ q)).semilinearMap`, together
with `LinearMap.isNoetherian_iff_of_bijective`, therefore identifies
`IsNoetherian R (M / I^q M)` with `IsNoetherian (R / I^q) (M / I^q M)`.
This is module Noetherianity, not Noetherianity of the quotient ring.
No alternate quotient or scalar action is used here.

## References

The finite scalar-cover argument and acted power propagation are reused from
the Formal Frontier Agents formalization in
`AdicModules.LinearAlgebra.Quotient.Coefficients` and
`AdicModules.RingTheory.Ideal.Operations`. The finite coefficient sum and its
coverage are `LinearMap.coefficientMap` and
`LinearMap.moduleSpan_le_range_coefficientMap`.

The proof uses Mathlib's quotient-map formalization by Johannes Hölzl,
Mario Carneiro, Kevin Buzzard and Yury Kudryashov, and its Noetherian-module
formalization by Mario Carneiro, Kevin Buzzard and María Inés de
Frutos-Fernández, in `Mathlib.RingTheory.Noetherian.Basic`.
-/

@[expose] public section

universe u v

namespace Submodule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Each original increment is a quotient of finitely many copies of `M / I M`.
The coefficient maps descend because their scalars lie in `I^q`. -/
private theorem isNoetherian_map_pow_smul_top_of_fg
    (I J : Ideal R) (hJ : J.FG) (hJI : J ≤ I)
    (h : J • (⊤ : Submodule R M) ⊔ I ^ 2 • (⊤ : Submodule R M) =
      I • (⊤ : Submodule R M))
    [IsNoetherian R (M ⧸ (I • (⊤ : Submodule R M)))] (q : ℕ) :
    IsNoetherian R ((I ^ q • (⊤ : Submodule R M)).map
      (I ^ (q + 1) • (⊤ : Submodule R M)).mkQ) := by
  classical
  obtain ⟨s, hs⟩ := hJ.pow (n := q)
  have hcoeff (a : s) : (a : R) ∈ I ^ q := by
    apply Ideal.pow_right_mono hJI q
    rw [← hs]
    exact subset_span a.property
  have hkill (a : s) : I • (⊤ : Submodule R M) ≤
      LinearMap.ker ((I ^ (q + 1) • (⊤ : Submodule R M)).mkQ.comp
        ((a : R) • (LinearMap.id : M →ₗ[R] M))) := by
    rw [← Ideal.moduleSpan_eq_smul_top]
    apply Ideal.moduleSpan_le.mpr
    intro b hb m
    change (I ^ (q + 1) • (⊤ : Submodule R M)).mkQ
      ((a : R) • (b • m)) = 0
    rw [smul_smul]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply smul_mem_smul _ (mem_top : m ∈ (⊤ : Submodule R M))
    rw [pow_succ]
    exact Ideal.mul_mem_mul (hcoeff a) hb
  let g (a : s) : (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R]
      M ⧸ (I ^ (q + 1) • (⊤ : Submodule R M)) :=
    (I • (⊤ : Submodule R M)).liftQ
      ((I ^ (q + 1) • (⊤ : Submodule R M)).mkQ.comp
        ((a : R) • (LinearMap.id : M →ₗ[R] M))) (hkill a)
  let f : (s → M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R]
      M ⧸ (I ^ (q + 1) • (⊤ : Submodule R M)) :=
    ∑ a : s, (g a).comp (LinearMap.proj a)
  have hcompat (m : s → M) :
      f (fun a => (I • (⊤ : Submodule R M)).mkQ (m a)) =
        (I ^ (q + 1) • (⊤ : Submodule R M)).mkQ
          (LinearMap.coefficientMap s m) := by
    simp [f, g, LinearMap.coefficientMap, map_sum]
  have hcover : J ^ q • (⊤ : Submodule R M) ≤
      LinearMap.range (LinearMap.coefficientMap (N := M) s) := by
    rw [← Ideal.moduleSpan_eq_smul_top, ← hs]
    exact LinearMap.moduleSpan_le_range_coefficientMap s
  have hlayer : (I ^ q • (⊤ : Submodule R M)).map
      (I ^ (q + 1) • (⊤ : Submodule R M)).mkQ =
      (J ^ q • (⊤ : Submodule R M)).map
        (I ^ (q + 1) • (⊤ : Submodule R M)).mkQ := by
    rw [← pow_smul_sup_next_eq_of_smul_sup_sq_eq I J ⊤ h q,
      map_sup, mkQ_map_self, sup_bot_eq]
  have hrange : LinearMap.range f = (I ^ q • (⊤ : Submodule R M)).map
      (I ^ (q + 1) • (⊤ : Submodule R M)).mkQ := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      choose m hm using fun a : s => (I • (⊤ : Submodule R M)).mkQ_surjective (v a)
      have hv : (fun a => (I • (⊤ : Submodule R M)).mkQ (m a)) = v := funext hm
      rw [← hv, hcompat]
      apply mem_map_of_mem
      exact Submodule.sum_mem _ fun a _ => smul_mem_smul (hcoeff a) mem_top
    · rw [hlayer]
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨v, hv⟩ := hcover hm
      refine ⟨fun a => (I • (⊤ : Submodule R M)).mkQ (v a), ?_⟩
      rw [hcompat, hv]
  have : IsNoetherian R (LinearMap.range f) := inferInstance
  rw [hrange] at this
  exact this

/-- For each `n ≥ 2`, an original ideal-power quotient of an arbitrary module is
Noetherian exactly when its first quotient is Noetherian and its acted first
layer is finitely generated over the original ring. The proof uses finite
coefficient covers, acted power propagation and Mathlib's Noetherian exact-extension
API; it assumes neither Noetherian coefficients nor finite generation of `I` or `M`.
The stock quotient-coefficient action gives the equivalent `R / I^n` interpretation
described in the module documentation. -/
theorem isNoetherian_quotient_pow_smul_top_iff
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 2 ≤ n) :
    IsNoetherian R (M ⧸ (I ^ n • (⊤ : Submodule R M))) ↔
      IsNoetherian R (M ⧸ (I • (⊤ : Submodule R M))) ∧
        ((I • (⊤ : Submodule R M)).map
          (I ^ 2 • (⊤ : Submodule R M)).mkQ).FG := by
  have hn1 : 1 ≤ n := (by decide : 1 ≤ 2).trans hn
  -- Transport the whole quotient-module proposition, including its scalar dictionary.
  have hpowOne := congrArg (fun K : Ideal R =>
    IsNoetherian R (M ⧸ (K • (⊤ : Submodule R M)))) (pow_one I)
  constructor
  · intro hN
    let := hN
    have h1 : IsNoetherian R (M ⧸ (I ^ 1 • (⊤ : Submodule R M))) :=
      isNoetherian_of_surjective (factorPow I M hn1)
        (LinearMap.range_eq_top.mpr (factor_surjective _))
    have : IsNoetherian R (M ⧸ (I ^ 2 • (⊤ : Submodule R M))) :=
      isNoetherian_of_surjective (factorPow I M hn)
        (LinearMap.range_eq_top.mpr (factor_surjective _))
    exact ⟨hpowOne.mp h1, IsNoetherian.noetherian _⟩
  · rintro ⟨h1, hF⟩
    let := h1
    obtain ⟨J, hJ, hJI, hacted⟩ :=
      I.exists_fg_subideal_smul_sup_eq_of_fg_map_mkQ
        (I ^ 2 • (⊤ : Submodule R M)) hF
    have hsq : I ^ 2 • (⊤ : Submodule R M) ≤ I • (⊤ : Submodule R M) :=
      smul_mono_left (Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0))
    rw [sup_eq_left.mpr hsq] at hacted
    have hquot (q : ℕ) : IsNoetherian R
        (M ⧸ (I ^ (q + 1) • (⊤ : Submodule R M))) := by
      induction q with
      | zero => exact hpowOne.mpr h1
      | succ q ih =>
        let := ih
        have := isNoetherian_map_pow_smul_top_of_fg I J hJ hJI hacted (q + 1)
        apply isNoetherian_of_range_eq_ker
          ((I ^ (q + 1) • (⊤ : Submodule R M)).map
            (I ^ ((q + 1) + 1) • (⊤ : Submodule R M)).mkQ).subtype
          (factorPowSucc I M (q + 1))
        simp only [Submodule.range_subtype, factorPowSucc, factorPow, factor,
          ker_mapQ, comap_id]
    exact (congrArg (fun q : ℕ =>
      IsNoetherian R (M ⧸ (I ^ q • (⊤ : Submodule R M))))
      (Nat.sub_add_cancel hn1)).mp (hquot (n - 1))

end Submodule
