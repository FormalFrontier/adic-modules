/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.AdicCompletion.Exactness

/-!
# Kernels of completed quotient maps and arbitrary linear maps

For a submodule `K` of a Noetherian original module `N`, compose the projection
`X × K → K` with the inclusion into `N`. Completion identifies the image of this
map with the kernel of the canonical completed quotient map. The extra module
`X` is arbitrary: no Noetherianity or finiteness of `X` is assumed, and the first
map kills the entire `X` factor, so it need not be injective.

Original exactness follows from Mathlib's submodule-quotient exact pair and its
invariance under precomposition by a surjective linear map.

For any original linear map between Noetherian modules, the completed kernel
inclusion has image equal to the kernel of the completed map. No surjectivity
of the original or completed map is assumed. This uses Mathlib's original
kernel-inclusion exact pair.

The kernel comparison also intertwines completion of the original factorization
of a map through the kernel with the kernel restriction of the completed map,
on the whole completed first source, without Noetherianity of that source.
-/

universe uR uN uX uP

private theorem ker_completed_quotient_eq_range
    {R : Type uR} [CommRing R] (I : Ideal R)
    {N : Type uN} [AddCommGroup N] [Module R N] [IsNoetherian R N]
    (K : Submodule R N)
    {X : Type uX} [AddCommGroup X] [Module R X] :
    LinearMap.ker (AdicCompletion.map I K.mkQ) =
      LinearMap.range (AdicCompletion.map I (K.subtype.comp (LinearMap.snd R X K))) := by
  have hExact : Function.Exact (K.subtype.comp (LinearMap.snd R X K)) K.mkQ :=
    (Function.Surjective.comp_exact_iff_exact
      (LinearMap.snd_surjective (R := R) (M := X) (M₂ := K))).mpr
        (LinearMap.exact_subtype_mkQ K)
  exact (AdicCompletion.map_exact_of_isNoetherian_middle I hExact
    (Submodule.mkQ_surjective K)).linearMap_ker_eq

private theorem ker_completed_map_eq_range
    {R : Type uR} [CommRing R] (I : Ideal R)
    {N : Type uN} [AddCommGroup N] [Module R N] [IsNoetherian R N]
    {P : Type uP} [AddCommGroup P] [Module R P] [IsNoetherian R P]
    (g : N →ₗ[R] P) :
    LinearMap.ker (AdicCompletion.map I g) =
      LinearMap.range (AdicCompletion.map I (LinearMap.ker g).subtype) := by
  exact (AdicCompletion.map_exact_of_isNoetherian I
    (LinearMap.exact_subtype_ker_map g)).linearMap_ker_eq

universe uM

/-- Completing the original factorization through the kernel agrees, on the
whole completed source, with the kernel comparison. The original first
source is arbitrary and need not be Noetherian. -/
private theorem completed_original_kernel_factorization
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N] [IsNoetherian R N]
    {P : Type uP} [AddCommGroup P] [Module R P] [IsNoetherian R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hgf : g.comp f = 0) :
    (AdicCompletion.kerEquivOfIsNoetherian I g).toLinearMap.comp
        (AdicCompletion.map I (f.codRestrict (LinearMap.ker g)
          (fun m ↦ LinearMap.mem_ker.mpr (LinearMap.congr_fun hgf m)))) =
      (AdicCompletion.map I f).codRestrict (LinearMap.ker (AdicCompletion.map I g))
        (fun z ↦ LinearMap.mem_ker.mpr (by
          have hzero : (AdicCompletion.map I g).comp (AdicCompletion.map I f) = 0 := by
            rw [AdicCompletion.map_comp, hgf, AdicCompletion.map_zero]
          exact LinearMap.congr_fun hzero z)) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    AdicCompletion.coe_kerEquivOfIsNoetherian_apply, LinearMap.codRestrict_apply,
    AdicCompletion.map_comp_apply, LinearMap.subtype_comp_codRestrict]
