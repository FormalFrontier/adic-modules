/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.AdicCompletion.Exactness

/-!
# Completing a submodule quotient with an arbitrary extra source

For a submodule `K` of a Noetherian original module `N`, compose the projection
`X × K → K` with the inclusion into `N`. Completion identifies the image of this
map with the kernel of the canonical completed quotient map. The extra module
`X` is arbitrary: no Noetherianity or finiteness of `X` is assumed, and the first
map kills the entire `X` factor, so it need not be injective.

Original exactness follows from Mathlib's submodule-quotient exact pair and its
invariance under precomposition by a surjective linear map.
-/

universe uR uN uX

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
