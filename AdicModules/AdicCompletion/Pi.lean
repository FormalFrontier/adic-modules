/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.LinearAlgebra.Pi

/-!
# Naturality of the product comparison for adic completion

The comparison `AdicCompletion.pi` commutes with the maps on completions induced by
componentwise linear maps between dependent products. The square is an equality of
linear maps over the completed ring, for every ideal and arbitrary indexing types.

## References

This file uses Mathlib's completion functor and product comparison, formalized by
Judith Ludwig and Christian Merten in
`Mathlib.RingTheory.AdicCompletion.Functoriality`, and Mathlib's dependent-product
linear map and projection API in `Mathlib.LinearAlgebra.Pi`.
-/

@[expose] public section

set_option warningAsError true

universe uR uJ uM uN

namespace AdicCompletion

variable {R : Type uR} [CommRing R] (I : Ideal R)
  {J : Type uJ} {M : J → Type uM} {N : J → Type uN}
  [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
  [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]

/-- The product comparison for adic completion is natural in componentwise linear maps.
This is an equality of linear maps over the completed ring, without finiteness
assumptions on the ideal or indexing type. -/
theorem pi_comp_map (f : ∀ j, M j →ₗ[R] N j) :
    pi I N ∘ₗ map I (LinearMap.piMap f) =
      LinearMap.piMap (fun j ↦ map I (f j)) ∘ₗ pi I M := by
  simp only [pi, LinearMap.piMap, LinearMap.pi_comp, LinearMap.comp_assoc,
    LinearMap.proj_pi, map_comp]

/-- Applying the product comparison after a componentwise map on completions amounts
to applying the induced map to each completed component. -/
@[simp]
theorem pi_map (f : ∀ j, M j →ₗ[R] N j) (x : AdicCompletion I (∀ j, M j)) :
    pi I N (map I (LinearMap.piMap f) x) =
      fun j ↦ map I (f j) (pi I M x j) :=
  LinearMap.congr_fun (pi_comp_map I f) x

end AdicCompletion
