/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Functor
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.LinearAlgebra.Prod

/-!
# Completed product inclusions

Adic completion carries the inclusion into the first factor of a product to a
monomorphism, by mapping its specified first-projection retraction. The linear map
on morphisms supplies this completed inclusion. For the bottom
ideal of the integers, this same completed inclusion sends the canonical image of
`1` to the nonzero canonical image of `(1, 0)`.

The completion maps and canonical images used here are the Mathlib APIs of
Judith Ludwig and Christian Merten.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AdicCompletion

open scoped ModuleCat.Algebra in
private theorem completed_inl_mono {R : Type u} [CommRing R] (I : Ideal R)
    (M N : Type v) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Mono (((functor I).mapLinearMap R) (ModuleCat.ofHom (LinearMap.inl R M N))) := by
  let splitting : SplitMono (ModuleCat.ofHom (LinearMap.inl R M N)) :=
    { retraction := ModuleCat.ofHom (LinearMap.fst R M N)
      id := by
        apply ModuleCat.hom_ext
        simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id] using
          (LinearMap.fst_comp_inl R M N) }
  exact (splitting.map (functor I)).mono

private theorem completed_inl_int_bot_boundary :
    ((functor (⊥ : Ideal ℤ)).map (ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ)))
        (of (⊥ : Ideal ℤ) ℤ 1) =
      of (⊥ : Ideal ℤ) (ℤ × ℤ) (1, 0) ∧
    ((functor (⊥ : Ideal ℤ)).map (ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ)))
        (of (⊥ : Ideal ℤ) ℤ 1) ≠ 0 := by
  have image :
      ((functor (⊥ : Ideal ℤ)).map (ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ)))
          (of (⊥ : Ideal ℤ) ℤ 1) =
        of (⊥ : Ideal ℤ) (ℤ × ℤ) (1, 0) := by
    rw [functor_map_apply, ModuleCat.hom_ofHom, map_of, LinearMap.inl_apply]
  refine ⟨image, ?_⟩
  rw [image]
  change of (⊥ : Ideal ℤ) (ℤ × ℤ) (1, 0) ≠
    (0 : AdicCompletion (⊥ : Ideal ℤ) (ℤ × ℤ))
  intro h
  have pair_eq_zero : (1, 0) = (0 : ℤ × ℤ) := by
    apply of_injective (⊥ : Ideal ℤ) (ℤ × ℤ)
    simpa only [_root_.map_zero] using h
  have one_eq_zero : (1 : ℤ) = 0 := congrArg Prod.fst pair_eq_zero
  exact one_ne_zero one_eq_zero

end AdicCompletion
