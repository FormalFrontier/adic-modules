/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Adic completion as a functor on modules

For an ideal `I` of a commutative ring `R`, `AdicCompletion.functor I` sends an
`R`-module to its `I`-adic completion, regarded as a module over `AdicCompletion I R`.
Its action on morphisms is Mathlib's `AdicCompletion.map`, with its natural linearity
over the completed coefficient ring. The functor is additive, and it is linear over
the original ring `R` using the relative linear structure on the target category.
The latter API uses the `ModuleCat.Algebra` scope. Mapped module isomorphisms agree
with `AdicCompletion.congr`.

The completion, its scalar structures, and the induced linear maps are supplied by
Mathlib's adic-completion development by Judith Ludwig and Christian Merten.
The categorical bundling reuses Mathlib's `ModuleCat` and linear-functor interfaces.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Adic completion of modules, with coefficients in the completed ring. -/
def functor : ModuleCat.{v} R ⥤ ModuleCat.{v} (AdicCompletion I R) where
  obj M := ModuleCat.of (AdicCompletion I R) (AdicCompletion I M)
  map f := ModuleCat.ofHom (AdicCompletion.map I f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    exact AdicCompletion.map_id I M
  map_comp {M N P} f g := by
    apply ModuleCat.hom_ext
    exact (AdicCompletion.map_comp I f.hom g.hom).symm

/-- The object assigned to a module is its completion over the completed ring. -/
theorem functor_obj (M : ModuleCat.{v} R) :
    (functor I).obj M = ModuleCat.of (AdicCompletion I R) (AdicCompletion I M) :=
  rfl

/-- The underlying linear map of a completed morphism is the induced map
on adic completions. -/
@[simp]
theorem functor_map_hom {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    ((functor I).map f).hom = AdicCompletion.map I f.hom :=
  rfl

/-- Evaluation of the functor's map agrees with the induced map on completions. -/
@[simp]
theorem functor_map_apply {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (x : AdicCompletion I M) :
    (functor I).map f x = AdicCompletion.map I f.hom x :=
  rfl

/-- Adic completion preserves addition of module morphisms. -/
instance functor_additive : (functor I).Additive where
  map_add {M N} {f g} := by
    apply ModuleCat.hom_ext
    change AdicCompletion.map I (f.hom + g.hom) =
      AdicCompletion.map I f.hom + AdicCompletion.map I g.hom
    exact (AdicCompletion.map I).map_add f.hom g.hom

end AdicCompletion

section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace AdicCompletion

universe u₁ v₁

variable {R : Type u₁} [CommRing R] (I : Ideal R)

/-- Adic completion is linear over the original coefficient ring, using the relative
linear structure on modules over the completed ring. -/
instance functor_linear :
    Functor.Linear R
      (AdicCompletion.functor I :
        ModuleCat.{v₁} R ⥤ ModuleCat.{v₁} (AdicCompletion I R)) where
  map_smul {M N} f r := by
    apply ModuleCat.hom_ext
    change AdicCompletion.map I (r • f.hom) =
      algebraMap R (AdicCompletion I R) r • AdicCompletion.map I f.hom
    refine LinearMap.ext fun (x : AdicCompletion I M) ↦ ?_
    calc
      AdicCompletion.map I (r • f.hom) x = r • AdicCompletion.map I f.hom x :=
        congrArg (fun g : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N ↦ g x)
          ((AdicCompletion.map I).map_smul r f.hom)
      _ = algebraMap R (AdicCompletion I R) r • AdicCompletion.map I f.hom x :=
        (IsScalarTower.algebraMap_smul (AdicCompletion I R) r
          (AdicCompletion.map I f.hom x)).symm

end AdicCompletion

end

section

universe u₂ v₂

open CategoryTheory

namespace AdicCompletion

variable {R : Type u₂} [CommRing R] (I : Ideal R)
variable {M N : ModuleCat.{v₂} R}

/-- Applying the adic-completion functor to a module isomorphism agrees with
its completed linear equivalence. -/
theorem functor_mapIso_toLinearEquiv (e : M ≅ N) :
    ((functor I).mapIso e).toLinearEquiv = congr I e.toLinearEquiv := by
  refine LinearEquiv.ext fun (x : AdicCompletion I M) ↦ ?_
  change AdicCompletion.map I e.hom.hom x =
    AdicCompletion.map I e.toLinearEquiv.toLinearMap x
  rw [CategoryTheory.Iso.toLinearMap_toLinearEquiv]

end AdicCompletion

end
