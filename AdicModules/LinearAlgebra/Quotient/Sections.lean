/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Sections of antitone quotient diagrams

An antitone family of submodules determines a diagram of quotient modules indexed by the
opposite preorder. The quotient projections assemble into `Submodule.toQuotientSections`,
whose kernel is the intersection of the family.

## Implementation notes

Compatible families use `ModuleCat.sectionsSubmodule` on the original dependent function
type. The scalar ring is unchanged, the index universe is independent, and the indexing
preorder may be empty. No smallness assumption is needed.

## References

* Mathlib, `Algebra/Category/ModuleCat/Limits`, `LinearAlgebra/Quotient/Basic` and
  `LinearAlgebra/Pi`: compatible families, quotient transitions and kernels of product maps.
-/

@[expose] public section

open CategoryTheory

universe uR uM uΛ

namespace Submodule

noncomputable section

variable {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module R M]
  {Λ : Type uΛ} [Preorder Λ] (F : Λ → Submodule R M) (hF : Antitone F)

/-- The diagram of quotients of an antitone family, with the canonical quotient factors
as transition maps. -/
def quotientDiagram : Λᵒᵖ ⥤ ModuleCat.{uM} R where
  obj i := ModuleCat.of R (M ⧸ F i.unop)
  map f := ModuleCat.ofHom (Submodule.factor (hF (leOfHom f.unop)))
  map_id i := by
    apply ModuleCat.hom_ext
    exact Submodule.mapQ_id (p := F i.unop)
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact (Submodule.factor_comp
      (hF (leOfHom f.unop)) (hF (leOfHom g.unop))).symm

@[simp]
theorem quotientDiagram_obj (i : Λᵒᵖ) :
    (quotientDiagram F hF).obj i = ModuleCat.of R (M ⧸ F i.unop) :=
  rfl

@[simp]
theorem quotientDiagram_map {i j : Λᵒᵖ} (f : i ⟶ j) :
    (quotientDiagram F hF).map f =
      ModuleCat.ofHom (Submodule.factor (hF (leOfHom f.unop))) :=
  rfl

/-- The quotient projections as a linear map to compatible families of quotient classes. -/
def toQuotientSections : M →ₗ[R] ModuleCat.sectionsSubmodule (quotientDiagram F hF) :=
  LinearMap.codRestrict (ModuleCat.sectionsSubmodule (quotientDiagram F hF))
    (LinearMap.pi (fun i : Λᵒᵖ => (F i.unop).mkQ)) (by
      intro x i μ f
      exact Submodule.factor_mk (hF (leOfHom f.unop)) x)

@[simp]
theorem toQuotientSections_apply (x : M) (i : Λᵒᵖ) :
    (toQuotientSections F hF x).val i = (F i.unop).mkQ x :=
  rfl

/-- The kernel of the map to quotient sections is the intersection of the submodules. -/
@[simp]
theorem ker_toQuotientSections :
    LinearMap.ker (toQuotientSections F hF) = ⨅ i, F i := by
  calc
    LinearMap.ker (toQuotientSections F hF) = ⨅ i : Λᵒᵖ, F i.unop := by
      simp only [toQuotientSections, LinearMap.ker_codRestrict]
      exact (LinearMap.ker_pi (fun i : Λᵒᵖ => (F i.unop).mkQ)).trans
        (iInf_congr fun i : Λᵒᵖ => ker_mkQ (F i.unop))
    _ = ⨅ i, F i :=
      le_antisymm
        (le_iInf fun i => iInf_le (fun j : Λᵒᵖ => F j.unop) (Opposite.op i))
        (le_iInf fun i => iInf_le F i.unop)

/-- An element maps to zero in the quotient sections exactly when it lies in every
submodule of the family. -/
@[simp]
theorem toQuotientSections_eq_zero_iff (x : M) :
    toQuotientSections F hF x = 0 ↔ ∀ i, x ∈ F i := by
  rw [← LinearMap.mem_ker, ker_toQuotientSections, mem_iInf]

/-- The map to quotient sections is injective exactly when the family has zero intersection. -/
theorem toQuotientSections_injective_iff :
    Function.Injective (toQuotientSections F hF) ↔ (⨅ i, F i) = ⊥ := by
  rw [← LinearMap.ker_eq_bot, ker_toQuotientSections]

end

end Submodule
