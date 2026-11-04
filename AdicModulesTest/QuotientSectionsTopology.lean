/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Topology.Algebra.Module.QuotientSections
import Mathlib.Topology.Order

/-!
# A proper closed stage in integer quotient sections

For the constant bottom filtration on `ℤ`, indexed by `ℕ`, give each quotient its
discrete topology explicitly. The stage-closure theorem excludes the section of `1`
from the closure of the stage-zero image: the coordinate-zero fiber is a proper
closed subset of the section space. No topology on the source integers is used.
-/

local notation "F" => (fun _ : ℕ => (⊥ : Submodule ℤ ℤ))
private theorem hF : Antitone F := fun _ _ _ => le_rfl
local notation "Γ" => ModuleCat.sectionsSubmodule (Submodule.quotientDiagram F hF)

-- A nonzero section outside the closed stage, using the new stage-closure API.
example :
    Submodule.toQuotientSections F hF (1 : ℤ) ∉
      @closure Γ
        (@instTopologicalSpaceSubtype (∀ i : ℕᵒᵖ, ℤ ⧸ F i.unop)
          (fun b => b ∈ Γ)
          (@Pi.topologicalSpace ℕᵒᵖ (fun i => ℤ ⧸ F i.unop) (fun _ => ⊥)))
        ((Submodule.toQuotientSections F hF) '' (F 0 : Set ℤ)) := by
  rw [Submodule.closure_toQuotientSections_image F hF (fun _ => ⊥) 0
    (@isClosed_discrete (ℤ ⧸ F 0) ⊥ (discreteTopology_bot _) {0})]
  intro h
  have hone : (1 : ℤ) ∈ F 0 := by
    apply (Submodule.Quotient.mk_eq_zero (p := F 0) (x := (1 : ℤ))).1
    exact (Submodule.toQuotientSections_apply F hF (1 : ℤ) (Opposite.op 0)).symm.trans h
  exact (one_ne_zero : (1 : ℤ) ≠ 0) (by simpa only [Submodule.mem_bot] using hone)
