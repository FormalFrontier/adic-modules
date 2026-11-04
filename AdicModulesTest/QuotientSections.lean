/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.LinearAlgebra.Quotient.Sections

/-!
# Injectivity for the zero filtration on the integers

The map to quotient sections for the constant bottom filtration on `ℤ`, indexed by `ℕ`,
is injective by the intersection criterion.
-/

example : Function.Injective
    (Submodule.toQuotientSections (R := ℤ) (M := ℤ)
      (fun _ : ℕ => ⊥) (fun _ _ _ => le_rfl)) := by
  exact (Submodule.toQuotientSections_injective_iff
    (R := ℤ) (M := ℤ) (fun _ : ℕ => ⊥) (fun _ _ _ => le_rfl)).2 (by simp)
