/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.LinearAlgebra.Quotient.Sections

/-!
# Quotient sections for the zero filtration on the integers

The map to quotient sections for the constant bottom filtration on `ℤ`, indexed by `ℕ`,
is injective by the intersection criterion. Evaluating the section of `1` at index `0`
gives a nonzero quotient class.
-/

example : Function.Injective
    (Submodule.toQuotientSections (R := ℤ) (M := ℤ)
      (fun _ : ℕ => ⊥) (fun _ _ _ => le_rfl)) := by
  exact (Submodule.toQuotientSections_injective_iff
    (R := ℤ) (M := ℤ) (fun _ : ℕ => ⊥) (fun _ _ _ => le_rfl)).2 (by simp)

example :
    Submodule.quotientSectionsEval (R := ℤ) (M := ℤ)
        (fun _ : ℕ => ⊥) (fun _ _ _ => le_rfl) (Opposite.op 0)
      (Submodule.toQuotientSections (R := ℤ) (M := ℤ)
        (fun _ : ℕ => ⊥) (fun _ _ _ => le_rfl) 1) ≠ 0 := by
  have hcoord :
      Submodule.quotientSectionsEval (R := ℤ) (M := ℤ)
          (fun _ : ℕ => ⊥) (fun _ _ _ => le_rfl) (Opposite.op 0)
        (Submodule.toQuotientSections (R := ℤ) (M := ℤ)
          (fun _ : ℕ => ⊥) (fun _ _ _ => le_rfl) 1) =
        (⊥ : Submodule ℤ ℤ).mkQ (1 : ℤ) := by
    exact congrArg
      (fun f : ℤ →ₗ[ℤ] ℤ ⧸ (⊥ : Submodule ℤ ℤ) => f (1 : ℤ))
      (Submodule.quotientSectionsEval_comp_toQuotientSections (R := ℤ) (M := ℤ)
        (fun _ : ℕ => ⊥) (fun _ _ _ => le_rfl) (Opposite.op 0))
  intro hzero
  have hmk : (⊥ : Submodule ℤ ℤ).mkQ (1 : ℤ) = 0 := hcoord.symm.trans hzero
  apply (one_ne_zero : (1 : ℤ) ≠ 0)
  simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_bot] using hmk
