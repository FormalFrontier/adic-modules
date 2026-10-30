/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Hom
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Completed-Hom evaluation in an infinite torsion target

For the target `(ℕ →₀ ℤ) × ZMod 2`, every completed value is recovered by
completing evaluation at `1` on the original module of maps from `ℤ`. The witness
uses the inverse completed-Hom equivalence on the scalar-multiplication map of the
given completed value. Thus the client uses arbitrary completed inputs, without
requiring target finiteness, projectivity or completeness, and does not unfold the
comparison or its equivalence.
-/

@[expose] public section

noncomputable section

namespace AdicCompletion

private theorem completed_evaluation_surjective :
    Function.Surjective
      (map (Ideal.span {(2 : ℤ)})
        (LinearMap.applyₗ (R := ℤ) (M₂ := (ℕ →₀ ℤ) × ZMod 2) (1 : ℤ))) := by
  let I : Ideal ℤ := Ideal.span {2}
  let N := (ℕ →₀ ℤ) × ZMod 2
  intro x
  let E := homEquivOfFiniteProjective I ℤ N
  let f : AdicCompletion I ℤ →ₗ[AdicCompletion I ℤ] AdicCompletion I N :=
    LinearMap.toSpanSingleton (AdicCompletion I ℤ) (AdicCompletion I N) x
  refine ⟨E.symm f, ?_⟩
  rw [← homComparison_apply_of]
  have hf : homComparison I ℤ N (E.symm f) = f := by
    rw [← homEquivOfFiniteProjective_apply]
    exact E.apply_symm_apply f
  rw [hf]
  change (1 : AdicCompletion I ℤ) • x = x
  exact one_smul _ x

end AdicCompletion
