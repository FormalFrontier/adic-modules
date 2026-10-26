/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianEtale
import AdicModules.Polynomial.Hensel
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.Tactic.NormNum

/-!
# A quadratic étale point over the 2-adic integers

The standard étale algebra for `X² - X + 2`, localized at its derivative,
has a point at zero over the residue field of the 2-adic integers. The
polynomial evaluates to `2` there before reduction, and its derivative
reduces to `-1`. This constructs the residue point without a base-ring
root or lift. The point also proves that the algebra is nontrivial; the
maximal ideal is nonzero and proper.

## Model inputs and conclusion

The standard étale construction and canonical adic completeness supply all model
inputs independently of `HenselianRing.existsUnique_algHom_lift_of_etale`.
The final unique-lift conclusion is an application of that theorem to these inputs.
-/

open Polynomial

namespace PadicInt

/-- The quadratic standard étale algebra over the 2-adic pair has its specified
zero residue point, with all lifting inputs proved independently. -/
private theorem exists_quadratic_etale_residue_point :
    ∃ (P : StandardEtalePair (PadicInt 2))
      (φ : P.Ring →ₐ[PadicInt 2]
        ((PadicInt 2) ⧸ IsLocalRing.maximalIdeal (PadicInt 2))),
      P.f = X ^ 2 - (X - C 2) ∧
      P.g = derivative P.f ∧
      φ P.X = 0 ∧
      Nontrivial P.Ring ∧
      HenselianRing (PadicInt 2) (IsLocalRing.maximalIdeal (PadicInt 2)) ∧
      Algebra.Etale (PadicInt 2) P.Ring ∧
      IsLocalRing.maximalIdeal (PadicInt 2) ≠ ⊥ ∧
      IsLocalRing.maximalIdeal (PadicInt 2) ≠ ⊤ := by
  let P : StandardEtalePair (PadicInt 2) :=
    { f := X ^ 2 - (X - C 2)
      monic_f := monic_X_pow_sub (by
        rw [degree_X_sub_C]
        norm_num)
      g := derivative (X ^ 2 - (X - C 2))
      cond := ⟨1, 0, 1, by simp⟩ }
  let : HenselianRing (PadicInt 2) (IsLocalRing.maximalIdeal (PadicInt 2)) :=
    IsAdicComplete.henselianRing _ _
  have htwo : (2 : PadicInt 2) ∈ IsLocalRing.maximalIdeal (PadicInt 2) := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (Set.mem_singleton (2 : PadicInt 2))
  have hpoint : P.HasMap
      (0 : (PadicInt 2) ⧸ IsLocalRing.maximalIdeal (PadicInt 2)) := by
    constructor
    · suffices h : Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (PadicInt 2)) (2 : PadicInt 2) = 0 by
        simpa [P] using h
      exact Ideal.Quotient.eq_zero_iff_mem.mpr htwo
    · simp [P]
  let φ : P.Ring →ₐ[PadicInt 2]
      ((PadicInt 2) ⧸ IsLocalRing.maximalIdeal (PadicInt 2)) := P.lift 0 hpoint
  have hnontrivial : Nontrivial P.Ring := by
    refine ⟨⟨0, 1, ?_⟩⟩
    intro h
    have hzero_one := congrArg φ h
    simp at hzero_one
  have hne_bot : IsLocalRing.maximalIdeal (PadicInt 2) ≠ ⊥ := by
    intro h
    simp [h] at htwo
  have hne_top : IsLocalRing.maximalIdeal (PadicInt 2) ≠ ⊤ :=
    (inferInstance : (IsLocalRing.maximalIdeal (PadicInt 2)).IsMaximal).ne_top
  exact ⟨P, φ, rfl, rfl, P.lift_X 0 hpoint, hnontrivial, inferInstance,
    inferInstance, hne_bot, hne_top⟩

/-- The zero residue point of the quadratic standard étale algebra has a unique lift
by `HenselianRing.existsUnique_algHom_lift_of_etale`. -/
private theorem existsUnique_algHom_lift_quadratic :
    ∃ (P : StandardEtalePair (PadicInt 2))
      (φ : P.Ring →ₐ[PadicInt 2]
        ((PadicInt 2) ⧸ IsLocalRing.maximalIdeal (PadicInt 2))),
      P.f = X ^ 2 - (X - C 2) ∧
      P.g = derivative P.f ∧
      φ P.X = 0 ∧
      Nontrivial P.Ring ∧
      IsLocalRing.maximalIdeal (PadicInt 2) ≠ ⊥ ∧
      IsLocalRing.maximalIdeal (PadicInt 2) ≠ ⊤ ∧
      ∃! ψ : P.Ring →ₐ[PadicInt 2] (PadicInt 2),
        (Ideal.Quotient.mkₐ (PadicInt 2)
          (IsLocalRing.maximalIdeal (PadicInt 2))).comp ψ = φ := by
  obtain ⟨P, φ, hf, hg, hpoint, hnontrivial, hHenselian, hEtale, hne_bot, hne_top⟩ :=
    exists_quadratic_etale_residue_point
  let := hHenselian
  let := hEtale
  exact ⟨P, φ, hf, hg, hpoint, hnontrivial, hne_bot, hne_top,
    HenselianRing.existsUnique_algHom_lift_of_etale φ⟩

end PadicInt
