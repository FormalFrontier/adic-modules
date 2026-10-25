/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.LinearAlgebra.Pi
public import Mathlib.Tactic.NormNum
public meta import Lean.Elab.Tactic.Omega

/-!
# Canonical quotient-product squares over the integers

The coordinate-map and ideal-inclusion squares are expressed as equalities of
linear maps between the original dependent-product quotients. The arithmetic
examples use the canonical integer-module quotients by the actions of the ideals
`(4)` and `(2)`. Multiplication by two and three acts in the two coordinates.
The transition preserves the class of one and kills the nonzero class of two.

## References

The quotient arrows and representative calculations use Mathlib's
`Submodule.mapQ`, `Submodule.factor`, and pointwise submodule-action API.
The product comparisons and their representative equations are those of
`AdicModules.LinearAlgebra.Pi`; their implementations are not unfolded here.
-/

set_option warningAsError true

universe uR uι uM uN

open scoped Pointwise

namespace QuotientPiNaturality

private def coordinateMapSquare
    {R : Type uR} [CommRing R]
    {ι : Type uι}
    {M : ι → Type uM} {N : ι → Type uN}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    {I : Ideal R} (hI : I.FG)
    (f : ∀ i, M i →ₗ[R] N i) : Prop :=
    (LinearMap.piMap (fun i =>
      (I • (⊤ : Submodule R (M i))).mapQ
        (I • (⊤ : Submodule R (N i))) (f i)
        (Submodule.smul_top_le_comap_smul_top I (f i)))).comp
      (hI.quotientPi M).toLinearMap =
    (hI.quotientPi N).toLinearMap.comp
      ((I • (⊤ : Submodule R (∀ i, M i))).mapQ
        (I • (⊤ : Submodule R (∀ i, N i)))
        (LinearMap.piMap f)
        (Submodule.smul_top_le_comap_smul_top I (LinearMap.piMap f)))

private def quotientTransitionSquare
    {R : Type uR} [CommRing R]
    {ι : Type uι} {M : ι → Type uM}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {I J : Ideal R} (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J) : Prop :=
    (LinearMap.piMap (fun i =>
      Submodule.factor
        (p := I • (⊤ : Submodule R (M i)))
        (p' := J • (⊤ : Submodule R (M i)))
        (Submodule.smul_mono_left
          (N := (⊤ : Submodule R (M i))) hIJ))).comp
      (hI.quotientPi M).toLinearMap =
    (hJ.quotientPi M).toLinearMap.comp
      (Submodule.factor
        (p := I • (⊤ : Submodule R (∀ i, M i)))
        (p' := J • (⊤ : Submodule R (∀ i, M i)))
        (Submodule.smul_mono_left
          (N := (⊤ : Submodule R (∀ i, M i))) hIJ))

private abbrev fourIdeal : Ideal ℤ := Ideal.span {(4 : ℤ)}

private abbrev twoIdeal : Ideal ℤ := Ideal.span {(2 : ℤ)}

private theorem fourFG : fourIdeal.FG := by
  exact ⟨{(4 : ℤ)}, by simp [fourIdeal]⟩

private theorem twoFG : twoIdeal.FG := by
  exact ⟨{(2 : ℤ)}, by simp [twoIdeal]⟩

private theorem four_le_two : fourIdeal ≤ twoIdeal := by
  apply (Ideal.span_singleton_le_iff_mem twoIdeal).mpr
  exact Ideal.mem_span_singleton.mpr ⟨(2 : ℤ), by norm_num⟩

private abbrev fourSubmodule : Submodule ℤ ℤ := fourIdeal • ⊤

private abbrev twoSubmodule : Submodule ℤ ℤ := twoIdeal • ⊤

private abbrev fourProduct : Submodule ℤ (Fin 2 → ℤ) := fourIdeal • ⊤

private abbrev twoProduct : Submodule ℤ (Fin 2 → ℤ) := twoIdeal • ⊤

private def coordinateMaps (i : Fin 2) : ℤ →ₗ[ℤ] ℤ :=
  (if i = 0 then (2 : ℤ) else 3) • LinearMap.id

private theorem mem_principal_action (n a : ℤ) :
    a ∈ (Ideal.span {n} : Ideal ℤ) • (⊤ : Submodule ℤ ℤ) ↔
      ∃ b : ℤ, n * b = a := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, smul_eq_mul]

private theorem four_class_ne_zero {a : ℤ} (ha : 1 ≤ a) (ha' : a ≤ 3) :
    fourSubmodule.mkQ a ≠ 0 := by
  intro h
  have hm : a ∈ fourSubmodule := (Submodule.Quotient.mk_eq_zero fourSubmodule).mp h
  obtain ⟨b, hb⟩ := (mem_principal_action 4 a).mp hm
  omega

private theorem one_mod_two_ne_zero : twoSubmodule.mkQ 1 ≠ 0 := by
  intro h
  have hm : (1 : ℤ) ∈ twoSubmodule :=
    (Submodule.Quotient.mk_eq_zero twoSubmodule).mp h
  obtain ⟨b, hb⟩ := (mem_principal_action 2 1).mp hm
  omega

private theorem two_mod_two_eq_zero : twoSubmodule.mkQ 2 = 0 := by
  apply (Submodule.Quotient.mk_eq_zero twoSubmodule).mpr
  exact (mem_principal_action 2 2).mpr ⟨1, by norm_num⟩

private theorem three_mod_two_eq_one : twoSubmodule.mkQ 3 = twoSubmodule.mkQ 1 := by
  apply (Submodule.Quotient.eq twoSubmodule).mpr
  exact (mem_principal_action 2 (3 - 1)).mpr ⟨1, by norm_num⟩

private theorem coordinate_images_nonzero_and_distinct :
    fourSubmodule.mkQ 2 ≠ 0 ∧ fourSubmodule.mkQ 3 ≠ 0 ∧
      fourSubmodule.mkQ 2 ≠ fourSubmodule.mkQ 3 := by
  refine ⟨four_class_ne_zero (by norm_num) (by norm_num),
    four_class_ne_zero (by norm_num) (by norm_num), ?_⟩
  intro h
  have hm : (2 : ℤ) - 3 ∈ fourSubmodule :=
    (Submodule.Quotient.eq fourSubmodule).mp h
  obtain ⟨b, hb⟩ := (mem_principal_action 4 (2 - 3)).mp hm
  omega

private theorem coordinate_paths_on_ones :
    ((LinearMap.piMap (fun i : Fin 2 =>
      fourSubmodule.mapQ fourSubmodule (coordinateMaps i)
        (Submodule.smul_top_le_comap_smul_top fourIdeal (coordinateMaps i)))).comp
      (fourFG.quotientPi (fun _ : Fin 2 => ℤ)).toLinearMap)
        (fourProduct.mkQ (fun _ => 1)) =
      (fun i => fourSubmodule.mkQ (if i = 0 then 2 else 3)) ∧
    ((fourFG.quotientPi (fun _ : Fin 2 => ℤ)).toLinearMap.comp
      (fourProduct.mapQ fourProduct (LinearMap.piMap coordinateMaps)
        (Submodule.smul_top_le_comap_smul_top fourIdeal
          (LinearMap.piMap coordinateMaps))))
        (fourProduct.mkQ (fun _ => 1)) =
      (fun i => fourSubmodule.mkQ (if i = 0 then 2 else 3)) := by
  constructor <;> funext i <;> by_cases hi : i = 0 <;>
    simp [LinearMap.comp_apply, LinearMap.piMap, coordinateMaps, hi, smul_eq_mul]

/-- The quotient map from the integers modulo `(4)` to the integers modulo `(2)` preserves
the nonzero class of `1` and kills the nonzero class of `2`. -/
public theorem integer_transition_nonzero_image_and_kernel :
    Submodule.factor
        (p := (Ideal.span {(4 : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ ℤ))
        (p' := (Ideal.span {(2 : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ ℤ))
        (by exact Submodule.smul_mono_left (N := (⊤ : Submodule ℤ ℤ)) four_le_two)
        (((Ideal.span {(4 : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ ℤ)).mkQ 1) =
      ((Ideal.span {(2 : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ ℤ)).mkQ 1 ∧
      ((Ideal.span {(2 : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ ℤ)).mkQ 1 ≠ 0 ∧
      ((Ideal.span {(4 : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ ℤ)).mkQ 2 ≠ 0 ∧
    Submodule.factor
        (p := (Ideal.span {(4 : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ ℤ))
        (p' := (Ideal.span {(2 : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ ℤ))
        (by exact Submodule.smul_mono_left (N := (⊤ : Submodule ℤ ℤ)) four_le_two)
        (((Ideal.span {(4 : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ ℤ)).mkQ 2) = 0 := by
  refine ⟨Submodule.factor_mk _ _, one_mod_two_ne_zero,
    four_class_ne_zero (by norm_num) (by norm_num), ?_⟩
  rw [Submodule.factor_mk]
  exact two_mod_two_eq_zero

private theorem transition_paths_on_two_three :
    ((LinearMap.piMap (fun _ : Fin 2 =>
      Submodule.factor
        (p := fourSubmodule) (p' := twoSubmodule)
        (Submodule.smul_mono_left (N := (⊤ : Submodule ℤ ℤ)) four_le_two))).comp
      (fourFG.quotientPi (fun _ : Fin 2 => ℤ)).toLinearMap)
        (fourProduct.mkQ (fun i => if i = 0 then 2 else 3)) =
      (fun i => twoSubmodule.mkQ (if i = 0 then 0 else 1)) ∧
    ((twoFG.quotientPi (fun _ : Fin 2 => ℤ)).toLinearMap.comp
      (Submodule.factor
        (p := fourProduct) (p' := twoProduct)
        (Submodule.smul_mono_left
          (N := (⊤ : Submodule ℤ (Fin 2 → ℤ))) four_le_two)))
        (fourProduct.mkQ (fun i => if i = 0 then 2 else 3)) =
      (fun i => twoSubmodule.mkQ (if i = 0 then 0 else 1)) := by
  constructor <;> funext i <;> by_cases hi : i = 0
  · simp [LinearMap.comp_apply, LinearMap.piMap, hi]
  · simpa [LinearMap.comp_apply, LinearMap.piMap, hi] using three_mod_two_eq_one
  · simp [LinearMap.comp_apply, hi]
  · simpa [LinearMap.comp_apply, LinearMap.piMap, hi] using three_mod_two_eq_one

private theorem zero_ideal_action :
    (⊥ : Ideal ℤ) • (⊤ : Submodule ℤ ℤ) = ⊥ := by
  exact Submodule.bot_smul (R := ℤ) (A := ℤ) (⊤ : Submodule ℤ ℤ)

private theorem top_ideal_class (a : ℤ) :
    ((⊤ : Ideal ℤ) • (⊤ : Submodule ℤ ℤ)).mkQ a = 0 := by
  apply (Submodule.Quotient.mk_eq_zero
    ((⊤ : Ideal ℤ) • (⊤ : Submodule ℤ ℤ))).mpr
  simpa only [one_smul] using
    (Submodule.smul_mem_smul
      (show (1 : ℤ) ∈ (⊤ : Ideal ℤ) from trivial)
      (show a ∈ (⊤ : Submodule ℤ ℤ) from trivial))

private theorem empty_product_class (x : Fin 0 → ℤ) :
    (fourIdeal • (⊤ : Submodule ℤ (Fin 0 → ℤ))).mkQ x = 0 := by
  have hx : x = 0 := by
    funext i
    exact Fin.elim0 i
  rw [hx, map_zero]

end QuotientPiNaturality
