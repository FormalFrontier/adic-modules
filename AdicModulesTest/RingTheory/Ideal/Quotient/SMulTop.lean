/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.Ideal.Quotient.SMulTop
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.NormNum

/-!
# A noncommutative quotient by an ideal times the top submodule

For `A = Matrix (Fin 2) (Fin 2) ℤ`, the quotient by
`(⊥ : Ideal ℤ) ^ 1 • (⊤ : Submodule ℤ A)` retains the noncommuting matrix
units `E₀₁` and `E₁₀`. Their commutator survives independently of the
noncommutativity calculation. Its negative diagonal entry also detects the
scalar term, rather than just its nonzero `E₀₀` entry.

The calculations use the algebra quotient projection and its compatibility
with the submodule quotient projection. The quotient carrier is not replaced
by the matrix ring. Exponent zero, the top ideal and subsingleton algebras give
trivial quotient boundary cases.

## References

The matrix-unit calculations follow Mathlib's `Matrix.single` arithmetic in
`Mathlib.Data.Matrix.Basis`. The recovery of a matrix from the bottom quotient
uses Mathlib's `Submodule.quotEquivOfEqBot` and its projection formula in
`Mathlib.LinearAlgebra.Quotient.Basic`. Entrywise separation also follows the
integer matrix quotient examples in
`AdicModulesTest.RingTheory.Ideal.Quotient.Matrix`.
-/

@[expose] public section

namespace Ideal.Quotient

private abbrev IntMatrix := Matrix (Fin 2) (Fin 2) ℤ

private abbrev bottomPower : Ideal ℤ := (⊥ : Ideal ℤ) ^ 1

private abbrev bottomPowerSubmodule : Submodule ℤ IntMatrix :=
  bottomPower • (⊤ : Submodule ℤ IntMatrix)

private def matrixUnit01 : IntMatrix := Matrix.single 0 1 1

private def matrixUnit10 : IntMatrix := Matrix.single 1 0 1

private def matrixCommutator : IntMatrix :=
  matrixUnit01 * matrixUnit10 + (-1 : ℤ) • (matrixUnit10 * matrixUnit01)

/-- The two matrix-unit images do not commute, and their commutator has a
nonzero image whose scalar contribution does not disappear. -/
private theorem matrix_smulTop_noncommutative_and_commutator :
    let q : IntMatrix →ₐ[ℤ] IntMatrix ⧸ bottomPowerSubmodule :=
      Ideal.Quotient.mkₐ ℤ (bottomPower.smulTop IntMatrix)
    q matrixUnit01 * q matrixUnit10 ≠ q matrixUnit10 * q matrixUnit01 ∧
      q matrixCommutator ≠ 0 ∧
      q matrixCommutator =
        q matrixUnit01 * q matrixUnit10 +
          (-1 : ℤ) • (q matrixUnit10 * q matrixUnit01) ∧
      q matrixCommutator ≠ q (matrixUnit01 * matrixUnit10) := by
  let q : IntMatrix →ₐ[ℤ] IntMatrix ⧸ bottomPowerSubmodule :=
    Ideal.Quotient.mkₐ ℤ (bottomPower.smulTop IntMatrix)
  have hN : bottomPowerSubmodule = ⊥ := by
    simp [bottomPowerSubmodule, bottomPower]
  let e := bottomPowerSubmodule.quotEquivOfEqBot hN
  have hleft : Function.LeftInverse e q := by
    intro a
    have hcoe : (q : IntMatrix → IntMatrix ⧸ bottomPowerSubmodule) =
        (bottomPowerSubmodule.mkQ : IntMatrix → IntMatrix ⧸ bottomPowerSubmodule) :=
      Ideal.Quotient.coe_mkₐ_smulTop bottomPower
    calc
      e (q a) = e (bottomPowerSubmodule.mkQ a) := congrArg e (congrFun hcoe a)
      _ = a := Submodule.quotEquivOfEqBot_apply_mk bottomPowerSubmodule hN a
  have hXY : matrixUnit01 * matrixUnit10 = Matrix.single 0 0 (1 : ℤ) := by
    simp only [matrixUnit01, matrixUnit10, Matrix.single_mul_single_same, mul_one]
  have hYX : matrixUnit10 * matrixUnit01 = Matrix.single 1 1 (1 : ℤ) := by
    simp only [matrixUnit01, matrixUnit10, Matrix.single_mul_single_same, mul_one]
  have hproducts : matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01 := by
    intro h
    have h00 := congrArg (fun a : IntMatrix ↦ a 0 0) h
    norm_num [hXY, hYX, Matrix.single_apply] at h00
  have hnoncommute : q matrixUnit01 * q matrixUnit10 ≠
      q matrixUnit10 * q matrixUnit01 := by
    intro h
    apply hproducts
    apply hleft.injective
    simpa only [map_mul] using h
  have hcommutator00 : matrixCommutator 0 0 = 1 := by
    norm_num [matrixCommutator, hXY, hYX, Matrix.single_apply]
  have hcommutator11 : matrixCommutator 1 1 = -1 := by
    norm_num [matrixCommutator, hXY, hYX, Matrix.single_apply]
  have hsurvives : q matrixCommutator ≠ 0 := by
    intro h
    have hrecover : e (q matrixCommutator) = matrixCommutator := by
      calc
        e (q matrixCommutator) = e (bottomPowerSubmodule.mkQ matrixCommutator) :=
          congrArg e (Ideal.Quotient.mkₐ_smulTop_apply bottomPower matrixCommutator)
        _ = matrixCommutator :=
          Submodule.quotEquivOfEqBot_apply_mk bottomPowerSubmodule hN matrixCommutator
    have hzero : matrixCommutator = 0 := by
      calc
        matrixCommutator = e (q matrixCommutator) := hrecover.symm
        _ = e 0 := congrArg e h
        _ = 0 := map_zero e
    have h00 := congrArg (fun a : IntMatrix ↦ a 0 0) hzero
    norm_num [hcommutator00] at h00
  have hscalar (r : ℤ) (a : IntMatrix) :
      q (r • a) = r • bottomPowerSubmodule.mkQ a := by
    have hlinear : q.toLinearMap = bottomPowerSubmodule.mkQ :=
      Ideal.Quotient.mkₐ_smulTop_toLinearMap bottomPower
    calc
      q (r • a) = r • q a := map_smul q r a
      _ = r • bottomPowerSubmodule.mkQ a :=
        congrArg (fun b : IntMatrix ⧸ bottomPowerSubmodule ↦ r • b)
          (LinearMap.congr_fun hlinear a)
  have hformula : q matrixCommutator =
      q matrixUnit01 * q matrixUnit10 +
        (-1 : ℤ) • (q matrixUnit10 * q matrixUnit01) := by
    calc
      q matrixCommutator = q (matrixUnit01 * matrixUnit10) +
          (-1 : ℤ) • bottomPowerSubmodule.mkQ (matrixUnit10 * matrixUnit01) := by
        rw [matrixCommutator, map_add, hscalar]
      _ = q (matrixUnit01 * matrixUnit10) +
          (-1 : ℤ) • q (matrixUnit10 * matrixUnit01) :=
        congrArg (fun b : IntMatrix ⧸ bottomPowerSubmodule ↦
          q (matrixUnit01 * matrixUnit10) + (-1 : ℤ) • b)
          (Ideal.Quotient.mkₐ_smulTop_apply bottomPower
            (matrixUnit10 * matrixUnit01)).symm
      _ = q matrixUnit01 * q matrixUnit10 +
          (-1 : ℤ) • (q matrixUnit10 * q matrixUnit01) := by
        simp only [map_mul]
  have hscalar_visible : q matrixCommutator ≠ q (matrixUnit01 * matrixUnit10) := by
    intro h
    have h11 := congrArg (fun a : IntMatrix ↦ a 1 1) (hleft.injective h)
    norm_num [hcommutator11, hXY, Matrix.single_apply] at h11
  exact ⟨hnoncommute, hsurvives, hformula, hscalar_visible⟩

private theorem matrix_smulTop_zero_level (I : Ideal ℤ) :
    (1 : IntMatrix ⧸ (I ^ 0 • (⊤ : Submodule ℤ IntMatrix))) = 0 := by
  have htop : I ^ 0 • (⊤ : Submodule ℤ IntMatrix) = ⊤ := by simp
  exact @Subsingleton.elim _ (Submodule.Quotient.subsingleton_iff.mpr htop) _ _

private theorem matrix_smulTop_top :
    (1 : IntMatrix ⧸ ((⊤ : Ideal ℤ) • (⊤ : Submodule ℤ IntMatrix))) = 0 := by
  have htop : (⊤ : Ideal ℤ) • (⊤ : Submodule ℤ IntMatrix) = ⊤ := by simp
  exact @Subsingleton.elim _ (Submodule.Quotient.subsingleton_iff.mpr htop) _ _

universe u v

private theorem smulTop_subsingleton {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A] [Subsingleton A] (J : Ideal R) :
    (1 : A ⧸ (J • (⊤ : Submodule R A))) = 0 :=
  Subsingleton.elim _ _

end Ideal.Quotient
