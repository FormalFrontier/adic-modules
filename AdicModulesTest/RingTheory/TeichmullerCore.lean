/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.Teichmuller
import AdicModules.RingTheory.Perfection
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.SimpleRing.Basic
meta import Lean.Elab.Tactic.Omega

/-!
# A Teichmüller image with imperfect residue

The ring `κ[[X]]`, with `κ = (ZMod 3)((T))`, is complete along the nonzero ideal
`(X)` and has reduced characteristic-three residue. The residue field is
imperfect: the Laurent monomial `T` has order one and is not a cube. These
inputs, and a nonzero perfection input with nonzero Teichmüller output, are
proved independently of the image characterization and injectivity laws.

Injectivity distinguishes the Teichmüller images of the distinct inputs two
and zero. The final proper-image boundary uses the image characterization.
Quotient plumbing is given for arbitrary reduced commutative coefficient
rings rather than requiring a field or perfectness. The same imperfect field also
supplies examples of the field operations on its inverse-Frobenius limit, with
unit inputs constructed using only the preexisting commutative ring structure.

## References

The independent inputs use Mathlib's Laurent-series monomial noncube,
power-series quotient and completeness, preexisting perfection ring, prime-field
units and coefficient ring-homomorphism laws. Only the indicated consumers use
the image/injectivity laws in `AdicModules.RingTheory.Teichmuller` and the field
interface in `AdicModules.RingTheory.Perfection`.
-/

-- This module supplies private input helpers and examples, not an exported API.
set_option linter.privateModule false

open PowerSeries

noncomputable section

universe u

section ResidueInputs

variable (κ : Type u) [CommRing κ]

private abbrev seriesIdeal : Ideal κ⟦X⟧ := Ideal.span {X}

private theorem constantCoeff_ker :
    RingHom.ker (constantCoeff (R := κ)) = seriesIdeal κ := by
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

private noncomputable def seriesResidueEquiv : (κ⟦X⟧ ⧸ seriesIdeal κ) ≃+* κ :=
  (Ideal.quotEquivOfEq (constantCoeff_ker κ).symm).trans
    ((constantCoeff (R := κ)).quotientKerEquivOfSurjective constantCoeff_surj)

private instance seriesResidue_charP (p : ℕ) [CharP κ p] :
    CharP (κ⟦X⟧ ⧸ seriesIdeal κ) p :=
  charP_of_injective_ringHom
    (f := (seriesResidueEquiv κ).symm.toRingHom) (seriesResidueEquiv κ).symm.injective p

private instance seriesResidue_reduced [IsReduced κ] :
    IsReduced (κ⟦X⟧ ⧸ seriesIdeal κ) :=
  isReduced_of_injective (seriesResidueEquiv κ).toRingHom (seriesResidueEquiv κ).injective

private theorem seriesIdeal_ne_bot [Nontrivial κ] : seriesIdeal κ ≠ ⊥ := by
  intro h
  have hx : (X : κ⟦X⟧) ∈ seriesIdeal κ := Ideal.subset_span (Set.mem_singleton X)
  rw [h, Ideal.mem_bot] at hx
  exact X_ne_zero hx

end ResidueInputs

section ImperfectResidue

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private abbrev κ := LaurentSeries (ZMod 3)

private instance residue_charP : CharP κ 3 :=
  charP_of_injective_ringHom (f := HahnSeries.C) HahnSeries.C_injective 3

-- Stock field structure implies reducedness; it does not imply perfectness.
noncomputable example : Field κ := inferInstance
example : IsReduced κ := inferInstance
example : CharP κ 3 := inferInstance

private theorem residue_infinite : Infinite κ :=
  Infinite.of_injective (fun n : ℤ ↦ (HahnSeries.single n (1 : ZMod 3) : κ)) (by
    intro a b h
    simpa only [HahnSeries.order_single one_ne_zero] using congrArg HahnSeries.order h)

private theorem T_not_cube :
    ¬ ∃ a : κ, a ^ 3 = HahnSeries.single (1 : ℤ) (1 : ZMod 3) := by
  rintro ⟨a, ha⟩
  have hord := congrArg HahnSeries.order ha
  rw [HahnSeries.order_pow, HahnSeries.order_single one_ne_zero] at hord
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hord
  omega

-- Imperfection is witnessed by a specific element, not a missing instance.
example : ¬ Function.Surjective (frobenius κ 3) := by
  intro h
  obtain ⟨a, ha⟩ := h (HahnSeries.single (1 : ℤ) (1 : ZMod 3))
  exact T_not_cube ⟨a, ha⟩

-- The kernel, completeness and quotient inputs are independent of the new laws.
example : RingHom.ker (constantCoeff (R := κ)) = seriesIdeal κ := constantCoeff_ker κ
example : Function.Surjective (constantCoeff (R := κ)) := constantCoeff_surj
example : IsAdicComplete (seriesIdeal κ) κ⟦X⟧ := inferInstance
example : IsReduced (κ⟦X⟧ ⧸ seriesIdeal κ) := inferInstance
example : CharP (κ⟦X⟧ ⧸ seriesIdeal κ) 3 := inferInstance
example : seriesIdeal κ ≠ ⊥ := seriesIdeal_ne_bot κ

private theorem residue_two_ne_zero : (2 : κ⟦X⟧ ⧸ seriesIdeal κ) ≠ 0 := by
  intro h
  have hκ : (2 : κ) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (seriesResidueEquiv κ) h
  have hc : HahnSeries.C (2 : ZMod 3) = (0 : κ) := by
    simpa only [map_ofNat] using hκ
  have : (2 : ZMod 3) = 0 := (HahnSeries.C_injective (Γ := ℤ)) (by
    rw [HahnSeries.C_zero]
    exact hc)
  exact (by decide : (2 : ZMod 3) ≠ 0) this

-- The stock perfection already supplies the input; no new tower data are assumed.
example : (2 : Perfection (κ⟦X⟧ ⧸ seriesIdeal κ) 3) ≠ 0 := by
  intro h
  apply residue_two_ne_zero
  simpa only [map_ofNat, map_zero] using congrArg (Perfection.coeff _ 3 0) h

-- Nontrivial output uses only the stock reduction law, not either new headline.
example : Perfection.teichmuller₀ 3 (seriesIdeal κ)
    (2 : Perfection (κ⟦X⟧ ⧸ seriesIdeal κ) 3) ≠ 0 := by
  intro h
  apply residue_two_ne_zero
  have hr := Perfection.mk_teichmuller₀
    (2 : Perfection (κ⟦X⟧ ⧸ seriesIdeal κ) 3)
  rw [h, map_zero] at hr
  simpa only [map_ofNat] using hr.symm

-- Injectivity distinguishes concrete inputs in the imperfect-residue model.
example : Perfection.teichmuller₀ 3 (seriesIdeal κ)
    (2 : Perfection (κ⟦X⟧ ⧸ seriesIdeal κ) 3) ≠
    Perfection.teichmuller₀ 3 (seriesIdeal κ) 0 := by
  intro h
  apply residue_two_ne_zero
  have hinput := Perfection.teichmuller₀_injective 3 (seriesIdeal κ) h
  simpa only [map_ofNat, map_zero] using congrArg (Perfection.coeff _ 3 0) hinput

-- This proper-image boundary depends on the image characterization,
-- unlike the imperfection witness and all inputs above.
example : C (HahnSeries.single (1 : ℤ) (1 : ZMod 3) : κ) ∉
    Set.range (Perfection.teichmuller₀ 3 (seriesIdeal κ)) := by
  intro h
  obtain ⟨r, hr⟩ := (Perfection.mem_range_teichmuller₀_iff 3 (seriesIdeal κ) _).mp h 1
  apply T_not_cube
  exact ⟨constantCoeff r, by simpa using congrArg (constantCoeff (R := κ)) hr⟩

-- These inputs use only the preexisting perfection ring and prime-field units.
-- Disabling the field instance for each declaration keeps it out of their inputs.
attribute [-instance] Perfection.instField in
private noncomputable def primeFieldLift : ZMod 3 →+* Perfection κ 3 :=
  (Perfection.lift 3 (ZMod 3) κ) HahnSeries.C

attribute [-instance] Perfection.instField in
private noncomputable def coreUnitTwo : (Perfection κ 3)ˣ :=
  Units.map primeFieldLift.toMonoidHom (Units.mk0 (2 : ZMod 3) (by decide))

attribute [-instance] Perfection.instField in
private theorem coeff_coreUnitTwo (n : ℕ) :
    Perfection.coeff κ 3 n (coreUnitTwo : Perfection κ 3) = 2 := by
  change Perfection.coeff κ 3 n (primeFieldLift (2 : ZMod 3)) = 2
  simp only [map_ofNat]

attribute [-instance] Perfection.instField in
private theorem coeff_coreUnitTwo_ne (n : ℕ) :
    Perfection.coeff κ 3 n (coreUnitTwo : Perfection κ 3) ≠ 0 ∧
      Perfection.coeff κ 3 n (coreUnitTwo : Perfection κ 3) ≠ 1 := by
  simp only [coeff_coreUnitTwo]
  constructor
  · intro h
    apply (by decide : (2 : ZMod 3) ≠ 0)
    apply HahnSeries.C_injective (Γ := ℤ)
    simpa only [map_ofNat, map_zero] using h
  · intro h
    apply (by decide : (2 : ZMod 3) ≠ 1)
    apply HahnSeries.C_injective (Γ := ℤ)
    simpa only [map_ofNat, map_one] using h

attribute [-instance] Perfection.instField in
private theorem core_zero_ne_one : (0 : Perfection κ 3) ≠ 1 := by
  intro h
  have hc := congrArg (Perfection.coeff κ 3 0) h
  exact (zero_ne_one : (0 : κ) ≠ 1) (by simpa only [map_zero, map_one] using hc)

-- The field constructor retains the exact preexisting ring data.
example : (Perfection.instField (K := κ) 3).toCommRing =
    inferInstanceAs (CommRing (Perfection.subring κ 3)) := rfl

-- Inversion is read through a ring homomorphism, not by reducing its definition.
example (n : ℕ) :
    Perfection.coeff κ 3 n ((coreUnitTwo : Perfection κ 3)⁻¹) = (2 : κ)⁻¹ := by
  rw [map_inv₀, coeff_coreUnitTwo]

-- The zeroth coefficient and the nonzero input are included in division.
example : Perfection.coeff κ 3 0
    ((coreUnitTwo : Perfection κ 3) / (coreUnitTwo : Perfection κ 3)) = 1 := by
  rw [map_div₀]
  exact div_self (coeff_coreUnitTwo_ne 0).1

example (n : ℕ) :
    Perfection.coeff κ 3 n
      (((coreUnitTwo : Perfection κ 3) ^ 2) / (coreUnitTwo : Perfection κ 3) ^ (-1 : ℤ)) =
      (2 : κ) ^ 2 / (2 : κ) ^ (-1 : ℤ) := by
  simp only [map_div₀, map_pow, map_zpow₀, coeff_coreUnitTwo]

example : (0 : Perfection κ 3)⁻¹ = 0 ∧ (coreUnitTwo : Perfection κ 3) / 0 = 0 := by
  simp

-- Surjectivity here uses the perfect prime field, not the imperfect Laurent field.
example : Function.Bijective (Perfection.coeff (ZMod 3) 3 0) :=
  ⟨RingHom.injective _, Perfection.coeff_surjective (surjective_frobenius (ZMod 3) 3) 0⟩

end ImperfectResidue
