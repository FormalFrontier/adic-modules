/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.Teichmuller
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.NormNum

/-!
# Standard models of Teichmüller sections

The input maps, kernel computations and algebraic completeness/perfectness
instances below use stock mathematics independently of the section output laws.
The mixed-characteristic model uses the usual normed `ℤ_[3]`; the power-series
model permits arbitrary perfect coefficient fields, including the infinite field
`AlgebraicClosure (ZMod 3)`.

The power-series comparison follows from the multiplicative universal property.
The computation at `2` in `ℤ_[3]` uses only multiplicativity and reduction;
naive integer-valued residue representatives are not multiplicative.
-/

-- This module supplies private examples and input helpers, not an exported API.
set_option linter.privateModule false

open PowerSeries

namespace PadicInt

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem reduction_three_surjective :
    Function.Surjective (toZMod : ℤ_[3] →+* ZMod 3) :=
  ZMod.ringHom_surjective toZMod

private theorem reduction_three_ker :
    RingHom.ker (toZMod : ℤ_[3] →+* ZMod 3) = Ideal.span {(3 : ℤ_[3])} := by
  simp only [ker_toZMod, maximalIdeal_eq_span_p, Nat.cast_ofNat]

private instance reduction_three_complete :
    IsAdicComplete (RingHom.ker (toZMod : ℤ_[3] →+* ZMod 3)) ℤ_[3] := by
  rw [ker_toZMod]
  infer_instance

-- The residue characteristic and perfectness are independent of the section.
example : PerfectRing (ZMod 3) 3 := inferInstance
example : CharP (ZMod 3) 3 := inferInstance
example : (2 : ZMod 3) ≠ 0 := by decide
example : (2 : ℤ_[3]) ≠ -1 := by norm_num

-- The integer-valued residue representatives fail multiplicativity independently
-- of any construction of a Teichmüller section.
example : ¬ (∀ a b : ZMod 3,
    ((a * b).val : ℤ_[3]) = (a.val : ℤ_[3]) * (b.val : ℤ_[3])) := by
  intro h
  have htwo := h 2 2
  change (1 : ℤ_[3]) = 2 * 2 at htwo
  norm_num at htwo

private noncomputable def sectionThree : ZMod 3 →*₀ ℤ_[3] :=
  RingHom.teichmullerSection 3 toZMod reduction_three_surjective

/-- The characteristic representative is `-1`, not the naive integer lift `2`. -/
private theorem sectionThree_two : sectionThree 2 = -1 := by
  have hres : (2 : ZMod 3) ^ 2 = 1 := by decide
  have hs : sectionThree 2 ^ 2 = 1 := by
    rw [← map_pow, hres, map_one]
  rcases sq_eq_one_iff.mp hs with h | h
  · have hr := RingHom.teichmullerSection_reduction_apply 3 toZMod
      reduction_three_surjective (2 : ZMod 3)
    change toZMod (sectionThree 2) = 2 at hr
    rw [h, map_one] at hr
    exact ((by decide : (1 : ZMod 3) ≠ 2) hr).elim
  · exact h

example : sectionThree 0 = 0 := map_zero _
example : sectionThree 1 = 1 := map_one _

example : toZMod (sectionThree 2) = (2 : ZMod 3) :=
  RingHom.teichmullerSection_reduction_apply 3 toZMod reduction_three_surjective 2

example : IsUnit (sectionThree 2) :=
  RingHom.isUnit_teichmullerSection 3 toZMod reduction_three_surjective (by decide)

-- The zeroth approximation includes every representative, not only a chosen lift.
example : sectionThree 2 ≡ (-1 : ℤ_[3]) [SMOD RingHom.ker toZMod] := by
  simpa [sectionThree] using RingHom.teichmullerSection_sModEq 3 toZMod
    reduction_three_surjective (2 : ZMod 3) (-1) 0 (by norm_num; decide)

-- The computed output differs from the naive integer-valued representative.
example : sectionThree 2 ≠ (2 : ℤ_[3]) := by
  rw [sectionThree_two]
  norm_num

-- A cheap boundary for the characteristic assumption on the ring refinement.
example : sectionThree (1 + 1) ≠ sectionThree 1 + sectionThree 1 := by
  have htwo : (1 + 1 : ZMod 3) = 2 := by norm_num
  rw [htwo, sectionThree_two, map_one]
  norm_num

end PadicInt

namespace PowerSeries

universe u

variable {k : Type u} [Field k]

/-- The constant coefficient map in the power-series model has kernel `(X)`. -/
private theorem ker_constantCoeff_eq_span_X :
    RingHom.ker (constantCoeff (R := k)) = Ideal.span {(X : k⟦X⟧)} := by
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

private instance constantCoeff_complete :
    IsAdicComplete (RingHom.ker (constantCoeff (R := k))) k⟦X⟧ := by
  rw [ker_constantCoeff_eq_span_X]
  infer_instance

-- Both surjectivity and the independent section C are stock coefficient facts.
example : Function.Surjective (constantCoeff (R := k)) := constantCoeff_surj
example (a : k) : constantCoeff (C a) = a := constantCoeff_C a
example : constantCoeff.comp (C : k →+* k⟦X⟧) = RingHom.id k := constantCoeff_comp_C

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k]

-- The source characteristic gives the target characteristic without target perfection.
private instance powerSeries_charP : CharP k⟦X⟧ p :=
  charP_of_injective_ringHom (f := C) C_injective p

/-- Uniqueness identifies the Teichmüller section with the constant-series map. -/
private theorem teichmullerSection_eq_C :
    RingHom.teichmullerSection p (constantCoeff (R := k)) constantCoeff_surj =
      (C : k →+* k⟦X⟧).toMonoidWithZeroHom := by
  symm
  exact RingHom.teichmullerSection_unique p (constantCoeff (R := k)) constantCoeff_surj
    (C : k →+* k⟦X⟧).toMonoidWithZeroHom (fun a ↦ constantCoeff_C a)

example : RingHom.teichmullerSection p (constantCoeff (R := k)) constantCoeff_surj 0 = 0 :=
  map_zero _

example (a : k) (ha : a ≠ 0) :
    RingHom.teichmullerSection p (constantCoeff (R := k)) constantCoeff_surj a ≠ 0 := by
  rw [teichmullerSection_eq_C]
  exact fun h ↦ ha (C_injective (by simpa using h))

example (a : k) :
    RingHom.teichmullerSectionRingHom p (constantCoeff (R := k)) constantCoeff_surj a = C a := by
  rw [RingHom.teichmullerSectionRingHom_apply, teichmullerSection_eq_C]
  rfl

end PowerSeries

section InfiniteResidue

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- All of these inputs are supplied independently by the algebraic closure.
noncomputable example : Field (AlgebraicClosure (ZMod 3)) := inferInstance
example : Infinite (AlgebraicClosure (ZMod 3)) := inferInstance
example : CharP (AlgebraicClosure (ZMod 3)) 3 := inferInstance
example : PerfectRing (AlgebraicClosure (ZMod 3)) 3 := inferInstance

example : RingHom.teichmullerSectionRingHom 3
    (constantCoeff (R := AlgebraicClosure (ZMod 3))) constantCoeff_surj 1 =
      (1 : (AlgebraicClosure (ZMod 3))⟦X⟧) :=
  map_one _

end InfiniteResidue
