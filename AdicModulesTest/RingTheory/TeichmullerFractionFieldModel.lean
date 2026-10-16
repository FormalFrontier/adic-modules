/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.TeichmullerFractionField
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum
meta import Lean.Elab.Tactic.Omega

/-!
# Fraction-field inputs and independent boundary models

The mixed-characteristic input is `ℤ_[3] ⊆ ℚ_[3]`. The equal-characteristic
input is `κ⟦X⟧ ⊆ κ⸨X⸩` for the infinite, imperfect field
`κ = (ZMod 3)⸨X⸩`. Both use their canonical algebra maps, maximal ideals,
residue fields, and fraction-field instances. Completeness is required only
for the valuation rings.

All input rows, the noncube obstruction in the residue field, and the roots
of zero and minus one are established independently of the image laws.
Only the final consumer checks invoke those laws.
-/

set_option linter.privateModule false

namespace TeichmullerFractionFieldModel

noncomputable section

private instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

namespace Padic

private abbrev R := ℤ_[3]
private abbrev K := ℚ_[3]
private abbrev I : Ideal R := IsLocalRing.maximalIdeal R

private noncomputable def residueEquiv : R ⧸ I ≃+* ZMod 3 := PadicInt.residueField

private instance residueCharP : CharP (R ⧸ I) 3 :=
  charP_of_injective_ringHom (f := residueEquiv.symm.toRingHom) residueEquiv.symm.injective 3

private instance quotientField : Field (R ⧸ I) := Ideal.Quotient.field I

private noncomputable abbrev ringInput : CommRing R := inferInstance
private theorem domainInput : IsDomain R := inferInstance
private theorem valuationInput : ValuationRing R := inferInstance
private theorem maximalInput : I.IsMaximal := inferInstance
private theorem completeInput : IsAdicComplete I R := inferInstance
private theorem characteristicInput : CharP (R ⧸ I) 3 := inferInstance
private noncomputable abbrev residueFieldInput : Field (R ⧸ I) := inferInstance
private noncomputable abbrev fractionFieldInput : Field K := inferInstance
private noncomputable abbrev algebraInput : Algebra R K := inferInstance
private theorem fractionInput : IsFractionRing R K := inferInstance
private noncomputable abbrev perfectionFieldInput : Field (Perfection (R ⧸ I) 3) := inferInstance

private theorem perfection_commRing_coherence :
    (inferInstance : Field (Perfection (R ⧸ I) 3)).toCommRing =
      (inferInstance : CommRing (Perfection (R ⧸ I) 3)) := rfl

private noncomputable def dataMap : Perfection (R ⧸ I) 3 →*₀ K :=
  (algebraMap R K).toMonoidWithZeroHom.comp (Perfection.teichmuller₀ 3 I)

private theorem dataMap_apply (a : Perfection (R ⧸ I) 3) :
    dataMap a = algebraMap R K (Perfection.teichmuller₀ 3 I a) := rfl

private theorem minus_one_ne_zero : (-1 : K) ≠ 0 := by simp
private theorem minus_one_ne_one : (-1 : K) ≠ 1 := by norm_num

private theorem zero_roots (n : ℕ) : ∃ y : K, y ^ (3 ^ n) = 0 :=
  ⟨0, zero_pow (pow_ne_zero n (by decide))⟩

private theorem minus_one_roots (n : ℕ) : ∃ y : K, y ^ (3 ^ n) = -1 :=
  ⟨-1, Odd.neg_one_pow (α := K) ((by decide : Odd (3 : ℕ)).pow (n := n))⟩

private theorem range_consumer :
    Set.range dataMap = ⋂ n : ℕ, Set.range (fun y : K ↦ y ^ (3 ^ n)) :=
  Perfection.range_algebraMap_comp_teichmuller₀ 3 I K

private theorem membership_consumer (x : K) :
    x ∈ Set.range dataMap ↔ ∀ n : ℕ, ∃ y : K, y ^ (3 ^ n) = x :=
  Perfection.mem_range_algebraMap_comp_teichmuller₀_iff 3 I K x

end Padic

namespace Imperfect

private abbrev κ := LaurentSeries (ZMod 3)
private abbrev R := PowerSeries κ
private abbrev K := LaurentSeries κ
private abbrev I : Ideal R := IsLocalRing.maximalIdeal R

private instance coefficientCharP : CharP κ 3 :=
  ((HahnSeries.C : ZMod 3 →+* κ).charP_iff_charP 3).mp inferInstance

private noncomputable def residueEquiv : R ⧸ I ≃+* κ :=
  PowerSeries.residueFieldOfPowerSeries

private instance residueCharP : CharP (R ⧸ I) 3 :=
  charP_of_injective_ringHom (f := residueEquiv.symm.toRingHom) residueEquiv.symm.injective 3

private instance ringComplete : IsAdicComplete I R := by
  change IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries κ)) (PowerSeries κ)
  rw [PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

private instance quotientField : Field (R ⧸ I) := Ideal.Quotient.field I

private noncomputable abbrev ringInput : CommRing R := inferInstance
private theorem domainInput : IsDomain R := inferInstance
private theorem valuationInput : ValuationRing R := inferInstance
private theorem maximalInput : I.IsMaximal := inferInstance
private theorem completeInput : IsAdicComplete I R := inferInstance
private theorem characteristicInput : CharP (R ⧸ I) 3 := inferInstance
private noncomputable abbrev residueFieldInput : Field (R ⧸ I) := inferInstance
private noncomputable abbrev fractionFieldInput : Field K := inferInstance
private noncomputable abbrev algebraInput : Algebra R K := inferInstance
private theorem fractionInput : IsFractionRing R K := inferInstance
private noncomputable abbrev perfectionFieldInput : Field (Perfection (R ⧸ I) 3) := inferInstance

private theorem perfection_commRing_coherence :
    (inferInstance : Field (Perfection (R ⧸ I) 3)).toCommRing =
      (inferInstance : CommRing (Perfection (R ⧸ I) 3)) := rfl

private noncomputable def dataMap : Perfection (R ⧸ I) 3 →*₀ K :=
  (algebraMap R K).toMonoidWithZeroHom.comp (Perfection.teichmuller₀ 3 I)

private theorem dataMap_apply (a : Perfection (R ⧸ I) 3) :
    dataMap a = algebraMap R K (Perfection.teichmuller₀ 3 I a) := rfl

private def innerX : κ := HahnSeries.single 1 1

private theorem innerX_not_cube (y : κ) : y ^ 3 ≠ innerX := by
  intro h
  have ho := congrArg HahnSeries.order h
  simp only [HahnSeries.order_pow, innerX, HahnSeries.order_single one_ne_zero,
    nsmul_eq_mul] at ho
  omega

private theorem coefficient_imperfect : ¬ PerfectRing κ 3 := by
  intro h
  let := h
  obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := κ) (p := 3)).surjective innerX
  exact innerX_not_cube y hy

private instance coefficientInfinite : Infinite κ :=
  Infinite.of_injective (fun n : ℕ ↦ (HahnSeries.single (n : ℤ) 1 : κ)) (by
    intro a b h
    have he : (a : ℤ) = (b : ℤ) := by
      simpa only [HahnSeries.order_single one_ne_zero] using congrArg HahnSeries.order h
    exact Int.ofNat.inj he)

private theorem residue_imperfect : ¬ PerfectRing (R ⧸ I) 3 := by
  intro h
  let := h
  obtain ⟨y, hy⟩ :=
    (PerfectRing.bijective_frobenius (R := R ⧸ I) (p := 3)).surjective
      (residueEquiv.symm innerX)
  apply innerX_not_cube (residueEquiv y)
  simpa only [map_pow, RingEquiv.apply_symm_apply] using congrArg residueEquiv hy

private theorem residue_infinite : Infinite (R ⧸ I) :=
  Infinite.of_surjective residueEquiv residueEquiv.surjective

private theorem minus_one_ne_zero : (-1 : K) ≠ 0 := by simp
private theorem minus_one_ne_one : (-1 : K) ≠ 1 := by
  intro h
  have he := congrArg (fun f : K ↦ f.coeff 0) h
  have hc : (-1 : κ) = 1 := by simpa using he
  have hz := congrArg (fun f : κ ↦ f.coeff 0) hc
  have hzz : (-1 : ZMod 3) = 1 := by
    simpa [HahnSeries.coeff_neg, HahnSeries.coeff_one] using hz
  exact (by decide : (-1 : ZMod 3) ≠ 1) hzz

private theorem zero_roots (n : ℕ) : ∃ y : K, y ^ (3 ^ n) = 0 :=
  ⟨0, zero_pow (pow_ne_zero n (by decide))⟩

private theorem minus_one_roots (n : ℕ) : ∃ y : K, y ^ (3 ^ n) = -1 :=
  ⟨-1, Odd.neg_one_pow (α := K) ((by decide : Odd (3 : ℕ)).pow (n := n))⟩

private theorem range_consumer :
    Set.range dataMap = ⋂ n : ℕ, Set.range (fun y : K ↦ y ^ (3 ^ n)) :=
  Perfection.range_algebraMap_comp_teichmuller₀ 3 I K

private theorem membership_consumer (x : K) :
    x ∈ Set.range dataMap ↔ ∀ n : ℕ, ∃ y : K, y ^ (3 ^ n) = x :=
  Perfection.mem_range_algebraMap_comp_teichmuller₀_iff 3 I K x

end Imperfect

end

end TeichmullerFractionFieldModel
