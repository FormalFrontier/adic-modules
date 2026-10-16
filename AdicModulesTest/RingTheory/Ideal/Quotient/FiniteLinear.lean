/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.Ideal.Quotient.Finite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The canonical linear Chinese remainder equivalence over the integers

For the ideals spanned by `2` and `3`, the public linear equivalence sends
`[8]` to `([0], [2])` and `2 • [8]` to `(2 • [0], 2 • [2])`. Both sides
use the quotient module actions of the common base ring `ℤ`.

## References

The common-base linear CRT and its characteristic identities come from
`AdicModules.RingTheory.Ideal.Quotient.Finite`, using Mathlib's canonical quotient
and Pi module actions. Integer quotient arithmetic supplies the `[8]` and
scalar-multiple calculations.
-/

universe u v

namespace Ideal

section CharacteristicPropositions

variable {R : Type u} {ι : Type v} [Ring R] [Finite ι]
  (I : ι → Ideal R) [∀ i, (I i).IsTwoSided]
  (hI : Pairwise (fun i j => I i ⊔ I j = ⊤))

-- Characteristic propositions for the canonical linear Chinese remainder equivalence.
private def linearEquivToEquivGoal : Prop :=
  (quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI).toEquiv =
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).toEquiv

private def linearEquivToAddEquivGoal : Prop :=
  (quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI).toAddEquiv =
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).toAddEquiv

private def linearEquivCoeGoal : Prop :=
  (⇑(quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI) :
      (R ⧸ ⨅ i, I i) → ((i : ι) → R ⧸ I i)) =
    ⇑(quotientInfToPiQuotient I)

private def linearEquivApplyGoal : Prop :=
  ∀ z : R ⧸ ⨅ i, I i,
    quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI z =
      quotientInfToPiQuotient I z

private def linearEquivComponentGoal : Prop :=
  ∀ (z : R ⧸ ⨅ i, I i) (i : ι),
    quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI z i =
      Quotient.factor (iInf_le I i) z

private def linearEquivMkGoal : Prop :=
  ∀ r : R, quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI
      (Quotient.mk (⨅ i, I i) r) = fun i => Quotient.mk (I i) r

private def linearEquivSmulGoal : Prop :=
  ∀ (r : R) (z : R ⧸ ⨅ i, I i),
    quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI (r • z) =
      r • quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI z

private theorem linearEquiv_toEquiv : linearEquivToEquivGoal I hI :=
  quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_toEquiv I hI

private theorem linearEquiv_toAddEquiv : linearEquivToAddEquivGoal I hI :=
  quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_toAddEquiv I hI

private theorem linearEquiv_coe : linearEquivCoeGoal I hI :=
  coe_quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI

private theorem linearEquiv_apply : linearEquivApplyGoal I hI :=
  quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_apply I hI

private theorem linearEquiv_component : linearEquivComponentGoal I hI :=
  quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_apply_apply I hI

private theorem linearEquiv_mk : linearEquivMkGoal I hI :=
  quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_mk I hI

private theorem linearEquiv_smul : linearEquivSmulGoal I hI :=
  quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_smul I hI

private theorem linearEquiv_symm_apply (g : (i : ι) → R ⧸ I i) :
    (quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI).symm g =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g :=
  quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_symm_apply I hI g

end CharacteristicPropositions

section Integers

private def moduli : Fin 2 → ℤ := ![2, 3]
private def residues : Fin 2 → ℤ := ![0, 2]
private def integerIdeals (i : Fin 2) : Ideal ℤ := Ideal.span {moduli i}

private theorem moduli_coprime : Pairwise (fun i j => IsCoprime (moduli i) (moduli j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact ⟨-1, 1, by norm_num [moduli]⟩
  · exact ⟨1, -1, by norm_num [moduli]⟩
  · exact (hij rfl).elim

private theorem integerIdeals_pairwise_sup_eq_top :
    Pairwise (fun i j => integerIdeals i ⊔ integerIdeals j = ⊤) := by
  intro i j hij
  exact Ideal.isCoprime_iff_sup_eq.mp
    ((Ideal.isCoprime_span_singleton_iff (moduli i) (moduli j)).mpr (moduli_coprime hij))

private noncomputable def integerLinearEquiv :
    (ℤ ⧸ ⨅ i, integerIdeals i) ≃ₗ[ℤ] ((i : Fin 2) → ℤ ⧸ integerIdeals i) :=
  quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop
    integerIdeals integerIdeals_pairwise_sup_eq_top

private theorem integerLinearEquiv_toEquiv :
    integerLinearEquiv.toEquiv =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop
        integerIdeals integerIdeals_pairwise_sup_eq_top).toEquiv :=
  rfl

private theorem integerLinearEquiv_toAddEquiv :
    integerLinearEquiv.toAddEquiv =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop
        integerIdeals integerIdeals_pairwise_sup_eq_top).toAddEquiv :=
  rfl

private theorem forward_eight :
    integerLinearEquiv (Quotient.mk (⨅ i, integerIdeals i) 8) =
      fun i => Quotient.mk (integerIdeals i) (residues i) := by
  change quotientInfRingEquivPiQuotientOfPairwiseSupEqTop
    integerIdeals integerIdeals_pairwise_sup_eq_top
    (Quotient.mk (⨅ i, integerIdeals i) 8) = _
  rw [quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_mk]
  funext i
  apply (Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [integerIdeals, Ideal.mem_span_singleton]
  fin_cases i <;> norm_num [moduli, residues]

private theorem scalar_two_eight :
    integerLinearEquiv ((2 : ℤ) • Quotient.mk (⨅ i, integerIdeals i) 8) =
      fun i => (2 : ℤ) • Quotient.mk (integerIdeals i) (residues i) := by
  rw [map_smul, forward_eight]
  rfl

private theorem additive_scalar_two_eight :
    integerLinearEquiv.toAddEquiv ((2 : ℤ) • Quotient.mk (⨅ i, integerIdeals i) 8) =
      (2 : ℤ) • (fun i => Quotient.mk (integerIdeals i) (residues i)) := by
  change integerLinearEquiv ((2 : ℤ) • Quotient.mk (⨅ i, integerIdeals i) 8) = _
  rw [map_smul, forward_eight]

end Integers

end Ideal
