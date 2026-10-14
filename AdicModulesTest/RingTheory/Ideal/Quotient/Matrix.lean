/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Ring.Pi
import Mathlib.LinearAlgebra.Matrix.Ideal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Two-sided congruences in integer matrix rings

For the three coordinate kernels in `(M₂(ℤ))³`, the first isomorphism theorem
identifies each quotient with its matrix coordinate. Their intersection is zero.
Combining these identifications with the quotient by zero gives a ring equivalence
whose forward map is the diagonal quotient map. Its underlying additive equivalence
preserves the canonical left action of the tuple ring on the quotient modules.
The action on a matrix coordinate is restriction along evaluation.

The entry ideals `2M₂(ℤ)`, `3M₂(ℤ)`, and `5M₂(ℤ)` give a different example:
the first two squares are strictly smaller than the original ideals. At precision
`(2, 2, 1)`, the noncentral residues `(0, E₀₀, E₀₁)` have the solution
`100E₀₀ + 36E₀₁`. Membership in the two squares is witnessed by products of two
members of the corresponding entry ideal. Exponent zero gives the top ideal and
the zero quotient, without an additional positivity convention.

All carriers, quotient rings, and module actions here come from Mathlib. The
matrix entry ideals use `Ideal.matrix`; their two-sidedness is transported from
`TwoSidedIdeal.matrix` and `TwoSidedIdeal.asIdeal`. These examples do not assert
an arbitrary-ring Chinese remainder construction or an arbitrary-power formula
for matrix entry ideals.
-/

namespace Ideal

private abbrev IntMatrix := Matrix (Fin 2) (Fin 2) ℤ
private abbrev MatrixTuple := Fin 3 → IntMatrix

private def e00 : IntMatrix := Matrix.single 0 0 1
private def e01 : IntMatrix := Matrix.single 0 1 1
private def e10 : IntMatrix := Matrix.single 1 0 1

private lemma e01_ne_zero : e01 ≠ 0 := by
  intro h
  have h01 := congrArg (fun A : IntMatrix ↦ A 0 1) h
  norm_num [e01, Matrix.single_apply] at h01

private theorem matrix_units_noncommute : e00 * e01 ≠ e01 * e00 := by
  have hleft : e00 * e01 = e01 := by
    simp [e00, e01, Matrix.single_mul_single_same]
  have hright : e01 * e00 = 0 := by
    simp [e00, e01, Matrix.single_mul_single_of_ne]
  rw [hleft, hright]
  exact e01_ne_zero

private theorem matrix_tuples_noncommute :
    (fun _ : Fin 3 ↦ e00) * (fun _ : Fin 3 ↦ e01) ≠
      (fun _ : Fin 3 ↦ e01) * (fun _ : Fin 3 ↦ e00) := by
  intro h
  exact matrix_units_noncommute (congrArg (fun x : MatrixTuple ↦ x 0) h)

section CoordinateKernels

private def coordinateEval (i : Fin 3) : MatrixTuple →+* IntMatrix :=
  Pi.evalRingHom (fun _ : Fin 3 ↦ IntMatrix) i

private def coordinateIdeal (i : Fin 3) : Ideal MatrixTuple :=
  RingHom.ker (coordinateEval i)

private instance coordinateIdeal_twoSided (i : Fin 3) :
    (coordinateIdeal i).IsTwoSided := by
  unfold coordinateIdeal
  infer_instance

private lemma mem_coordinateIdeal (i : Fin 3) (x : MatrixTuple) :
    x ∈ coordinateIdeal i ↔ x i = 0 := by
  change x ∈ RingHom.ker (coordinateEval i) ↔ _
  rw [RingHom.mem_ker]
  rfl

private lemma coordinateIdeal_nonzero_of_ne (i j : Fin 3) (hij : i ≠ j) :
    coordinateIdeal i ≠ ⊥ := by
  have hm : Pi.single j (1 : IntMatrix) ∈ coordinateIdeal i := by
    rw [mem_coordinateIdeal]
    simp [Pi.single_apply, hij, hij.symm]
  intro hbot
  have hz : (Pi.single j (1 : IntMatrix) : MatrixTuple) = 0 := by
    simpa only [hbot, Submodule.mem_bot] using hm
  have hj := congrArg (fun x : MatrixTuple ↦ x j) hz
  have hone : (1 : IntMatrix) = 0 := by simpa using hj
  exact one_ne_zero hone

private theorem coordinateIdeals_nonzero_proper (i : Fin 3) :
    coordinateIdeal i ≠ ⊥ ∧ coordinateIdeal i ≠ ⊤ := by
  constructor
  · fin_cases i
    · exact coordinateIdeal_nonzero_of_ne 0 1 (by decide)
    · exact coordinateIdeal_nonzero_of_ne 1 0 (by decide)
    · exact coordinateIdeal_nonzero_of_ne 2 0 (by decide)
  · exact RingHom.ker_ne_top (coordinateEval i)

private theorem coordinateIdeals_pairwise_comaximal :
    Pairwise (fun i j : Fin 3 ↦ coordinateIdeal i ⊔ coordinateIdeal j = ⊤) := by
  intro i j hij
  apply (Ideal.eq_top_iff_one _).mpr
  apply Submodule.mem_sup.mpr
  refine ⟨Pi.single j (1 : IntMatrix), ?_, 1 - Pi.single j (1 : IntMatrix), ?_, ?_⟩
  · rw [mem_coordinateIdeal]
    simp [Pi.single_apply, hij, hij.symm]
  · rw [mem_coordinateIdeal]
    simp
  · rw [add_comm, sub_add_cancel]

private lemma coordinateIdeals_iInf : (⨅ i, coordinateIdeal i) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  apply Ideal.mem_bot.mpr
  apply funext
  intro i
  exact (mem_coordinateIdeal i x).mp (Ideal.mem_iInf.mp hx i)

private lemma coordinateIdeal_mul_self (i : Fin 3) :
    coordinateIdeal i * coordinateIdeal i = coordinateIdeal i := by
  apply le_antisymm Ideal.mul_le_right
  intro x hx
  have hi : x i = 0 := (mem_coordinateIdeal i x).mp hx
  have he : 1 - Pi.single i (1 : IntMatrix) ∈ coordinateIdeal i := by
    rw [mem_coordinateIdeal]
    simp
  have hmul : x * (1 - Pi.single i (1 : IntMatrix)) = x := by
    apply funext
    intro j
    by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [Pi.single_apply, hji]
  rw [← hmul]
  exact Ideal.mul_mem_mul hx he

private theorem coordinateIdeal_pow_succ (i : Fin 3) (n : ℕ) :
    coordinateIdeal i ^ (n + 1) = coordinateIdeal i := by
  induction n with
  | zero => exact Submodule.pow_one _
  | succ n ih => rw [Submodule.pow_succ, ih, coordinateIdeal_mul_self]

private noncomputable def coordinateEquiv (i : Fin 3) :
    (MatrixTuple ⧸ coordinateIdeal i) ≃+* IntMatrix :=
  (coordinateEval i).quotientKerEquivOfSurjective
    (Pi.evalRingHom (fun _ : Fin 3 ↦ IntMatrix) i).surjective

private lemma coordinateEquiv_mk (i : Fin 3) (x : MatrixTuple) :
    coordinateEquiv i (Ideal.Quotient.mk (coordinateIdeal i) x) = x i := by
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ x

private lemma coordinateEquiv_smul (i : Fin 3) (r : MatrixTuple)
    (q : MatrixTuple ⧸ coordinateIdeal i) :
    coordinateEquiv i (r • q) =
      @SMul.smul MatrixTuple IntMatrix
        (coordinateEval i).toModule.toDistribMulAction.toMulAction.toSMul
        r (coordinateEquiv i q) := by
  letI := (coordinateEval i).toModule
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hmk : r • Ideal.Quotient.mk (coordinateIdeal i) x =
      Ideal.Quotient.mk (coordinateIdeal i) (r * x) := rfl
  rw [hmk, coordinateEquiv_mk, coordinateEquiv_mk]
  rfl

private noncomputable def coordinateLinearEquiv (i : Fin 3) :
    letI := (coordinateEval i).toModule
    (MatrixTuple ⧸ coordinateIdeal i) ≃ₗ[MatrixTuple] IntMatrix := by
  letI := (coordinateEval i).toModule
  exact (coordinateEquiv i).toAddEquiv.toLinearEquiv (coordinateEquiv_smul i)

private lemma coordinateLinearEquiv_apply (i : Fin 3)
    (q : MatrixTuple ⧸ coordinateIdeal i) :
    (coordinateLinearEquiv i).toEquiv q = coordinateEquiv i q := rfl

private noncomputable def coordinateModelEquiv :
    (MatrixTuple ⧸ ⨅ i, coordinateIdeal i) ≃+*
      ((i : Fin 3) → MatrixTuple ⧸ coordinateIdeal i) :=
  ((Ideal.quotEquivOfEq coordinateIdeals_iInf).trans
    (RingEquiv.quotientBot MatrixTuple)).trans
      (RingEquiv.piCongrRight coordinateEquiv).symm

private lemma coordinateModelEquiv_mk (x : MatrixTuple) :
    coordinateModelEquiv (Ideal.Quotient.mk (⨅ i, coordinateIdeal i) x) =
      fun i ↦ Ideal.Quotient.mk (coordinateIdeal i) x := by
  ext i
  apply (coordinateEquiv i).injective
  change coordinateEquiv i ((coordinateEquiv i).symm
      ((RingEquiv.quotientBot MatrixTuple
        (Ideal.quotEquivOfEq coordinateIdeals_iInf
          (Ideal.Quotient.mk (⨅ i, coordinateIdeal i) x))) i)) =
    coordinateEquiv i (Ideal.Quotient.mk (coordinateIdeal i) x)
  rw [RingEquiv.apply_symm_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.quotientBot_mk, coordinateEquiv_mk]

private theorem coordinateModelEquiv_agrees
    (q : MatrixTuple ⧸ ⨅ i, coordinateIdeal i) :
    coordinateModelEquiv q = Ideal.quotientInfToPiQuotient coordinateIdeal q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [coordinateModelEquiv_mk, Ideal.quotientInfToPiQuotient_mk]

private theorem coordinateModelEquiv_component (i : Fin 3)
    (q : MatrixTuple ⧸ ⨅ i, coordinateIdeal i) :
    coordinateModelEquiv q i = Ideal.Quotient.factor (iInf_le coordinateIdeal i) q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [coordinateModelEquiv_mk, Ideal.Quotient.factor_mk]

private lemma coordinateModelEquiv_smul (r : MatrixTuple)
    (q : MatrixTuple ⧸ ⨅ i, coordinateIdeal i) :
    coordinateModelEquiv (r • q) =
      @SMul.smul MatrixTuple ((i : Fin 3) → MatrixTuple ⧸ coordinateIdeal i)
        (Pi.module (Fin 3) (fun i ↦ MatrixTuple ⧸ coordinateIdeal i)
          MatrixTuple).toDistribMulAction.toMulAction.toSMul
        r (coordinateModelEquiv q) := by
  letI canonicalModule :
      Module MatrixTuple ((i : Fin 3) → MatrixTuple ⧸ coordinateIdeal i) :=
    Pi.module (Fin 3) (fun i ↦ MatrixTuple ⧸ coordinateIdeal i) MatrixTuple
  letI : SMul MatrixTuple ((i : Fin 3) → MatrixTuple ⧸ coordinateIdeal i) :=
    canonicalModule.toDistribMulAction.toMulAction.toSMul
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hmk : r • Ideal.Quotient.mk (⨅ i, coordinateIdeal i) x =
      Ideal.Quotient.mk (⨅ i, coordinateIdeal i) (r * x) := rfl
  have hcomponents :
      (fun i ↦ Ideal.Quotient.mk (coordinateIdeal i) (r * x)) =
        @SMul.smul MatrixTuple ((i : Fin 3) → MatrixTuple ⧸ coordinateIdeal i)
          canonicalModule.toDistribMulAction.toMulAction.toSMul
          r (fun i ↦ Ideal.Quotient.mk (coordinateIdeal i) x) := by
    apply funext
    intro i
    have hproj :
        (@SMul.smul MatrixTuple ((j : Fin 3) → MatrixTuple ⧸ coordinateIdeal j)
          canonicalModule.toDistribMulAction.toMulAction.toSMul
          r (fun j ↦ Ideal.Quotient.mk (coordinateIdeal j) x)) i =
            r • Ideal.Quotient.mk (coordinateIdeal i) x := by
      simpa only [LinearMap.proj_apply, HSMul.hSMul, SMul.smul,
        DistribMulAction.toDistribSMul] using
        (@LinearMap.map_smul MatrixTuple
          ((j : Fin 3) → MatrixTuple ⧸ coordinateIdeal j)
          (MatrixTuple ⧸ coordinateIdeal i) _ _ _ canonicalModule _
          (LinearMap.proj (R := MatrixTuple)
            (φ := fun j : Fin 3 ↦ MatrixTuple ⧸ coordinateIdeal j) i) r
          (fun j ↦ Ideal.Quotient.mk (coordinateIdeal j) x))
    have hquot :
        Ideal.Quotient.mk (coordinateIdeal i) (r * x) =
          r • Ideal.Quotient.mk (coordinateIdeal i) x := by
      simpa only [Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk, smul_eq_mul] using
        (coordinateIdeal i).mkQ.map_smul r x
    exact hquot.trans hproj.symm
  simpa only [hmk, coordinateModelEquiv_mk] using hcomponents

private noncomputable def coordinateModelLinearEquiv :
    letI : Module MatrixTuple ((i : Fin 3) → MatrixTuple ⧸ coordinateIdeal i) :=
      Pi.module (Fin 3) (fun i ↦ MatrixTuple ⧸ coordinateIdeal i) MatrixTuple
    (MatrixTuple ⧸ ⨅ i, coordinateIdeal i) ≃ₗ[MatrixTuple]
      ((i : Fin 3) → MatrixTuple ⧸ coordinateIdeal i) := by
  letI : Module MatrixTuple ((i : Fin 3) → MatrixTuple ⧸ coordinateIdeal i) :=
    Pi.module (Fin 3) (fun i ↦ MatrixTuple ⧸ coordinateIdeal i) MatrixTuple
  exact coordinateModelEquiv.toAddEquiv.toLinearEquiv coordinateModelEquiv_smul

private lemma coordinateModelLinearEquiv_component (i : Fin 3)
    (q : MatrixTuple ⧸ ⨅ i, coordinateIdeal i) :
    coordinateModelLinearEquiv q i = Ideal.Quotient.factor (iInf_le coordinateIdeal i) q :=
  coordinateModelEquiv_component i q

private def prescribedTuple : MatrixTuple := ![e00, e01, e10]

private def coordinateRepresentative (i : Fin 3) : MatrixTuple :=
  Pi.single i (prescribedTuple i)

private theorem prescribedTuple_noncentral :
    (fun _ : Fin 3 ↦ e00) * prescribedTuple ≠
      prescribedTuple * (fun _ : Fin 3 ↦ e00) := by
  intro h
  apply matrix_units_noncommute
  have h1 := congrArg (fun x : MatrixTuple ↦ x 1) h
  simpa [prescribedTuple] using h1

private theorem prescribedTuple_coordinate (i : Fin 3) :
    coordinateEquiv i (Ideal.Quotient.mk (coordinateIdeal i) (coordinateRepresentative i)) =
      prescribedTuple i := by
  rw [coordinateEquiv_mk]
  simp [coordinateRepresentative]

private theorem prescribedTuple_solves (i : Fin 3) :
    prescribedTuple - coordinateRepresentative i ∈ coordinateIdeal i := by
  rw [mem_coordinateIdeal]
  simp [coordinateRepresentative]

private theorem prescribedTuple_quotient_solution :
    coordinateModelEquiv (Ideal.Quotient.mk (⨅ i, coordinateIdeal i) prescribedTuple) =
      fun i ↦ Ideal.Quotient.mk (coordinateIdeal i) (coordinateRepresentative i) := by
  rw [coordinateModelEquiv_mk]
  ext i
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (prescribedTuple_solves i)

private theorem prescribedTuple_inverse :
    coordinateModelEquiv.symm
        (fun i ↦ Ideal.Quotient.mk (coordinateIdeal i) (coordinateRepresentative i)) =
      Ideal.Quotient.mk (⨅ i, coordinateIdeal i) prescribedTuple := by
  apply coordinateModelEquiv.injective
  rw [RingEquiv.apply_symm_apply, prescribedTuple_quotient_solution]

private theorem prescribedTuple_nonzero_class :
    Ideal.Quotient.mk (⨅ i, coordinateIdeal i) prescribedTuple ≠ 0 := by
  intro h
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp h
  have hz : prescribedTuple = 0 := by
    simpa only [coordinateIdeals_iInf, Ideal.mem_bot] using hm
  have h01 := congrArg (fun x : MatrixTuple ↦ x 1) hz
  apply e01_ne_zero
  simpa [prescribedTuple] using h01

private theorem coordinateIdeal_zero_exponent (i : Fin 3) (x : MatrixTuple) :
    Ideal.Quotient.mk (coordinateIdeal i ^ 0) x = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Submodule.pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

end CoordinateKernels

section EntryIdeals

private def entryIdeal (p : ℤ) : Ideal IntMatrix :=
  (Ideal.span {p}).matrix (Fin 2)

private instance entryIdeal_twoSided (p : ℤ) : (entryIdeal p).IsTwoSided := by
  unfold entryIdeal
  rw [← Ideal.asIdeal_toTwoSided (Ideal.span {p}), ← TwoSidedIdeal.asIdeal_matrix]
  infer_instance

private lemma mem_entryIdeal (p : ℤ) (A : IntMatrix) :
    A ∈ entryIdeal p ↔ ∀ i j, p ∣ A i j := by
  simp only [entryIdeal, Ideal.mem_matrix, Ideal.mem_span_singleton]

private lemma scalar_mem_entryIdeal (p a : ℤ) (h : p ∣ a) :
    (a : IntMatrix) ∈ entryIdeal p := by
  rw [mem_entryIdeal]
  intro i j
  rw [Matrix.intCast_apply]
  by_cases hij : i = j
  · rw [if_pos hij]
    exact h
  · rw [if_neg hij]
    exact dvd_zero p

private lemma entryIdeal_nonzero_proper (p : ℤ) (hp : p ≠ 0) (hunit : ¬p ∣ 1) :
    entryIdeal p ≠ ⊥ ∧ entryIdeal p ≠ ⊤ := by
  constructor
  · intro hbot
    have hm := scalar_mem_entryIdeal p p (dvd_refl p)
    have hz : (p : IntMatrix) = 0 := by
      simpa only [hbot, Ideal.mem_bot] using hm
    have h00 := congrArg (fun A : IntMatrix ↦ A 0 0) hz
    exact hp (by simpa [Matrix.intCast_apply] using h00)
  · intro htop
    have hm : (1 : IntMatrix) ∈ entryIdeal p := by
      rw [htop]
      exact Submodule.mem_top
    have h00 := (mem_entryIdeal p 1).mp hm 0 0
    exact hunit (by simpa using h00)

private theorem entryIdeals_nonzero_proper :
    (entryIdeal 2 ≠ ⊥ ∧ entryIdeal 2 ≠ ⊤) ∧
      (entryIdeal 3 ≠ ⊥ ∧ entryIdeal 3 ≠ ⊤) ∧
      (entryIdeal 5 ≠ ⊥ ∧ entryIdeal 5 ≠ ⊤) := by
  exact ⟨entryIdeal_nonzero_proper 2 (by norm_num) (by norm_num),
    entryIdeal_nonzero_proper 3 (by norm_num) (by norm_num),
    entryIdeal_nonzero_proper 5 (by norm_num) (by norm_num)⟩

private theorem entryIdeals_two_three_comaximal : entryIdeal 2 ⊔ entryIdeal 3 = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply Submodule.mem_sup.mpr
  refine ⟨((-2 : ℤ) : IntMatrix), scalar_mem_entryIdeal 2 (-2) (by norm_num),
    ((3 : ℤ) : IntMatrix), scalar_mem_entryIdeal 3 3 (dvd_refl _), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.intCast_apply, Matrix.ofNat_apply]

private theorem entryIdeals_two_five_comaximal : entryIdeal 2 ⊔ entryIdeal 5 = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply Submodule.mem_sup.mpr
  refine ⟨((6 : ℤ) : IntMatrix), scalar_mem_entryIdeal 2 6 (by norm_num),
    ((-5 : ℤ) : IntMatrix), scalar_mem_entryIdeal 5 (-5) (by norm_num), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.intCast_apply, Matrix.ofNat_apply]

private theorem entryIdeals_three_five_comaximal : entryIdeal 3 ⊔ entryIdeal 5 = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply Submodule.mem_sup.mpr
  refine ⟨((6 : ℤ) : IntMatrix), scalar_mem_entryIdeal 3 6 (by norm_num),
    ((-5 : ℤ) : IntMatrix), scalar_mem_entryIdeal 5 (-5) (by norm_num), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.intCast_apply, Matrix.ofNat_apply]

private def entryIdealFamily : Fin 3 → Ideal IntMatrix :=
  ![entryIdeal 2, entryIdeal 3, entryIdeal 5]

private instance entryIdealFamily_twoSided (i : Fin 3) :
    (entryIdealFamily i).IsTwoSided := by
  fin_cases i
  · change (entryIdeal 2).IsTwoSided
    infer_instance
  · change (entryIdeal 3).IsTwoSided
    infer_instance
  · change (entryIdeal 5).IsTwoSided
    infer_instance

private theorem entryIdealFamily_pairwise_comaximal :
    Pairwise (fun i j : Fin 3 ↦ entryIdealFamily i ⊔ entryIdealFamily j = ⊤) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  · exact entryIdeals_two_three_comaximal
  · exact entryIdeals_two_five_comaximal
  · change entryIdeal 3 ⊔ entryIdeal 2 = ⊤
    simpa only [sup_comm] using entryIdeals_two_three_comaximal
  · exact entryIdeals_three_five_comaximal
  · change entryIdeal 5 ⊔ entryIdeal 2 = ⊤
    simpa only [sup_comm] using entryIdeals_two_five_comaximal
  · change entryIdeal 5 ⊔ entryIdeal 3 = ⊤
    simpa only [sup_comm] using entryIdeals_three_five_comaximal

private def matrixSolution : IntMatrix := Matrix.single 0 0 100 + Matrix.single 0 1 36
private def factorTwo : IntMatrix := Matrix.single 0 0 50 + Matrix.single 0 1 18
private def factorThree : IntMatrix := Matrix.single 0 0 33 + Matrix.single 0 1 12

private lemma matrixSolution_eq :
    matrixSolution = (100 : IntMatrix) * e00 + (36 : IntMatrix) * e01 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixSolution, e00, e01, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.single_apply, Matrix.ofNat_apply]

private lemma factorTwo_mem : factorTwo ∈ entryIdeal 2 := by
  rw [mem_entryIdeal]
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [factorTwo, Matrix.single_apply]

private lemma factorThree_mem : factorThree ∈ entryIdeal 3 := by
  rw [mem_entryIdeal]
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [factorThree, Matrix.single_apply]

private lemma factorTwo_product : ((2 : ℤ) : IntMatrix) * factorTwo = matrixSolution := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorTwo, matrixSolution, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.single_apply, Matrix.intCast_apply, Matrix.ofNat_apply]

private lemma factorThree_product :
    ((3 : ℤ) : IntMatrix) * factorThree = matrixSolution - e00 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorThree, matrixSolution, e00, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.single_apply, Matrix.intCast_apply, Matrix.ofNat_apply]

private lemma matrixSolution_mem_two_square : matrixSolution ∈ entryIdeal 2 ^ 2 := by
  rw [Submodule.pow_succ, Submodule.pow_one, ← factorTwo_product]
  exact Ideal.mul_mem_mul (scalar_mem_entryIdeal 2 2 (dvd_refl _)) factorTwo_mem

private lemma matrixSolution_sub_e00_mem_three_square :
    matrixSolution - e00 ∈ entryIdeal 3 ^ 2 := by
  rw [Submodule.pow_succ, Submodule.pow_one, ← factorThree_product]
  exact Ideal.mul_mem_mul (scalar_mem_entryIdeal 3 3 (dvd_refl _)) factorThree_mem

private lemma matrixSolution_sub_e01_mem_five : matrixSolution - e01 ∈ entryIdeal 5 := by
  rw [mem_entryIdeal]
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [matrixSolution, e01, Matrix.single_apply]

private def entryPrecision : Fin 3 → ℕ := ![2, 2, 1]
private def entryResidue : Fin 3 → IntMatrix := ![0, e00, e01]

private theorem matrixSolution_congruences (i : Fin 3) :
    matrixSolution - entryResidue i ∈ entryIdealFamily i ^ entryPrecision i := by
  fin_cases i
  · change matrixSolution - 0 ∈ entryIdeal 2 ^ 2
    simpa only [sub_zero] using matrixSolution_mem_two_square
  · change matrixSolution - e00 ∈ entryIdeal 3 ^ 2
    exact matrixSolution_sub_e00_mem_three_square
  · change matrixSolution - e01 ∈ entryIdeal 5 ^ 1
    rw [Submodule.pow_one]
    exact matrixSolution_sub_e01_mem_five

private theorem matrixSolution_quotient_residues (i : Fin 3) :
    Ideal.Quotient.mk (entryIdealFamily i ^ entryPrecision i) matrixSolution =
      Ideal.Quotient.mk (entryIdealFamily i ^ entryPrecision i) (entryResidue i) := by
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (matrixSolution_congruences i)

private theorem matrixSolution_noncentral : matrixSolution * e00 ≠ e00 * matrixSolution := by
  intro h
  have h01 := congrArg (fun A : IntMatrix ↦ A 0 1) h
  norm_num [matrixSolution, e00, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.single_apply] at h01

private lemma two_square_le_four : entryIdeal 2 ^ 2 ≤ entryIdeal 4 := by
  rw [Submodule.pow_succ, Submodule.pow_one]
  apply Ideal.mul_le.mpr
  intro A hA B hB
  rw [mem_entryIdeal]
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.dvd_sum
  intro k _
  have h := mul_dvd_mul ((mem_entryIdeal 2 A).mp hA i k)
    ((mem_entryIdeal 2 B).mp hB k j)
  norm_num at h
  exact h

private lemma three_square_le_nine : entryIdeal 3 ^ 2 ≤ entryIdeal 9 := by
  rw [Submodule.pow_succ, Submodule.pow_one]
  apply Ideal.mul_le.mpr
  intro A hA B hB
  rw [mem_entryIdeal]
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.dvd_sum
  intro k _
  have h := mul_dvd_mul ((mem_entryIdeal 3 A).mp hA i k)
    ((mem_entryIdeal 3 B).mp hB k j)
  norm_num at h
  exact h

private theorem two_square_nonzero_proper : entryIdeal 2 ^ 2 ≠ ⊥ ∧ entryIdeal 2 ^ 2 ≠ ⊤ := by
  constructor
  · intro hbot
    have hz : matrixSolution = 0 := by
      simpa only [hbot, Ideal.mem_bot] using matrixSolution_mem_two_square
    have h00 := congrArg (fun A : IntMatrix ↦ A 0 0) hz
    norm_num [matrixSolution, Matrix.single_apply] at h00
  · intro htop
    have hfour : entryIdeal 4 = ⊤ := top_unique (htop ▸ two_square_le_four)
    exact (entryIdeal_nonzero_proper 4 (by norm_num) (by norm_num)).2 hfour

private theorem three_square_nonzero_proper : entryIdeal 3 ^ 2 ≠ ⊥ ∧ entryIdeal 3 ^ 2 ≠ ⊤ := by
  constructor
  · intro hbot
    have hz : matrixSolution - e00 = 0 := by
      simpa only [hbot, Ideal.mem_bot] using matrixSolution_sub_e00_mem_three_square
    have h00 := congrArg (fun A : IntMatrix ↦ A 0 0) hz
    norm_num [matrixSolution, e00, Matrix.single_apply] at h00
  · intro htop
    have hnine : entryIdeal 9 = ⊤ := top_unique (htop ▸ three_square_le_nine)
    exact (entryIdeal_nonzero_proper 9 (by norm_num) (by norm_num)).2 hnine

private theorem two_square_changes : entryIdeal 2 ^ 2 ≠ entryIdeal 2 := by
  intro h
  have hm := scalar_mem_entryIdeal 2 2 (dvd_refl _)
  rw [← h] at hm
  have h00 := (mem_entryIdeal 4 _).mp (two_square_le_four hm) 0 0
  norm_num [Matrix.intCast_apply] at h00

private theorem three_square_changes : entryIdeal 3 ^ 2 ≠ entryIdeal 3 := by
  intro h
  have hm := scalar_mem_entryIdeal 3 3 (dvd_refl _)
  rw [← h] at hm
  have h00 := (mem_entryIdeal 9 _).mp (three_square_le_nine hm) 0 0
  norm_num [Matrix.intCast_apply] at h00

private theorem entryIdeal_zero_exponent (p : ℤ) (x : IntMatrix) :
    Ideal.Quotient.mk (entryIdeal p ^ 0) x = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Submodule.pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

end EntryIdeals

end Ideal
