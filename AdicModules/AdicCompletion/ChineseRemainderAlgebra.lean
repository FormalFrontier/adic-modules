/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.ChangeIdealAlgebra
public import AdicModules.AdicCompletion.ChineseRemainder
public import Mathlib.Algebra.Algebra.Tower

/-!
# Chinese remainders for completed algebras

For a finite selection of pairwise comaximal ideals of a commutative ring `A`,
completion at their product is the product of their completions as an `A`-algebra.
The algebra equivalence has exactly the underlying linear equivalence
`AdicCompletion.equivPiOfPairwiseSupEqTop`; its forward coordinates are the
inclusion-induced algebra homomorphisms.

The stock `AlgEquiv.restrictScalars` also gives the equivalence over an independent
commutative ring acting on `A`, with the original completion and Pi actions.

## References

This construction uses Mathlib's algebra homomorphism bundling and scalar
restriction APIs and the module Chinese remainder equivalence in
`AdicModules.AdicCompletion.ChineseRemainder`. It does not require a new quotient
or inverse-limit Chinese remainder construction.
-/

@[expose] public section

noncomputable section

universe u v w

namespace AdicCompletion

variable (A : Type u) [CommRing A]
variable {ι : Type w} (I : ι → Ideal A) (s : Finset ι)
variable (hI : (s : Set ι).Pairwise (fun i j => I i ⊔ I j = ⊤))

/-- Completion at a finite product of pairwise comaximal ideals is the product
of their completions, as an algebra over the original ring. -/
def algEquivPiOfPairwiseSupEqTop :
    AdicCompletion (∏ i ∈ s, I i) A ≃ₐ[A] ((i : s) → AdicCompletion (I i.1) A) :=
  AlgEquiv.ofBijective
    (AlgHom.pi (fun i : s => mapOfLEₐ A (Ideal.prod_le_inf.trans (Finset.inf_le i.2))))
    (by exact (equivPiOfPairwiseSupEqTop A I s hI).bijective)

/-- The forward algebra homomorphism is the product of the inclusion maps. -/
@[simp]
theorem algEquivPiOfPairwiseSupEqTop_toAlgHom :
    (algEquivPiOfPairwiseSupEqTop A I s hI).toAlgHom =
      AlgHom.pi (fun i : s => mapOfLEₐ A (Ideal.prod_le_inf.trans (Finset.inf_le i.2))) :=
  rfl

/-- The underlying linear equivalence is the module Chinese remainder equivalence. -/
@[simp]
theorem algEquivPiOfPairwiseSupEqTop_toLinearEquiv :
    (algEquivPiOfPairwiseSupEqTop A I s hI).toLinearEquiv =
      equivPiOfPairwiseSupEqTop A I s hI := by
  apply LinearEquiv.ext
  intro x
  rfl

/-- The underlying linear map is the product of the original linear inclusion maps. -/
@[simp]
theorem algEquivPiOfPairwiseSupEqTop_toLinearMap :
    (algEquivPiOfPairwiseSupEqTop A I s hI).toLinearMap =
      LinearMap.pi (fun i : s => mapOfLE A (Ideal.prod_le_inf.trans (Finset.inf_le i.2))) :=
  rfl

/-- The inverse has exactly the underlying inverse module equivalence. -/
theorem algEquivPiOfPairwiseSupEqTop_symm_toLinearEquiv :
    (algEquivPiOfPairwiseSupEqTop A I s hI).symm.toLinearEquiv =
      (equivPiOfPairwiseSupEqTop A I s hI).symm := by
  rw [AlgEquiv.toLinearEquiv_symm, algEquivPiOfPairwiseSupEqTop_toLinearEquiv]

/-- Each forward coordinate is the inclusion-induced algebra map. -/
@[simp]
theorem algEquivPiOfPairwiseSupEqTop_apply
    (x : AdicCompletion (∏ i ∈ s, I i) A) (i : s) :
    algEquivPiOfPairwiseSupEqTop A I s hI x i =
      mapOfLEₐ A (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) x := rfl

/-- At every precision, a forward coordinate is the canonical ideal-quotient factor. -/
theorem algEquivPiOfPairwiseSupEqTop_evalₐ
    (x : AdicCompletion (∏ i ∈ s, I i) A) (i : s) (n : ℕ) :
    evalₐ (I i.1) n (algEquivPiOfPairwiseSupEqTop A I s hI x i) =
      Ideal.Quotient.factorₐ A
        (Ideal.pow_right_mono (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) n)
        (evalₐ (∏ i ∈ s, I i) n x) :=
  mapOfLEₐ_evalₐ A (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) n x

/-- The same coordinate formula in the original module quotient presentation. -/
theorem algEquivPiOfPairwiseSupEqTop_eval
    (x : AdicCompletion (∏ i ∈ s, I i) A) (i : s) (n : ℕ) :
    eval (I i.1) A n (algEquivPiOfPairwiseSupEqTop A I s hI x i) =
      Submodule.factor (Submodule.smul_mono_left
        (Ideal.pow_right_mono (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) n))
        (eval (∏ i ∈ s, I i) A n x) :=
  mapOfLEₐ_eval A (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) n x

/-- Canonical images decompose diagonally. -/
@[simp]
theorem algEquivPiOfPairwiseSupEqTop_of (a : A) :
    algEquivPiOfPairwiseSupEqTop A I s hI (of (∏ i ∈ s, I i) A a) =
      fun i : s => of (I i.1) A a := by
  funext i
  exact mapOfLEₐ_of A (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) a

/-- Inclusion into a component recovers that component of the inverse tuple. -/
@[simp]
theorem algEquivPiOfPairwiseSupEqTop_symm_apply
    (y : (i : s) → AdicCompletion (I i.1) A) (i : s) :
    mapOfLEₐ A (Ideal.prod_le_inf.trans (Finset.inf_le i.2))
        ((algEquivPiOfPairwiseSupEqTop A I s hI).symm y) = y i :=
  congrFun ((algEquivPiOfPairwiseSupEqTop A I s hI).apply_symm_apply y) i

/-- A diagonal tuple of canonical images has the expected inverse. -/
@[simp]
theorem algEquivPiOfPairwiseSupEqTop_symm_of (a : A) :
    (algEquivPiOfPairwiseSupEqTop A I s hI).symm (fun i : s => of (I i.1) A a) =
      of (∏ i ∈ s, I i) A a := by
  apply (algEquivPiOfPairwiseSupEqTop A I s hI).injective
  rw [AlgEquiv.apply_symm_apply, algEquivPiOfPairwiseSupEqTop_of]

private theorem evalₐ_eq_mk_iff (J : Ideal A) (n : ℕ) (x : AdicCompletion J A) (a : A) :
    evalₐ J n x = Ideal.Quotient.mk (J ^ n) a ↔
      eval J A n x = Submodule.Quotient.mk a := by
  have h : (J ^ n • ⊤ : Ideal A) = J ^ n := by simp
  constructor
  · intro hx
    rw [← factor_evalₐ_eq_eval J x h.symm.le, hx]
    rfl
  · intro hx
    rw [← factor_eval_eq_evalₐ J x h.le, hx]
    rfl

/-- The inverse residue is represented by `a` exactly when all component residues
are represented by `a`. This includes precision zero. -/
theorem algEquivPiOfPairwiseSupEqTop_symm_evalₐ_eq_mk_iff
    (y : (i : s) → AdicCompletion (I i.1) A) (n : ℕ) (a : A) :
    evalₐ (∏ i ∈ s, I i) n ((algEquivPiOfPairwiseSupEqTop A I s hI).symm y) =
        Ideal.Quotient.mk ((∏ i ∈ s, I i) ^ n) a ↔
      ∀ i : s, evalₐ (I i.1) n (y i) = Ideal.Quotient.mk (I i.1 ^ n) a := by
  simp only [evalₐ_eq_mk_iff]
  have hsymm : (algEquivPiOfPairwiseSupEqTop A I s hI).symm y =
      (equivPiOfPairwiseSupEqTop A I s hI).symm y :=
    LinearEquiv.congr_fun (algEquivPiOfPairwiseSupEqTop_symm_toLinearEquiv A I s hI) y
  rw [hsymm]
  exact equivPiOfPairwiseSupEqTop_symm_eval_eq_mk_iff A I s hI y n a

/-- Scalar restriction preserves the original module equivalence and its actions. -/
theorem algEquivPiOfPairwiseSupEqTop_restrictScalars_toLinearEquiv
    (S : Type v) [CommRing S] [Algebra S A] :
    ((algEquivPiOfPairwiseSupEqTop A I s hI).restrictScalars S).toLinearEquiv =
      (equivPiOfPairwiseSupEqTop A I s hI).restrictScalars S := by
  rw [AlgEquiv.toLinearEquiv_restrictScalars,
    algEquivPiOfPairwiseSupEqTop_toLinearEquiv]

/-- Over an independent scalar ring the forward map is still the product of the
stock scalar restrictions of the inclusion maps. -/
theorem algEquivPiOfPairwiseSupEqTop_restrictScalars_toAlgHom
    (S : Type v) [CommRing S] [Algebra S A] :
    ((algEquivPiOfPairwiseSupEqTop A I s hI).restrictScalars S).toAlgHom =
      AlgHom.pi (fun i : s =>
        (mapOfLEₐ A (Ideal.prod_le_inf.trans (Finset.inf_le i.2))).restrictScalars S) := by
  apply AlgHom.ext
  intro x
  rfl

end AdicCompletion
