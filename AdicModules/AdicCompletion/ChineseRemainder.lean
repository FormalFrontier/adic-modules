/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.ChangeIdeal
public import AdicModules.RingTheory.Ideal.Quotient.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Chinese remainders for adic module completions

Completion at a finite product of pairwise comaximal ideals is the product of the
individual completions, as a module over the original ring. No finiteness condition
on the module or on the generators of the ideals is needed.

## References

The stage construction uses the finite Chinese remainder equivalence, following
Kenny Lau and Patrick Massot's Mathlib formalization, together with Mathlib's
quotient–tensor equivalence of Antoine Chambert-Loir and Jujian Zhang and
Judith Ludwig and Christian Merten's finite product–tensor equivalence.
The inverse limit uses Mathlib's `AdicCompletion.lift`, developed by Kenny Lau,
Judith Ludwig, Christian Merten and Jiedong Jiang.
-/

public section

noncomputable section

universe u v w t

open Submodule TensorProduct

namespace AdicCompletion

variable {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {ι : Type w} (I : ι → Ideal R) (s : Finset ι)
variable (hI : (s : Set ι).Pairwise (fun i j => I i ⊔ I j = ⊤))

include hI

private theorem prod_pow_eq_iInf (n : ℕ) :
    (∏ i ∈ s, I i) ^ n = ⨅ i : s, I i.1 ^ n := by
  rw [← Finset.prod_pow]
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp only [iInf_subtype]
  · intro i hi j hj hij
    exact Ideal.isCoprime_iff_sup_eq.mpr (Ideal.pow_sup_pow_eq_top (hI hi hj hij))

private def stageEquiv (n : ℕ) :
    (M ⧸ ((∏ i ∈ s, I i) ^ n • ⊤ : Submodule R M)) ≃ₗ[R]
      ((i : s) → M ⧸ (I i.1 ^ n • ⊤ : Submodule R M)) := by
  classical
  let e := (Submodule.quotEquivOfEq _ _ (prod_pow_eq_iInf I s hI n)).trans
    (Ideal.quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop
      (fun i : s => I i.1 ^ n) (fun i j hij =>
        Ideal.pow_sup_pow_eq_top (hI i.2 j.2 (fun h => hij (Subtype.ext h)))))
  exact (quotTensorEquivQuotSMul M _).symm ≪≫ₗ
    TensorProduct.congr e (LinearEquiv.refl R M) ≪≫ₗ
    TensorProduct.piLeft R M (fun i : s => R ⧸ I i.1 ^ n) ≪≫ₗ
    LinearEquiv.piCongrRight (fun i => quotTensorEquivQuotSMul M (I i.1 ^ n))

private theorem stageEquiv_mk (n : ℕ) (m : M) :
    stageEquiv M I s hI n (Submodule.Quotient.mk m) =
      fun _ => Submodule.Quotient.mk m := by
  classical
  have h1 : (Submodule.quotEquivOfEq _ _ (prod_pow_eq_iInf I s hI n))
      (1 : R ⧸ (∏ i ∈ s, I i) ^ n) = 1 :=
    Submodule.quotEquivOfEq_mk _ _ _ (1 : R)
  have h2 : Ideal.quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop
      (fun i : s => I i.1 ^ n) (fun i j hij =>
        Ideal.pow_sup_pow_eq_top (hI i.2 j.2 (fun h => hij (Subtype.ext h)))) 1 =
      fun _ => 1 :=
    Ideal.quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_mk _ _ 1
  funext i
  simp [stageEquiv, TensorProduct.piLeft, h1, h2, LinearEquiv.piCongrRight_apply]

private theorem stageEquiv_apply (n : ℕ)
    (x : M ⧸ ((∏ i ∈ s, I i) ^ n • ⊤ : Submodule R M)) (i : s) :
    stageEquiv M I s hI n x i =
      Submodule.factor (Submodule.smul_mono_left
        (Ideal.pow_right_mono (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) n)) x := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [stageEquiv_mk]
  rfl

private theorem stageEquiv_transition {a b : ℕ} (hab : a ≤ b)
    (x : M ⧸ ((∏ i ∈ s, I i) ^ b • ⊤ : Submodule R M)) (i : s) :
    stageEquiv M I s hI a (transitionMap (∏ j ∈ s, I j) M hab x) i =
      transitionMap (I i.1) M hab (stageEquiv M I s hI b x i) := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change stageEquiv M I s hI a (Submodule.Quotient.mk m) i =
    transitionMap (I i.1) M hab (stageEquiv M I s hI b (Submodule.Quotient.mk m) i)
  rw [stageEquiv_mk, stageEquiv_mk]
  rfl

private def inverseStage (n : ℕ) :
    ((i : s) → AdicCompletion (I i.1) M) →ₗ[R]
      M ⧸ ((∏ i ∈ s, I i) ^ n • ⊤ : Submodule R M) :=
  (stageEquiv M I s hI n).symm.toLinearMap.comp
    (LinearMap.pi (fun i => (eval (I i.1) M n).comp (LinearMap.proj i)))

private theorem inverseStage_apply (n : ℕ) (y : (i : s) → AdicCompletion (I i.1) M) :
    inverseStage M I s hI n y =
      (stageEquiv M I s hI n).symm (fun i => eval (I i.1) M n (y i)) := rfl

private theorem inverseStage_compatible {a b : ℕ} (hab : a ≤ b) :
    transitionMap (∏ j ∈ s, I j) M hab ∘ₗ inverseStage M I s hI b =
      inverseStage M I s hI a := by
  apply LinearMap.ext
  intro y
  apply (stageEquiv M I s hI a).injective
  funext i
  rw [LinearMap.comp_apply, stageEquiv_transition]
  simp only [inverseStage, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.pi_apply, LinearMap.proj_apply]
  exact transitionMap_comp_eval_apply (I i.1) M hab (y i)

private def completionEquiv :
    AdicCompletion (∏ i ∈ s, I i) M ≃ₗ[R] ((i : s) → AdicCompletion (I i.1) M) := by
  let inv := lift (∏ i ∈ s, I i) (inverseStage M I s hI)
    (fun h => inverseStage_compatible M I s hI h)
  refine
    { toLinearMap := LinearMap.pi (fun i =>
        mapOfLE M (Ideal.prod_le_inf.trans (Finset.inf_le i.2)))
      invFun := inv
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply AdicCompletion.ext
    intro n
    change (stageEquiv M I s hI n).symm
      (fun i => eval (I i.1) M n
        (mapOfLE M (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) x)) = eval (∏ i ∈ s, I i) M n x
    apply (stageEquiv M I s hI n).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    exact (mapOfLE_eval M _ n x).trans (stageEquiv_apply M I s hI n _ i).symm
  · intro y
    funext i
    apply AdicCompletion.ext
    intro n
    change eval (I i.1) M n
      (mapOfLE M (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) (inv y)) =
        eval (I i.1) M n (y i)
    have hinv : eval (∏ j ∈ s, I j) M n (inv y) = inverseStage M I s hI n y := rfl
    rw [mapOfLE_eval, ← stageEquiv_apply M I s hI, hinv, inverseStage_apply,
      LinearEquiv.apply_symm_apply]

private theorem completionMap_bijective :
    Function.Bijective (LinearMap.pi (fun i : s =>
      mapOfLE M (Ideal.prod_le_inf.trans (Finset.inf_le i.2))) :
        AdicCompletion (∏ i ∈ s, I i) M →ₗ[R] ((i : s) → AdicCompletion (I i.1) M)) :=
  (completionEquiv M I s hI).bijective

@[expose] public section

/-- The canonical finite comaximal decomposition of adic inverse-limit module
completions. Its forward coordinates are the inclusion-induced maps, with all
module structures taken over the original ring. -/
def equivPiOfPairwiseSupEqTop :
    AdicCompletion (∏ i ∈ s, I i) M ≃ₗ[R] ((i : s) → AdicCompletion (I i.1) M) :=
  LinearEquiv.ofBijective
    (LinearMap.pi (fun i => mapOfLE M (Ideal.prod_le_inf.trans (Finset.inf_le i.2))))
    (by exact completionMap_bijective M I s hI)

/-- As a linear map, decomposition is the product of the inclusion-induced maps. -/
@[simp]
theorem equivPiOfPairwiseSupEqTop_toLinearMap :
    (equivPiOfPairwiseSupEqTop M I s hI).toLinearMap =
      LinearMap.pi (fun i => mapOfLE M (Ideal.prod_le_inf.trans (Finset.inf_le i.2))) := rfl

/-- Every forward coordinate is precisely the existing inclusion-induced map. -/
@[simp]
theorem equivPiOfPairwiseSupEqTop_apply (x : AdicCompletion (∏ i ∈ s, I i) M) (i : s) :
    equivPiOfPairwiseSupEqTop M I s hI x i =
      mapOfLE M (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) x := rfl

/-- At every precision, decomposition is the canonical quotient factor. -/
theorem equivPiOfPairwiseSupEqTop_eval (x : AdicCompletion (∏ i ∈ s, I i) M)
    (i : s) (n : ℕ) :
    eval (I i.1) M n (equivPiOfPairwiseSupEqTop M I s hI x i) =
      Submodule.factor (Submodule.smul_mono_left
        (Ideal.pow_right_mono (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) n))
          (eval (∏ i ∈ s, I i) M n x) := by
  rw [equivPiOfPairwiseSupEqTop_apply]
  exact mapOfLE_eval M (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) n x

/-- The canonical image of a module element decomposes diagonally. -/
@[simp]
theorem equivPiOfPairwiseSupEqTop_of (m : M) :
    equivPiOfPairwiseSupEqTop M I s hI (of (∏ i ∈ s, I i) M m) =
      fun i : s => of (I i.1) M m := by
  funext i
  rw [equivPiOfPairwiseSupEqTop_apply, mapOfLE_of]

/-- The inverse is characterized at each stage by simultaneous representatives.
This describes the canonical stage Chinese remainder inverse without choosing
representatives in the definition. -/
theorem equivPiOfPairwiseSupEqTop_symm_eval_eq_mk_iff
    (y : (i : s) → AdicCompletion (I i.1) M) (n : ℕ) (m : M) :
    eval (∏ i ∈ s, I i) M n ((equivPiOfPairwiseSupEqTop M I s hI).symm y) =
        Submodule.Quotient.mk m ↔
      ∀ i : s, eval (I i.1) M n (y i) = Submodule.Quotient.mk m := by
  constructor
  · intro hm i
    have hi := equivPiOfPairwiseSupEqTop_eval M I s hI
      ((equivPiOfPairwiseSupEqTop M I s hI).symm y) i n
    rw [LinearEquiv.apply_symm_apply, hm] at hi
    exact hi
  · intro hm
    apply (stageEquiv M I s hI n).injective
    funext i
    rw [stageEquiv_apply, ← equivPiOfPairwiseSupEqTop_eval M I s hI,
      LinearEquiv.apply_symm_apply, stageEquiv_mk]
    exact hm i

/-- Decomposition is natural in arbitrary maps of the original modules. The
completed scalar rings depend on the ideals, so the square is stated pointwise. -/
theorem equivPiOfPairwiseSupEqTop_natural
    {N : Type t} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (x : AdicCompletion (∏ i ∈ s, I i) M) (i : s) :
    equivPiOfPairwiseSupEqTop N I s hI (map (∏ i ∈ s, I i) f x) i =
      map (I i.1) f (equivPiOfPairwiseSupEqTop M I s hI x i) := by
  rw [equivPiOfPairwiseSupEqTop_apply, equivPiOfPairwiseSupEqTop_apply]
  exact mapOfLE_natural M (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) f x

/-- The inverse decomposition is natural in maps of the original modules. -/
theorem equivPiOfPairwiseSupEqTop_symm_natural
    {N : Type t} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (y : (i : s) → AdicCompletion (I i.1) M) :
    map (∏ i ∈ s, I i) f ((equivPiOfPairwiseSupEqTop M I s hI).symm y) =
      (equivPiOfPairwiseSupEqTop N I s hI).symm (fun i => map (I i.1) f (y i)) := by
  apply (equivPiOfPairwiseSupEqTop N I s hI).injective
  funext i
  rw [equivPiOfPairwiseSupEqTop_natural, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- Decomposition commutes with every transition to a lower precision. -/
theorem equivPiOfPairwiseSupEqTop_transition
    (x : AdicCompletion (∏ i ∈ s, I i) M) (i : s) {a b : ℕ} (hab : a ≤ b) :
    transitionMap (I i.1) M hab
        (eval (I i.1) M b (equivPiOfPairwiseSupEqTop M I s hI x i)) =
      eval (I i.1) M a (equivPiOfPairwiseSupEqTop M I s hI x i) :=
  transitionMap_comp_eval_apply (I i.1) M hab (equivPiOfPairwiseSupEqTop M I s hI x i)

/-- A diagonal tuple is sent back to the canonical image of its representative. -/
@[simp]
theorem equivPiOfPairwiseSupEqTop_symm_of (m : M) :
    (equivPiOfPairwiseSupEqTop M I s hI).symm (fun i => of (I i.1) M m) =
      of (∏ i ∈ s, I i) M m := by
  apply (equivPiOfPairwiseSupEqTop M I s hI).injective
  rw [LinearEquiv.apply_symm_apply, equivPiOfPairwiseSupEqTop_of]

omit hI in
/-- The zeroth quotient of every adic completion is zero. -/
@[simp]
theorem eval_zero (J : Ideal R) (x : AdicCompletion J M) : eval J M 0 x = 0 := by
  have : Subsingleton (M ⧸ (J ^ 0 • ⊤ : Submodule R M)) :=
    Submodule.Quotient.subsingleton_iff.mpr (by simp)
  exact Subsingleton.elim _ _

omit hI in
/-- For an empty family the inverse comparison has value zero. -/
theorem equivPiOfPairwiseSupEqTop_symm_empty
    (y : (i : (∅ : Finset ι)) → AdicCompletion (I i.1) M) :
    (equivPiOfPairwiseSupEqTop M I ∅ (by simp)).symm y = 0 := by
  apply (equivPiOfPairwiseSupEqTop M I ∅ (by simp)).injective
  funext i
  exact False.elim (Finset.notMem_empty i.1 i.2)

omit hI in
/-- For a singleton family the comparison is the identity after the canonical
identification of the product ideal with its sole factor. -/
theorem equivPiOfPairwiseSupEqTop_singleton (a : ι) (x : AdicCompletion (I a) M) :
    equivPiOfPairwiseSupEqTop M I {a} (by simp)
        ((Finset.prod_singleton I a : ∏ i ∈ ({a} : Finset ι), I i = I a).symm ▸ x)
        ⟨a, Finset.mem_singleton_self a⟩ = x := by
  rw [equivPiOfPairwiseSupEqTop_apply]
  have aux {A B : Ideal R} (h : A = B) (z : AdicCompletion B M) :
      mapOfLE M h.le (h.symm ▸ z) = z := by
    subst B
    exact LinearMap.congr_fun (mapOfLE_id M A) z
  exact aux (Finset.prod_singleton I a) x

end

end AdicCompletion
