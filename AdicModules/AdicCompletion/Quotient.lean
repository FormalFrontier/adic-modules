/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import AdicModules.AdicCompletion.Kernel
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.Basic

import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Quotients of adic completions

The coordinate projections are semilinear over the corresponding coefficient
evaluations, including the normalized first projection to the residue quotient.

For an ideal `I` in a commutative ring, finite generation of one specified
positive power identifies every ideal-power quotient of the raw `I`-adic
completion of an arbitrary module with the corresponding quotient of the original
module. The comparisons are linear over the original ring, natural in original
linear maps, and compatible with the precision transitions.

For coefficients the comparison is an algebra equivalence from the quotient by
the power of the extended ideal to `R ⧸ I ^ k`. It agrees with the module comparison
through the class-preserving ideal/submodule quotient identifications.

The forward maps are induced by evaluation; their inverses are induced by the
original maps to the completion. Degree zero and trivial rings are included.
The fixed-stage coefficient comparison also remains available assuming only
finite generation of that stage's ideal power, independently of any positive-power
hypothesis.

For an arbitrary ideal, flatness or projectivity of the raw completion over its
completed coefficient ring descends to every original ideal-power quotient over
its coefficient quotient. The original quotient is a retract of scalar extension
of the completed module along evaluation. Only this one-sided retraction is used;
no identification of evaluation kernels with extended ideal powers is required.

## References

The semilinear projections bundle the coordinate evaluation and completed-module
scalar laws from Mathlib's `RingTheory/AdicCompletion/Basic.lean` and `Algebra.lean`,
by Kenny Lau, Judith Ludwig, Christian Merten and Jiedong Jiang. Their targets use
the quotient module action from Pierre-Alexandre Bazin's
`Algebra/Module/Torsion/Basic.lean`.

The construction uses Mathlib's quotient equivalence for equal ideals and its
first isomorphism theorems for linear maps and algebras. The inverses are
described using Mathlib's
algebra homomorphism induced on ideal quotients. The descent statements use
Christian Merten's flat base-change and retract results in Mathlib, Kevin Buzzard
and Antoine Labelle's projective tensor and splitting results, and the quotient–tensor
equivalence of Antoine Chambert-Loir and Jujian Zhang. Scalar extension of maps uses
Mathlib's `LinearMap.liftBaseChange`.
-/

@[expose] public section

universe u v w uR uM

open TensorProduct

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- Evaluation at precision `n`, semilinear over the canonical coefficient evaluation. -/
noncomputable def evalₛₗ (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    AdicCompletion I M →ₛₗ[(evalₐ I n).toRingHom]
      M ⧸ (I ^ n • (⊤ : Submodule R M)) where
  toFun := eval I M n
  map_add' := (eval I M n).map_add
  map_smul' s x := val_smul_eq_evalₐ_smul I n s (x.val n)

/-- The semilinear projection has the original-ring-linear evaluation as its
underlying function. -/
@[simp]
theorem evalₛₗ_apply (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (x : AdicCompletion I M) :
    evalₛₗ I M n x = eval I M n x := rfl

/-- The projection sends an original element to its residue class. -/
@[simp]
theorem evalₛₗ_of (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (m : M) :
    evalₛₗ I M n (of I M m) = (I ^ n • (⊤ : Submodule R M)).mkQ m :=
  eval_of I M n m

/-- Every stage projection is surjective. -/
theorem evalₛₗ_surjective (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) :
    Function.Surjective (evalₛₗ I M n) := eval_surjective I M n

/-- The semilinear projections commute with the precision transitions. -/
theorem transitionMap_evalₛₗ (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I M) :
    transitionMap I M hmn (evalₛₗ I M n x) = evalₛₗ I M m x :=
  transitionMap_comp_eval_apply I M hmn x

/-- First evaluation with codomain the original first quotient and coefficient
map to the residue ring `R ⧸ I`. -/
noncomputable def evalOneₛₗ (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    AdicCompletion I M →ₛₗ[(evalOneₐ I).toRingHom]
      M ⧸ (I • (⊤ : Submodule R M)) where
  toFun x :=
    Submodule.factor
      (show (I ^ 1 • (⊤ : Submodule R M)) ≤ I • (⊤ : Submodule R M) by simp)
      (evalₛₗ I M 1 x)
  map_add' x y := by simp only [map_add]
  map_smul' s x := by
    induction s using induction_on I R with | _ s =>
    induction x using induction_on I M with | _ x =>
    rfl

/-- First semilinear evaluation agrees with original-ring-linear evaluation,
followed by the canonical first-quotient factor. -/
@[simp]
theorem evalOneₛₗ_apply (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (x : AdicCompletion I M) :
    evalOneₛₗ I M x =
      Submodule.factor
        (show (I ^ 1 • (⊤ : Submodule R M)) ≤ I • (⊤ : Submodule R M) by simp)
        (eval I M 1 x) := rfl

/-- The normalized projection takes an original element to its first residue. -/
@[simp]
theorem evalOneₛₗ_of (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (m : M) :
    evalOneₛₗ I M (of I M m) = (I • (⊤ : Submodule R M)).mkQ m := rfl

/-- Normalization to the first quotient preserves surjectivity. -/
theorem evalOneₛₗ_surjective (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    Function.Surjective (evalOneₛₗ I M) := by
  intro q
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) q
  exact ⟨of I M m, evalOneₛₗ_of I M m⟩

/-- For the coefficient module, normalized semilinear evaluation is the canonical
algebra evaluation after the class-preserving ideal quotient factor. -/
theorem factor_evalOneₛₗ_eq_evalOneₐ (I : Ideal R) (x : AdicCompletion I R) :
    Ideal.Quotient.factor (show (I • ⊤ : Ideal R) ≤ I by simp)
      (evalOneₛₗ I R x) = evalOneₐ I x := by
  rw [evalOneₛₗ_apply, ← factorₐ_evalₐ_one,
    ← factor_eval_eq_evalₐ I x (le_of_eq (Ideal.mul_top _))]
  exact Quotient.inductionOn' (eval I R 1 x) (fun _ ↦ rfl)

/-- The quotient of a completed module by an ideal power is the corresponding
quotient of the original module, if one positive ideal power is finitely generated. -/
noncomputable def quotientPowLinearEquivOfFGPow (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) :
    (AdicCompletion I M ⧸ (I ^ k • (⊤ : Submodule R (AdicCompletion I M)))) ≃ₗ[R]
      M ⧸ (I ^ k • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k)).trans
      ((eval I M k).quotKerEquivOfSurjective (eval_surjective I M k))

/-- The module comparison sends every completed representative to its evaluation. -/
@[simp]
theorem quotientPowLinearEquivOfFGPow_mk (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (x : AdicCompletion I M) :
    quotientPowLinearEquivOfFGPow I M hn hI k (Submodule.Quotient.mk x) =
      eval I M k x := by
  simp [quotientPowLinearEquivOfFGPow]

/-- The module comparison preserves the residue of every original element. -/
theorem quotientPowLinearEquivOfFGPow_of (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (m : M) :
    quotientPowLinearEquivOfFGPow I M hn hI k
        (Submodule.Quotient.mk (of I M m)) = Submodule.Quotient.mk m := by
  rw [quotientPowLinearEquivOfFGPow_mk, eval_of]
  rfl

/-- The inverse module comparison is induced by the original map to the completion. -/
@[simp]
theorem quotientPowLinearEquivOfFGPow_symm_mk (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (m : M) :
    (quotientPowLinearEquivOfFGPow I M hn hI k).symm (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (of I M m) := by
  apply (quotientPowLinearEquivOfFGPow I M hn hI k).injective
  rw [LinearEquiv.apply_symm_apply, quotientPowLinearEquivOfFGPow_of]

/-- The inverse module comparison recovers the class of every completed element
from its evaluation. -/
theorem quotientPowLinearEquivOfFGPow_symm_eval (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (x : AdicCompletion I M) :
    (quotientPowLinearEquivOfFGPow I M hn hI k).symm (eval I M k x) =
      Submodule.Quotient.mk x := by
  rw [← quotientPowLinearEquivOfFGPow_mk I M hn hI k x,
    LinearEquiv.symm_apply_apply]

/-- Quotient comparisons commute with the quotient maps induced by every original
linear map. -/
theorem quotientPowLinearEquivOfFGPow_natural (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (f : M →ₗ[R] N)
    (z : AdicCompletion I M ⧸ (I ^ k • (⊤ : Submodule R (AdicCompletion I M)))) :
    quotientPowLinearEquivOfFGPow I N hn hI k
        ((((map I f).restrictScalars R).reduceModIdeal (I ^ k)).restrictScalars R z) =
      ((f.reduceModIdeal (I ^ k)).restrictScalars R)
        (quotientPowLinearEquivOfFGPow I M hn hI k z) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  simpa only [LinearMap.restrictScalars_apply, LinearMap.reduceModIdeal_apply,
    Submodule.mkQ_apply, quotientPowLinearEquivOfFGPow_mk, eval_apply] using map_val_apply I f x

/-- Quotient comparisons commute with the intrinsic precision projections on the
completion and the precision projections on the original module. -/
theorem quotientPowLinearEquivOfFGPow_transitionMap (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) {j k : ℕ} (hjk : j ≤ k)
    (z : AdicCompletion I M ⧸ (I ^ k • (⊤ : Submodule R (AdicCompletion I M)))) :
    quotientPowLinearEquivOfFGPow I M hn hI j
        (transitionMap I (AdicCompletion I M) hjk z) =
      transitionMap I M hjk (quotientPowLinearEquivOfFGPow I M hn hI k z) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  rw [Submodule.factor_mk, Submodule.mkQ_apply, Submodule.mkQ_apply,
    quotientPowLinearEquivOfFGPow_mk, quotientPowLinearEquivOfFGPow_mk]
  exact (transitionMap_comp_eval_apply I M hjk x).symm

/-- The linear evaluation kernel determines the coefficient evaluation kernel. -/
theorem map_pow_eq_ker_evalₐ (I : Ideal R) (n : ℕ)
    (h : (I ^ n) • (⊤ : Submodule R (AdicCompletion I R)) = (eval I R n).ker) :
    (I.map (algebraMap R (AdicCompletion I R))) ^ n =
      RingHom.ker (evalₐ I n).toRingHom := by
  have hpow :
      ((I.map (algebraMap R (AdicCompletion I R))) ^ n).restrictScalars R =
        (eval I R n).ker := by
    rw [← Ideal.map_pow, ← Ideal.smul_top_eq_map]
    exact h
  have htop : (I ^ n • ⊤ : Ideal R) = I ^ n := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  ext x
  change x ∈ ((I.map (algebraMap R (AdicCompletion I R))) ^ n).restrictScalars R ↔
    evalₐ I n x = 0
  rw [hpow, LinearMap.mem_ker]
  constructor
  · intro hx
    rw [← factor_eval_eq_evalₐ I x htop.le, hx]
    rfl
  · intro hx
    rw [← factor_evalₐ_eq_eval I x htop.ge, hx]
    rfl

private theorem quotientPowAlgEquiv_mk_of_kernel (I : Ideal R) (n : ℕ)
    (h : (I ^ n) • (⊤ : Submodule R (AdicCompletion I R)) = (eval I R n).ker)
    (x : AdicCompletion I R) :
    ((Ideal.quotientEquivAlgOfEq R (map_pow_eq_ker_evalₐ I n h)).trans
        (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n)))
          (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n) x) =
      evalₐ I n x := by
  change (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n))
      (Ideal.Quotient.mk (RingHom.ker (evalₐ I n).toRingHom) x) = _
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (surjective_evalₐ I n) x

/-- Evaluation identifies the quotient of the adic completion by the `n`th power
of the extended ideal with `R ⧸ I ^ n`, assuming only that `I ^ n` is finitely
generated. -/
noncomputable def quotientPowAlgEquiv (I : Ideal R) (n : ℕ) (h : (I ^ n).FG) :
    (AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n) ≃ₐ[R]
      R ⧸ I ^ n :=
  (Ideal.quotientEquivAlgOfEq R (by
    exact map_pow_eq_ker_evalₐ I n (pow_smul_top_eq_ker_eval_of_fg_pow h))).trans
      (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n))

/-- The quotient comparison sends a completion representative to its evaluation. -/
@[simp]
theorem quotientPowAlgEquiv_mk (I : Ideal R) (n : ℕ) (h : (I ^ n).FG)
    (x : AdicCompletion I R) :
    quotientPowAlgEquiv I n h
        (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n) x) =
      evalₐ I n x := by
  exact quotientPowAlgEquiv_mk_of_kernel I n (pow_smul_top_eq_ker_eval_of_fg_pow h) x

/-- The inverse comparison sends a residue class to the class of its image in
the adic completion. -/
@[simp]
theorem quotientPowAlgEquiv_symm_mk (I : Ideal R) (n : ℕ) (h : (I ^ n).FG) (r : R) :
    (quotientPowAlgEquiv I n h).symm (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n)
        (algebraMap R (AdicCompletion I R) r) := by
  apply (quotientPowAlgEquiv I n h).injective
  simpa only [AlgEquiv.apply_symm_apply, quotientPowAlgEquiv_mk,
    Ideal.Quotient.algebraMap_eq] using ((evalₐ I n).commutes r).symm

/-- The inverse comparison is the algebra homomorphism on quotients induced by
the algebra map to the completion. -/
theorem quotientPowAlgEquiv_symm_toAlgHom (I : Ideal R) (n : ℕ) (h : (I ^ n).FG) :
    (quotientPowAlgEquiv I n h).symm.toAlgHom =
      Ideal.quotientMapₐ ((I.map (algebraMap R (AdicCompletion I R))) ^ n)
        (Algebra.ofId R (AdicCompletion I R))
        (by
          change I ^ n ≤
            ((I.map (algebraMap R (AdicCompletion I R))) ^ n).comap
              (algebraMap R (AdicCompletion I R))
          rw [← Ideal.map_pow (algebraMap R (AdicCompletion I R)) I n]
          exact Ideal.le_comap_map) := by
  apply AlgHom.ext
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simpa only [AlgEquiv.toAlgHom_apply, Ideal.quotient_map_mkₐ,
    Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply] using
    quotientPowAlgEquiv_symm_mk I n h r

/-- If one positive ideal power is finitely generated, evaluation identifies every
quotient of the completed coefficient ring with the corresponding original quotient. -/
noncomputable def quotientPowAlgEquivOfFGPow (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) :
    (AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ k) ≃ₐ[R]
      R ⧸ I ^ k :=
  (Ideal.quotientEquivAlgOfEq R (by
    exact map_pow_eq_ker_evalₐ I k (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k))).trans
      (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I k))

/-- The positive-power coefficient comparison sends every representative to its evaluation. -/
@[simp]
theorem quotientPowAlgEquivOfFGPow_mk (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (x : AdicCompletion I R) :
    quotientPowAlgEquivOfFGPow I hn hI k
        (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ k) x) =
      evalₐ I k x := by
  exact quotientPowAlgEquiv_mk_of_kernel I k
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k) x

/-- The inverse positive-power coefficient comparison is induced by the algebra map
to the completion. -/
@[simp]
theorem quotientPowAlgEquivOfFGPow_symm_mk (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (r : R) :
    (quotientPowAlgEquivOfFGPow I hn hI k).symm (Ideal.Quotient.mk (I ^ k) r) =
      Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ k)
        (algebraMap R (AdicCompletion I R) r) := by
  apply (quotientPowAlgEquivOfFGPow I hn hI k).injective
  simpa only [AlgEquiv.apply_symm_apply, quotientPowAlgEquivOfFGPow_mk,
    Ideal.Quotient.algebraMap_eq] using ((evalₐ I k).commutes r).symm

/-- The whole inverse of the positive-power coefficient comparison is the induced
algebra homomorphism on ideal quotients. -/
theorem quotientPowAlgEquivOfFGPow_symm_toAlgHom (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) :
    (quotientPowAlgEquivOfFGPow I hn hI k).symm.toAlgHom =
      Ideal.quotientMapₐ ((I.map (algebraMap R (AdicCompletion I R))) ^ k)
        (Algebra.ofId R (AdicCompletion I R))
        (by
          change I ^ k ≤
            ((I.map (algebraMap R (AdicCompletion I R))) ^ k).comap
              (algebraMap R (AdicCompletion I R))
          rw [← Ideal.map_pow (algebraMap R (AdicCompletion I R)) I k]
          exact Ideal.le_comap_map) := by
  apply AlgHom.ext
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simpa only [AlgEquiv.toAlgHom_apply, Ideal.quotient_map_mkₐ,
    Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply] using
    quotientPowAlgEquivOfFGPow_symm_mk I hn hI k r

/-- The positive-power and fixed-stage coefficient comparisons agree wherever both
finite-generation hypotheses are available. -/
theorem quotientPowAlgEquivOfFGPow_eq (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (h : (I ^ k).FG) :
    quotientPowAlgEquivOfFGPow I hn hI k = quotientPowAlgEquiv I k h :=
  rfl

/-- The coefficient comparisons commute with the algebra projections between
ideal-power quotients. -/
theorem quotientPowAlgEquivOfFGPow_factor (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) {j k : ℕ} (hjk : j ≤ k)
    (z : AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ k) :
    quotientPowAlgEquivOfFGPow I hn hI j
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hjk) z) =
      Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hjk)
        (quotientPowAlgEquivOfFGPow I hn hI k z) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (quotientPowAlgEquivOfFGPow I hn hI k z)
  have hz := congrArg (quotientPowAlgEquivOfFGPow I hn hI k).symm hr
  rw [AlgEquiv.symm_apply_apply, quotientPowAlgEquivOfFGPow_symm_mk] at hz
  rw [← hz]
  change quotientPowAlgEquivOfFGPow I hn hI j
      (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ j)
        (algebraMap R (AdicCompletion I R) r)) = _
  rw [quotientPowAlgEquivOfFGPow_mk, quotientPowAlgEquivOfFGPow_mk,
    (evalₐ I j).commutes, (evalₐ I k).commutes]
  exact ((Ideal.Quotient.factorₐ R
    (show I ^ k ≤ I ^ j from Ideal.pow_le_pow_right hjk)).commutes r).symm

/-- The coefficient comparison agrees with the original-ring-linear module comparison
through the explicit class-preserving ideal/submodule quotient identifications. -/
theorem quotientPowAlgEquivOfFGPow_toLinearEquiv (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ)
    (z : AdicCompletion I R ⧸ (I ^ k • (⊤ : Submodule R (AdicCompletion I R)))) :
    (quotientPowAlgEquivOfFGPow I hn hI k).toLinearEquiv
        (((Submodule.quotEquivOfEq _ _ (show
            (I ^ k • (⊤ : Submodule R (AdicCompletion I R))) =
              ((I.map (algebraMap R (AdicCompletion I R))) ^ k).restrictScalars R by
            rw [← Ideal.map_pow, ← Ideal.smul_top_eq_map])).trans
          (Submodule.Quotient.restrictScalarsEquiv R
            ((I.map (algebraMap R (AdicCompletion I R))) ^ k))) z) =
      Submodule.quotEquivOfEq _ _ (show (I ^ k • ⊤ : Ideal R) = I ^ k by
        rw [Ideal.smul_eq_mul, Ideal.mul_top])
          (quotientPowLinearEquivOfFGPow I R hn hI k z) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  simp only [Submodule.mkQ_apply, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    Submodule.Quotient.restrictScalarsEquiv_mk, AlgEquiv.toLinearEquiv_apply,
    quotientPowLinearEquivOfFGPow_mk]
  change quotientPowAlgEquivOfFGPow I hn hI k
      (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ k) x) = _
  rw [quotientPowAlgEquivOfFGPow_mk]
  have htop : (I ^ k • ⊤ : Ideal R) = I ^ k := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  rw [← factor_eval_eq_evalₐ I x htop.le]
  obtain ⟨r, hr⟩ := Submodule.mkQ_surjective (I ^ k • (⊤ : Submodule R R)) (eval I R k x)
  rw [← hr]
  rfl

/-- The original quotient is a retract of base change along evaluation; both
flatness and projectivity therefore descend. The scalar dictionaries stay local. -/
private theorem quotient_flat_projective_retract (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    (Module.Flat (AdicCompletion I R) (AdicCompletion I M) →
      Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M)))) ∧
    (Module.Projective (AdicCompletion I R) (AdicCompletion I M) →
      Module.Projective (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M)))) := by
  let S := AdicCompletion I R
  let H := AdicCompletion I M
  let A := R ⧸ I ^ n
  let Q := M ⧸ (I ^ n • (⊤ : Submodule R M))
  let : Algebra S A := (evalₐ I n).toRingHom.toAlgebra
  let : IsScalarTower R S A := IsScalarTower.of_algHom (evalₐ I n)
  let : IsScalarTower R A Q :=
    (Module.isTorsionBySet_quotient_ideal_smul M (I ^ n)).isScalarTower
  let : Module S Q := Module.restrictScalars S A Q
  let : IsScalarTower S A Q := IsScalarTower.restrictScalars S A Q
  -- Evaluation is S-linear for precisely the action induced by evalₐ.
  let e : H →ₗ[S] Q :=
    { (eval I M n).toAddMonoidHom with
      map_smul' := fun s x => (evalₛₗ I M n).map_smulₛₗ s x }
  let T := A ⊗[S] H
  let f : M →ₗ[R] T :=
    ((TensorProduct.mk S A H 1).restrictScalars R).comp (of I M)
  let c : (A ⊗[R] M) ≃ₗ[A] Q :=
    (TensorProduct.quotTensorEquivQuotSMul M (I ^ n)).extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap R A))
  let α : Q →ₗ[A] T := (f.liftBaseChange A).comp c.symm.toLinearMap
  let β : T →ₗ[A] Q := e.liftBaseChange A
  have hsplit : β.comp α = LinearMap.id := by
    apply LinearMap.ext
    intro q
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
      (I ^ n • (⊤ : Submodule R M)) q
    change e.liftBaseChange A
      (f.liftBaseChange A (c.symm (Submodule.Quotient.mk m))) = _
    rw [show c.symm (Submodule.Quotient.mk m) = (1 : A) ⊗ₜ[R] m from
      TensorProduct.quotTensorEquivQuotSMul_symm_mk (I ^ n) m]
    rw [LinearMap.liftBaseChange_one_tmul]
    change e.liftBaseChange A ((1 : A) ⊗ₜ[S] of I M m) = _
    rw [LinearMap.liftBaseChange_one_tmul]
    exact eval_of I M n m
  constructor
  · intro h
    let : Module.Flat S H := h
    let : Module.Flat A T := Module.Flat.baseChange S A H
    exact Module.Flat.of_retract α β hsplit
  · intro h
    let : Module.Projective S H := h
    let : Module.Projective A T := inferInstance
    exact Module.Projective.of_split α β hsplit

/-- Flatness of the raw completion over its completed coefficient ring implies
flatness of every original ideal-power quotient over its coefficient quotient. -/
theorem moduleFlat_quotient_of_flat_completion
    {R : Type uR} [CommRing R] (I : Ideal R)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Flat (AdicCompletion I R) (AdicCompletion I M)] (n : ℕ) :
    Module.Flat (R ⧸ I ^ n)
      (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
  (quotient_flat_projective_retract I M n).1 inferInstance

/-- Projectivity of the raw completion over its completed coefficient ring implies
projectivity of every original ideal-power quotient over its coefficient quotient. -/
theorem moduleProjective_quotient_of_projective_completion
    {R : Type uR} [CommRing R] (I : Ideal R)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Projective (AdicCompletion I R) (AdicCompletion I M)] (n : ℕ) :
    Module.Projective (R ⧸ I ^ n)
      (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
  (quotient_flat_projective_retract I M n).2 inferInstance

end AdicCompletion
