/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.RingHom
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Ideal.Maps

set_option warningAsError true

/-!
# Adic completion and restriction of scalars

Let `R → S` be an algebra, `M` an `S`-module with a compatible `R`-module structure,
and `I` an ideal of `R`. The filtration of `M` by the powers of `I` agrees, after
restriction of scalars, with the filtration by powers of the extended ideal in `S`.
Thus their quotients and their inverse-limit adic completions are linearly
equivalent over `R`. No finiteness, separatedness, or completeness assumption is used.

The equivalence goes from completion along the extended ideal to completion
along `I`. Its inverse, both quotient representatives, and the transition maps
are described by the accompanying lemmas. It also intertwines the canonical
completed scalar actions through the completed coefficient ring map. Its inverse
is the bijective semilinear map `restrictScalarsSemilinearMap`, with scalar
compatibility given by `LinearMap.map_smulₛₗ`; the coefficient ring map need not
be invertible. The law `restrictScalarsSemilinearMap_map` expresses naturality
in an original module map. Under this comparison, the completed coefficient ring
map agrees with completion of the original coefficient linear map.

## References

The comparison uses Mathlib's ideal-map/power identity,
`Submodule.Quotient.restrictScalarsEquiv`, representative-preserving
`Submodule.quotEquivOfEq` and compatible-family `AdicCompletion` interfaces.
The original project implementation and its distinct library adaptation are
credited in `docs/CREDITS.md`.
-/

@[expose] public section

universe uR uS uM uN

namespace AdicCompletion

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The powers of an extended ideal act on `M` by the same submodules after
restriction of scalars as the corresponding powers of the original ideal. -/
theorem map_pow_smul_top_restrictScalars (I : Ideal R) (n : ℕ) :
    (((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M)).restrictScalars R) =
      I ^ n • (⊤ : Submodule R M) := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq]
  rfl

/-- The level-`n` quotient comparison, from the extended-ideal quotient to the
original-ideal quotient, linear over `R`. -/
def restrictScalarsLevelEquiv (I : Ideal R) (N : Type*) [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] (n : ℕ) :
    (N ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S N)) ≃ₗ[R]
      N ⧸ (I ^ n • ⊤ : Submodule R N) :=
  (Submodule.Quotient.restrictScalarsEquiv R
      ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S N))).symm.trans
    (Submodule.quotEquivOfEq _ _ (map_pow_smul_top_restrictScalars (M := N) I n))

@[simp]
theorem restrictScalarsLevelEquiv_mk (I : Ideal R) (n : ℕ) (x : M) :
    restrictScalarsLevelEquiv I M n
      (Submodule.Quotient.mk x :
        M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) =
      (Submodule.Quotient.mk x : M ⧸ (I ^ n • ⊤ : Submodule R M)) := by
  simp [restrictScalarsLevelEquiv]

@[simp]
theorem restrictScalarsLevelEquiv_symm_mk (I : Ideal R) (n : ℕ) (x : M) :
    (restrictScalarsLevelEquiv I M n).symm
      (Submodule.Quotient.mk x : M ⧸ (I ^ n • ⊤ : Submodule R M)) =
      (Submodule.Quotient.mk x :
        M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) := by
  apply (restrictScalarsLevelEquiv I M n).injective
  simp

/-- The level comparisons commute with the transition maps. -/
theorem restrictScalarsLevelEquiv_transitionMap (I : Ideal R) {m n : ℕ}
    (hmn : m ≤ n)
    (x : M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) :
    restrictScalarsLevelEquiv I M m
        (transitionMap (I.map (algebraMap R S)) M hmn x) =
      transitionMap I M hmn (restrictScalarsLevelEquiv I M n x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change restrictScalarsLevelEquiv I M m
      (Submodule.factor _ (Submodule.mkQ _ x)) =
        Submodule.factor _ (restrictScalarsLevelEquiv I M n (Submodule.mkQ _ x))
    simp

/-- The inverse level comparisons commute with the transition maps. -/
theorem restrictScalarsLevelEquiv_symm_transitionMap (I : Ideal R) {m n : ℕ}
    (hmn : m ≤ n) (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    (restrictScalarsLevelEquiv I M m).symm (transitionMap I M hmn x) =
      transitionMap (I.map (algebraMap R S)) M hmn
        ((restrictScalarsLevelEquiv I M n).symm x) := by
  apply (restrictScalarsLevelEquiv I M m).injective
  rw [restrictScalarsLevelEquiv_transitionMap]
  simp

/-- Restricting scalars commutes with forming the inverse-limit completion:
extended-ideal completion is the original-ideal completion as an
`R`-module. -/
def restrictScalarsEquiv (I : Ideal R) (N : Type*) [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] :
    AdicCompletion (I.map (algebraMap R S)) N ≃ₗ[R] AdicCompletion I N where
  toFun x := ⟨fun n => restrictScalarsLevelEquiv I N n (x.val n), by
    intro m n hmn
    rw [← restrictScalarsLevelEquiv_transitionMap I hmn]
    exact congrArg (restrictScalarsLevelEquiv I N m) (x.property hmn)⟩
  invFun x := ⟨fun n => (restrictScalarsLevelEquiv I N n).symm (x.val n), by
    intro m n hmn
    change transitionMap (I.map (algebraMap R S)) N hmn
        ((restrictScalarsLevelEquiv I N n).symm (x.val n)) =
      (restrictScalarsLevelEquiv I N m).symm (x.val m)
    rw [← restrictScalarsLevelEquiv_symm_transitionMap I hmn]
    exact congrArg (restrictScalarsLevelEquiv I N m).symm (x.property hmn)⟩
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (restrictScalarsLevelEquiv I N n).symm_apply_apply (x.val n)
  right_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (restrictScalarsLevelEquiv I N n).apply_symm_apply (x.val n)
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact (restrictScalarsLevelEquiv I N n).map_add (x.val n) (y.val n)
  map_smul' a x := by
    apply AdicCompletion.ext
    intro n
    exact (restrictScalarsLevelEquiv I N n).map_smul a (x.val n)

@[simp]
theorem restrictScalarsEquiv_eval (I : Ideal R)
    (x : AdicCompletion (I.map (algebraMap R S)) M) (n : ℕ) :
    eval I M n (restrictScalarsEquiv I M x) =
      restrictScalarsLevelEquiv I M n
        (eval (I.map (algebraMap R S)) M n x) :=
  rfl

@[simp]
theorem restrictScalarsEquiv_symm_eval (I : Ideal R) (x : AdicCompletion I M) (n : ℕ) :
    eval (I.map (algebraMap R S)) M n ((restrictScalarsEquiv I M).symm x) =
      (restrictScalarsLevelEquiv I M n).symm (eval I M n x) :=
  rfl

@[simp]
theorem restrictScalarsEquiv_of (I : Ideal R) (x : M) :
    restrictScalarsEquiv I M (of (I.map (algebraMap R S)) M x) = of I M x := by
  apply AdicCompletion.ext
  intro n
  exact restrictScalarsLevelEquiv_mk I n x

@[simp]
theorem restrictScalarsEquiv_symm_of (I : Ideal R) (x : M) :
    (restrictScalarsEquiv I M).symm (of I M x) =
      of (I.map (algebraMap R S)) M x := by
  apply (restrictScalarsEquiv I M).injective
  simp

/-- The quotient comparison intertwines the original quotient-coefficient
actions through the induced coefficient map. -/
theorem restrictScalarsLevelEquiv_smul (I : Ideal R) (n : ℕ) (r : R ⧸ I ^ n)
    (x : M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) :
    restrictScalarsLevelEquiv I M n
        (Ideal.quotientMap ((I.map (algebraMap R S)) ^ n) (algebraMap R S)
          ((Ideal.pow_right_mono Ideal.le_comap_map n).trans
            (Ideal.le_comap_pow (algebraMap R S) n)) r • x) =
      r • restrictScalarsLevelEquiv I M n x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    simp only [Ideal.quotientMap_mk, Module.Quotient.mk_smul_mk,
      restrictScalarsLevelEquiv_mk, IsScalarTower.algebraMap_smul]

/-- Restriction of scalars intertwines the canonical completed module actions
through the canonical completed coefficient ring map. No finiteness or
intrinsic-completeness assumption is required. -/
theorem restrictScalarsEquiv_smul (I : Ideal R) (a : AdicCompletion I R)
    (x : AdicCompletion (I.map (algebraMap R S)) M) :
    restrictScalarsEquiv I M
        (mapRingHom I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map a • x) =
      a • restrictScalarsEquiv I M x := by
  apply AdicCompletion.ext
  intro n
  change restrictScalarsLevelEquiv I M n
      ((mapRingHom I (I.map (algebraMap R S)) (algebraMap R S)
        Ideal.le_comap_map a • x).val n) =
    (a • restrictScalarsEquiv I M x).val n
  rw [smul_eval, smul_eval, val_smul_eq_evalₐ_smul, val_smul_eq_evalₐ_smul,
    evalₐ_mapRingHom]
  exact restrictScalarsLevelEquiv_smul I n (evalₐ I n a) (x.val n)

/-- The inverse restriction-of-scalars comparison, semilinear over the canonical
completed coefficient ring map. Both completions retain their canonical completed
module actions. This map is bijective even though the coefficient ring map need
not be injective or surjective. -/
noncomputable def restrictScalarsSemilinearMap (I : Ideal R) (N : Type*) [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] :
    AdicCompletion I N →ₛₗ[
      mapRingHom I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map]
      AdicCompletion (I.map (algebraMap R S)) N :=
  let e := restrictScalarsEquiv (S := S) I N
  { toFun := e.symm
    map_add' := e.symm.map_add
    map_smul' := by
      intro a x
      apply e.injective
      calc
        e (e.symm (a • x)) = a • x := e.apply_symm_apply _
        _ = a • e (e.symm x) :=
          congrArg (fun y => a • y) (e.apply_symm_apply x).symm
        _ = e (mapRingHom I (I.map (algebraMap R S)) (algebraMap R S)
            Ideal.le_comap_map a • e.symm x) :=
          (restrictScalarsEquiv_smul (S := S) I a (e.symm x)).symm }

/-- The semilinear comparison has the same function as the inverse original-ring
linear comparison. -/
@[simp]
theorem restrictScalarsSemilinearMap_apply (I : Ideal R) (x : AdicCompletion I M) :
    restrictScalarsSemilinearMap (S := S) I M x =
      (restrictScalarsEquiv (S := S) I M).symm x :=
  rfl

/-- The semilinear restriction comparison is bijective on completed modules. -/
theorem restrictScalarsSemilinearMap_bijective (I : Ideal R) (N : Type*)
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] :
    Function.Bijective (restrictScalarsSemilinearMap (S := S) I N) :=
  (restrictScalarsEquiv (S := S) I N).symm.bijective

/-- Restriction of scalars on completions is natural in an original linear map. -/
theorem restrictScalarsSemilinearMap_map
    {R : Type uR} [CommRing R]
    {S : Type uS} [CommRing S] [Algebra R S]
    {M : Type uM} [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M]
    {N : Type uN} [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N]
    (I : Ideal R) (f : M →ₗ[S] N) (x : AdicCompletion I M) :
    restrictScalarsSemilinearMap (S := S) I N
        (map I (f.restrictScalars R) x) =
      map (I.map (algebraMap R S)) f
        (restrictScalarsSemilinearMap (S := S) I M x) := by
  simp only [restrictScalarsSemilinearMap_apply]
  apply AdicCompletion.ext
  intro n
  change (restrictScalarsLevelEquiv (S := S) I N n).symm
      ((f.restrictScalars R).reduceModIdeal (I ^ n) (x.val n)) =
    f.reduceModIdeal ((I.map (algebraMap R S)) ^ n)
      ((restrictScalarsLevelEquiv (S := S) I M n).symm (x.val n))
  induction x.val n using Submodule.Quotient.induction_on with
  | _ m =>
    simp only [LinearMap.reduceModIdeal_apply, restrictScalarsLevelEquiv_symm_mk,
      LinearMap.restrictScalars_apply]

/-- Under restriction of scalars, the completed coefficient ring map is the
completion of the original coefficient linear map. -/
@[simp]
theorem restrictScalarsEquiv_mapRingHom (I : Ideal R) (a : AdicCompletion I R) :
    restrictScalarsEquiv I S
        (mapRingHom I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map a) =
      map I (Algebra.linearMap R S) a := by
  apply AdicCompletion.ext
  intro n
  induction a using AdicCompletion.induction_on with
  | _ a =>
    rw [map_mk]
    change restrictScalarsLevelEquiv I S n
        (eval (I.map (algebraMap R S)) S n
          (mapRingHom I (I.map (algebraMap R S)) (algebraMap R S)
            Ideal.le_comap_map (mk I R a))) =
      Submodule.Quotient.mk (algebraMap R S (a.val n))
    rw [← factor_evalₐ_eq_eval (I.map (algebraMap R S)) _
      (le_of_eq (Ideal.mul_top _).symm), evalₐ_mapRingHom, evalₐ_mk]
    rw [Ideal.quotientMap_mk, Ideal.Quotient.factor_mk,
      ← Ideal.Quotient.mk_eq_mk]
    exact restrictScalarsLevelEquiv_mk (R := R) (S := S) (M := S) I n
      (algebraMap R S (a.val n))

end AdicCompletion
