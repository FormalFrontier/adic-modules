/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.LinearAlgebra.Quotient.DFinsupp
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Dependent direct sums and adic completion

For any ideal `I`, the completion of a dependent direct sum identifies with the
submodule of families of completed coordinates whose support is finite at each
original quotient evaluation. The finite exceptional set may depend on the
precision. The comparison is linear over `AdicCompletion I R` with its canonical
actions, and its coordinates are the completed direct-sum projections.

The inverse uses the quotient–direct-sum equivalence at each original ideal power
and the compatible-family universal property of raw adic completion. No finite
generation, separatedness or completeness assumption is needed. On finite index
types the comparison agrees with the finite product equivalence.

## References

This file uses Mathlib's adic completion, canonical completed scalar action and
completion functor, formalized by Judith Ludwig and Christian Merten, together
with Mathlib's dependent finitely supported functions. The original quotient
comparisons are `Ideal.quotientDFinsupp`; the inverse is assembled by Mathlib's
`AdicCompletion.lift`.
-/

@[expose] public section

universe uR uι uM uN

namespace AdicCompletion

variable {R : Type uR} [CommRing R] {ι : Type uι}
  (I : Ideal R) (M : ι → Type uM)
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Families of completed coordinates with finite support at every original
ideal-power quotient evaluation, with the inherited completed-ring action. -/
def restrictedProduct :
    Submodule (AdicCompletion I R) (∀ i, AdicCompletion I (M i)) where
  carrier := {x | ∀ n : ℕ, Set.Finite {i | eval I (M i) n (x i) ≠ 0}}
  zero_mem' := by
    intro n
    simp
  add_mem' := by
    intro x y hx hy n
    refine ((hx n).union (hy n)).subset ?_
    intro i hi
    by_cases hxi : eval I (M i) n (x i) = 0
    · right
      intro hyi
      apply hi
      simp only [Pi.add_apply, map_add, hxi, hyi, add_zero]
    · exact Or.inl hxi
  smul_mem' := by
    intro a x hx n
    refine (hx n).subset ?_
    intro i hi hxi
    apply hi
    change (a • x i).val n = 0
    rw [smul_eval]
    change a.val n • eval I (M i) n (x i) = 0
    rw [hxi, smul_zero]

/-- Membership is precisely finite support at every natural-number precision. -/
@[simp]
theorem mem_restrictedProduct (x : ∀ i, AdicCompletion I (M i)) :
    x ∈ restrictedProduct I M ↔
      ∀ n : ℕ, Set.Finite {i | eval I (M i) n (x i) ≠ 0} :=
  Iff.rfl

/-- Restricted families are equal when all their completed coordinates agree. -/
@[ext]
theorem restrictedProduct_ext {x y : restrictedProduct I M}
    (h : ∀ i,
      (x : ∀ i, AdicCompletion I (M i)) i =
      (y : ∀ i, AdicCompletion I (M i)) i) : x = y :=
  Subtype.ext (funext h)

private theorem quotientDFinsupp_eval_apply
    (x : AdicCompletion I (Π₀ i, M i)) (n : ℕ) (i : ι) :
    Ideal.quotientDFinsupp (I ^ n) M (eval I (Π₀ i, M i) n x) i =
      eval I (M i) n (map I (DFinsupp.lapply (R := R) (M := M) i) x) := by
  rw [Ideal.quotientDFinsupp_apply]
  rfl

private noncomputable def dfinsuppComparison :
    AdicCompletion I (Π₀ i, M i) →ₗ[AdicCompletion I R] restrictedProduct I M :=
  (LinearMap.pi (fun i => map I (DFinsupp.lapply (R := R) (M := M) i))).codRestrict
    (restrictedProduct I M) (by
      intro x
      apply (mem_restrictedProduct I M _).2
      intro n
      simpa only [LinearMap.pi_apply, ← quotientDFinsupp_eval_apply] using
        (Ideal.quotientDFinsupp (I ^ n) M (eval I (Π₀ i, M i) n x)).finite_support)

private theorem dfinsuppComparison_apply
    (x : AdicCompletion I (Π₀ i, M i)) (i : ι) :
    (dfinsuppComparison I M x : ∀ i, AdicCompletion I (M i)) i =
      map I (DFinsupp.lapply (R := R) (M := M) i) x :=
  rfl

/-- Pack the finite family of original quotient coordinates at one precision. -/
private noncomputable def restrictedStage (n : ℕ) :
    restrictedProduct I M →ₗ[R] Π₀ i, M i ⧸ (I ^ n • (⊤ : Submodule R (M i))) where
  toFun x := by
    classical
    let h := (mem_restrictedProduct I M _).1 x.property n
    exact
      { toFun := fun i => eval I (M i) n (x.val i)
        support' := Trunc.mk ⟨h.toFinset.val, fun i => by
          by_cases hi : eval I (M i) n (x.val i) = 0
          · exact Or.inr hi
          · exact Or.inl (show i ∈ h.toFinset from h.mem_toFinset.mpr hi)⟩ }
  map_add' x y := by
    apply DFinsupp.ext
    intro i
    exact (eval I (M i) n).map_add (x.val i) (y.val i)
  map_smul' r x := by
    apply DFinsupp.ext
    intro i
    exact (eval I (M i) n).map_smul r (x.val i)

private theorem restrictedStage_apply (n : ℕ) (x : restrictedProduct I M) (i : ι) :
    restrictedStage I M n x i = eval I (M i) n (x.val i) :=
  rfl

private noncomputable def restrictedStagePreimage (n : ℕ) :
    restrictedProduct I M →ₗ[R]
      (Π₀ i, M i) ⧸ (I ^ n • (⊤ : Submodule R (Π₀ i, M i))) :=
  ((Ideal.quotientDFinsupp (I ^ n) M).symm.restrictScalars R).toLinearMap ∘ₗ
    restrictedStage I M n

private theorem quotientDFinsupp_restrictedStagePreimage
    (n : ℕ) (x : restrictedProduct I M) :
    Ideal.quotientDFinsupp (I ^ n) M (restrictedStagePreimage I M n x) =
      restrictedStage I M n x := by
  simp only [restrictedStagePreimage, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalars_apply, LinearEquiv.apply_symm_apply]

private theorem restrictedStagePreimage_compatible {m n : ℕ} (hmn : m ≤ n) :
    transitionMap I (Π₀ i, M i) hmn ∘ₗ restrictedStagePreimage I M n =
      restrictedStagePreimage I M m := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply]
  apply (Ideal.quotientDFinsupp (I ^ m) M).injective
  calc
    Ideal.quotientDFinsupp (I ^ m) M
        (transitionMap I (Π₀ i, M i) hmn (restrictedStagePreimage I M n x)) =
      DFinsupp.mapRange.linearMap (R := R)
        (fun i => transitionMap I (M i) hmn)
        (Ideal.quotientDFinsupp (I ^ n) M (restrictedStagePreimage I M n x)) :=
      Ideal.quotientDFinsupp_factor (J := I ^ n) (K := I ^ m) (M := M)
        (Ideal.pow_le_pow_right hmn) (restrictedStagePreimage I M n x)
    _ = Ideal.quotientDFinsupp (I ^ m) M (restrictedStagePreimage I M m x) := by
      simp only [quotientDFinsupp_restrictedStagePreimage]
      apply DFinsupp.ext
      intro i
      simp only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply,
        restrictedStage_apply, eval_apply]
      exact transitionMap_comp_eval_apply I (M i) hmn (x.val i)

private theorem dfinsuppComparison_bijective : Function.Bijective (dfinsuppComparison I M) := by
  constructor
  · intro x y h
    apply AdicCompletion.ext
    intro n
    apply (Ideal.quotientDFinsupp (I ^ n) M).injective
    apply DFinsupp.ext
    intro i
    change Ideal.quotientDFinsupp (I ^ n) M (eval I (Π₀ i, M i) n x) i =
      Ideal.quotientDFinsupp (I ^ n) M (eval I (Π₀ i, M i) n y) i
    rw [quotientDFinsupp_eval_apply, quotientDFinsupp_eval_apply]
    exact congrArg (eval I (M i) n)
      (congrArg (fun z : restrictedProduct I M => z.val i) h)
  · intro x
    let g := restrictedStagePreimage I M
    have hg : ∀ {m n : ℕ} (hmn : m ≤ n),
        transitionMap I (Π₀ i, M i) hmn ∘ₗ g n = g m :=
      fun hmn => restrictedStagePreimage_compatible I M hmn
    refine ⟨lift I g hg x, ?_⟩
    apply restrictedProduct_ext
    intro i
    apply AdicCompletion.ext
    intro n
    change eval I (M i) n
        (map I (DFinsupp.lapply (R := R) (M := M) i) (lift I g hg x)) =
      eval I (M i) n (x.val i)
    rw [← quotientDFinsupp_eval_apply]
    have heval : eval I (Π₀ i, M i) n (lift I g hg x) = g n x := by
      simpa only [LinearMap.comp_apply] using
        LinearMap.congr_fun (eval_lift I g hg n) x
    rw [heval, quotientDFinsupp_restrictedStagePreimage, restrictedStage_apply]

/-- Completion of a dependent direct sum is the restricted product of the
component completions, linearly over the canonically completed coefficient ring. -/
noncomputable def dfinsuppEquiv :
    AdicCompletion I (Π₀ i, M i) ≃ₗ[AdicCompletion I R]
      restrictedProduct I M :=
  private_decl% (LinearEquiv.ofBijective
    (dfinsuppComparison I M) (dfinsuppComparison_bijective I M))

/-- The comparison's coordinates are the completed direct-sum projections. -/
@[simp]
theorem dfinsuppEquiv_apply_apply
    (x : AdicCompletion I (Π₀ i, M i)) (i : ι) :
    (dfinsuppEquiv I M x : ∀ i, AdicCompletion I (M i)) i =
      map I (DFinsupp.lapply (R := R) (M := M) i) x :=
  dfinsuppComparison_apply I M x i

/-- The comparison sends an original finite family to its componentwise images. -/
@[simp]
theorem dfinsuppEquiv_of (m : Π₀ i, M i) :
    (dfinsuppEquiv I M (of I (Π₀ i, M i) m) :
      ∀ i, AdicCompletion I (M i)) =
      fun i => of I (M i) (m i) := by
  funext i
  rw [dfinsuppEquiv_apply_apply, map_of]
  rfl

/-- Each completed coordinate of the inverse is the prescribed coordinate. -/
@[simp]
theorem dfinsuppEquiv_symm_apply_apply
    (x : restrictedProduct I M) (i : ι) :
    map I (DFinsupp.lapply (R := R) (M := M) i)
        ((dfinsuppEquiv I M).symm x) =
      (x : ∀ i, AdicCompletion I (M i)) i := by
  simpa only [dfinsuppEquiv_apply_apply] using
    congrArg (fun z : restrictedProduct I M => z.val i)
      ((dfinsuppEquiv I M).apply_symm_apply x)

/-- At every original quotient precision, the inverse has the prescribed
finitely supported component evaluations. -/
theorem dfinsuppEquiv_symm_eval
    (x : restrictedProduct I M) (n : ℕ) (i : ι) :
    Ideal.quotientDFinsupp (I ^ n) M
        (eval I (Π₀ i, M i) n ((dfinsuppEquiv I M).symm x)) i =
      eval I (M i) n ((x : ∀ i, AdicCompletion I (M i)) i) := by
  rw [quotientDFinsupp_eval_apply, dfinsuppEquiv_symm_apply_apply]

/-- The inverse is the completion class of an original family exactly when
all its completed coordinates are the corresponding original images. -/
theorem dfinsuppEquiv_symm_eq_of_iff
    (x : restrictedProduct I M) (m : Π₀ i, M i) :
    (dfinsuppEquiv I M).symm x = of I (Π₀ i, M i) m ↔
      ∀ i, (x : ∀ i, AdicCompletion I (M i)) i =
        of I (M i) (m i) := by
  constructor
  · intro h i
    rw [← dfinsuppEquiv_symm_apply_apply I M x i, h, map_of]
    rfl
  · intro h
    apply (dfinsuppEquiv I M).injective
    apply restrictedProduct_ext
    intro i
    simpa only [LinearEquiv.apply_symm_apply, dfinsuppEquiv_of] using h i

/-- The direct-sum completion comparison is natural in original component maps. -/
theorem dfinsuppEquiv_naturality
    (N : ι → Type uN)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i)
    (x : AdicCompletion I (Π₀ i, M i)) (i : ι) :
    (dfinsuppEquiv I N
        (map I (DFinsupp.mapRange.linearMap f) x) :
      ∀ i, AdicCompletion I (N i)) i =
      map I (f i)
        ((dfinsuppEquiv I M x : ∀ i, AdicCompletion I (M i)) i) := by
  rw [dfinsuppEquiv_apply_apply, dfinsuppEquiv_apply_apply,
    map_comp_apply, map_comp_apply]
  have hcomp :
      DFinsupp.lapply (R := R) (M := N) i ∘ₗ DFinsupp.mapRange.linearMap f =
        f i ∘ₗ DFinsupp.lapply (R := R) (M := M) i := by
    apply LinearMap.ext
    intro m
    rfl
  exact congrArg (fun g => map I g x) hcomp

/-- Every family is restricted when the index type is finite, for any ideal. -/
theorem restrictedProduct_eq_top [Finite ι] :
    restrictedProduct I M = ⊤ := by
  apply top_unique
  intro x _
  exact (mem_restrictedProduct I M x).2 (fun _ => Set.toFinite _)

/-- On finite index types the whole comparison agrees with completion of the
finite direct-sum/function equivalence followed by the finite product comparison. -/
theorem dfinsuppEquiv_piEquivOfFintype
    [DecidableEq ι] [Fintype ι] :
    (restrictedProduct I M).subtype ∘ₗ
        (dfinsuppEquiv I M).toLinearMap =
      (piEquivOfFintype I M).toLinearMap ∘ₗ
        (congr I
          (DFinsupp.linearEquivFunOnFintype (R := R) (M := M))).toLinearMap := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
    dfinsuppEquiv_apply_apply, piEquivOfFintype_apply, congr_apply, pi,
    LinearMap.pi_apply, map_comp_apply]
  rfl

end AdicCompletion
