/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.LinearMap
public import AdicModules.AdicCompletion.Pi
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Completion of modules of linear maps

For every ideal, `AdicCompletion.homComparison` evaluates a completed module of
linear maps on a completed source. Both its scalar linearities use the canonical
action of the completed ring. Its quotient-coordinate law describes its value on
all completed inputs, not just on the images of original maps.

For a finite projective source, `homEquivOfFiniteProjective` makes this comparison
a linear equivalence. The target module is arbitrary. Independently, maps from
the completion of a finite module to any module over the completed ring agree if
they agree on the original module.

## Implementation and references

Reduction uses Mathlib's `LinearMap.reduceModIdeal`, factored once using
`Submodule.liftQ`; compatible evaluations use `AdicCompletion.lift`. The finite-free
case uses the existing finite-product and `LinearEquiv.piRing` equivalences; the
general case uses a finite-free projective splitting. No completeness assumption
on the raw inverse limit and no finite generation assumption on the ideal is used.

We reuse Mathlib's completion formalizations by Kenny Lau, Judith Ludwig,
Christian Merten and Jiedong Jiang, the quotient formalizations by Johannes Hölzl,
Mario Carneiro, Kevin Buzzard and Yury Kudryashov, and the Pi linear algebra API
by these authors and Eric Wieser.
The projective splitting is due to Johan Commelin, building on the projective-module
formalization by Kevin Buzzard and Antoine Labelle. The finite-free Hom retract
approach also follows the Formal Frontier Projective Modules library; the product
and linear-map completion APIs are from Formal Frontier Adic Modules.
-/

@[expose] public section

noncomputable section

universe u v w t z

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

section Comparison

variable (N : Type w) [AddCommGroup N] [Module R N]

private def homReduction (J : Ideal R) :
    ((M →ₗ[R] N) ⧸ (J • ⊤ : Submodule R (M →ₗ[R] N))) →ₗ[R ⧸ J]
      (M ⧸ (J • ⊤ : Submodule R M) →ₗ[R ⧸ J]
        N ⧸ (J • ⊤ : Submodule R N)) :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective <|
    (J • ⊤ : Submodule R (M →ₗ[R] N)).liftQ (LinearMap.reduceModIdeal J) (by
      intro f hf
      change LinearMap.reduceModIdeal J f = 0
      refine Submodule.smul_induction_on hf (fun r hr f _ ↦ ?_) (fun f g hf hg ↦ ?_)
      · apply LinearMap.ext
        intro x
        obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (J • ⊤ : Submodule R M) x
        change Submodule.Quotient.mk (r • f m) = 0
        exact (Submodule.Quotient.mk_eq_zero _).mpr
          (Submodule.smul_mem_smul hr Submodule.mem_top)
      · rw [map_add, hf, hg, add_zero])

private theorem homReduction_mk (J : Ideal R) (f : M →ₗ[R] N) :
    homReduction M N J ((J • ⊤ : Submodule R (M →ₗ[R] N)).mkQ f) =
      f.reduceModIdeal J :=
  rfl

private theorem homReduction_transition {m n : ℕ} (hmn : m ≤ n)
    (F : (M →ₗ[R] N) ⧸ (I ^ n • ⊤ : Submodule R (M →ₗ[R] N)))
    (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    transitionMap I N hmn (homReduction M N (I ^ n) F x) =
      homReduction M N (I ^ m) (transitionMap I (M →ₗ[R] N) hmn F)
        (transitionMap I M hmn x) := by
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ F
  exact LinearMap.congr_fun (transitionMap_comp_reduceModIdeal I f hmn) x

/-- Evaluate a completed module of linear maps on the completed source. Both Hom
scalar rings are the canonical completed ring; no finiteness assumptions are needed. -/
@[no_expose] def homComparison :
    AdicCompletion I (M →ₗ[R] N) →ₗ[AdicCompletion I R]
      (AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N) where
  toFun F :=
    { __ := lift I
        (fun n ↦ ((homReduction M N (I ^ n) (eval I (M →ₗ[R] N) n F)).restrictScalars R).comp
          (eval I M n))
        (fun {m n} hmn ↦ by
          apply LinearMap.ext
          intro x
          exact (homReduction_transition I M N hmn
            (eval I (M →ₗ[R] N) n F) (eval I M n x)).trans (by
              change homReduction M N (I ^ m)
                (transitionMap I (M →ₗ[R] N) hmn (F.val n))
                (transitionMap I M hmn (x.val n)) =
                  homReduction M N (I ^ m) (F.val m) (x.val m)
              rw [F.property hmn, x.property hmn]))
      map_smul' a x := by
        apply AdicCompletion.ext
        intro n
        change homReduction M N (I ^ n) (F.val n) ((a • x).val n) =
          a.val n • homReduction M N (I ^ n) (F.val n) (x.val n)
        rw [smul_eval, val_smul_eq_evalₐ_smul, val_smul_eq_evalₐ_smul, map_smul] }
  map_add' F G := by
    apply LinearMap.ext
    intro x
    apply AdicCompletion.ext
    intro n
    change homReduction M N (I ^ n) ((F + G).val n) (x.val n) =
      homReduction M N (I ^ n) (F.val n) (x.val n) +
        homReduction M N (I ^ n) (G.val n) (x.val n)
    rw [val_add_apply, map_add, LinearMap.add_apply]
  map_smul' a F := by
    apply LinearMap.ext
    intro x
    apply AdicCompletion.ext
    intro n
    change homReduction M N (I ^ n) ((a • F).val n) (x.val n) =
      a.val n • homReduction M N (I ^ n) (F.val n) (x.val n)
    rw [smul_eval, val_smul_eq_evalₐ_smul, val_smul_eq_evalₐ_smul,
      map_smul, LinearMap.smul_apply]

private theorem eval_homComparison (F : AdicCompletion I (M →ₗ[R] N))
    (x : AdicCompletion I M) (n : ℕ) :
    eval I N n (homComparison I M N F x) =
      homReduction M N (I ^ n) (eval I (M →ₗ[R] N) n F) (eval I M n x) :=
  rfl

/-- At every precision, any representative of the entire Hom coordinate evaluates
by the existing reduction of that representative. This applies to all completed inputs. -/
theorem eval_homComparison_apply (F : AdicCompletion I (M →ₗ[R] N))
    (x : AdicCompletion I M) (n : ℕ) (f : M →ₗ[R] N)
    (hf : eval I (M →ₗ[R] N) n F =
      (I ^ n • (⊤ : Submodule R (M →ₗ[R] N))).mkQ f) :
    eval I N n (homComparison I M N F x) =
      f.reduceModIdeal (I ^ n) (eval I M n x) := by
  rw [eval_homComparison, hf, homReduction_mk]

/-- On an original map, completed evaluation is exactly Mathlib's completed map,
as an equality of maps linear over the completed ring. -/
@[simp]
theorem homComparison_of (f : M →ₗ[R] N) :
    homComparison I M N (of I (M →ₗ[R] N) f) = map I f := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  exact eval_homComparison_apply I M N (of I (M →ₗ[R] N) f) x n f rfl

/-- Evaluating at an original source element is completion of the original
evaluation linear map. -/
@[simp]
theorem homComparison_apply_of (F : AdicCompletion I (M →ₗ[R] N)) (m : M) :
    homComparison I M N F (of I M m) =
      map I (LinearMap.applyₗ (R := R) (M₂ := N) m) F := by
  apply AdicCompletion.ext
  intro n
  obtain ⟨f, hf⟩ := Submodule.mkQ_surjective
    (I ^ n • ⊤ : Submodule R (M →ₗ[R] N)) (eval I (M →ₗ[R] N) n F)
  rw [show (homComparison I M N F (of I M m)).val n =
      f.reduceModIdeal (I ^ n) (eval I M n (of I M m)) from
        eval_homComparison_apply I M N F _ n f hf.symm]
  change _ = (LinearMap.applyₗ (R := R) (M₂ := N) m).reduceModIdeal (I ^ n)
    (eval I (M →ₗ[R] N) n F)
  rw [← hf]
  rfl

section Naturality

variable {L : Type t} [AddCommGroup L] [Module R L]
variable {P : Type z} [AddCommGroup P] [Module R P]

/-- Completed evaluation is contravariantly natural in any original source map. -/
theorem homComparison_precomp (g : L →ₗ[R] M) (F : AdicCompletion I (M →ₗ[R] N)) :
    homComparison I L N (map I (LinearMap.lcomp R N g) F) =
      (homComparison I M N F).comp (map I g) := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  obtain ⟨f, hf⟩ := Submodule.mkQ_surjective
    (I ^ n • ⊤ : Submodule R (M →ₗ[R] N)) (eval I (M →ₗ[R] N) n F)
  have hfg : eval I (L →ₗ[R] N) n (map I (LinearMap.lcomp R N g) F) =
      (I ^ n • ⊤ : Submodule R (L →ₗ[R] N)).mkQ (f.comp g) := by
    change (LinearMap.lcomp R N g).reduceModIdeal (I ^ n)
      (eval I (M →ₗ[R] N) n F) = _
    rw [← hf]
    rfl
  rw [show (homComparison I L N (map I (LinearMap.lcomp R N g) F) x).val n =
      (f.comp g).reduceModIdeal (I ^ n) (eval I L n x) from
        eval_homComparison_apply I L N _ x n _ hfg]
  change _ = eval I N n (homComparison I M N F (map I g x))
  rw [eval_homComparison_apply I M N F _ n f hf.symm]
  obtain ⟨l, hl⟩ := Submodule.mkQ_surjective (I ^ n • ⊤ : Submodule R L)
    (eval I L n x)
  change _ = f.reduceModIdeal (I ^ n) (g.reduceModIdeal (I ^ n) (eval I L n x))
  rw [← hl]
  rfl

/-- Completed evaluation is covariantly natural in any original target map. -/
theorem homComparison_postcomp (h : N →ₗ[R] P) (F : AdicCompletion I (M →ₗ[R] N)) :
    homComparison I M P (map I (LinearMap.compRight R h) F) =
      (map I h).comp (homComparison I M N F) := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  obtain ⟨f, hf⟩ := Submodule.mkQ_surjective
    (I ^ n • ⊤ : Submodule R (M →ₗ[R] N)) (eval I (M →ₗ[R] N) n F)
  have hfh : eval I (M →ₗ[R] P) n (map I (LinearMap.compRight R h) F) =
      (I ^ n • ⊤ : Submodule R (M →ₗ[R] P)).mkQ (h.comp f) := by
    change (LinearMap.compRight R h).reduceModIdeal (I ^ n)
      (eval I (M →ₗ[R] N) n F) = _
    rw [← hf]
    rfl
  rw [show (homComparison I M P (map I (LinearMap.compRight R h) F) x).val n =
      (h.comp f).reduceModIdeal (I ^ n) (eval I M n x) from
        eval_homComparison_apply I M P _ x n _ hfh]
  change _ = h.reduceModIdeal (I ^ n) (eval I N n (homComparison I M N F x))
  rw [eval_homComparison_apply I M N F x n f hf.symm]
  obtain ⟨m, hm⟩ := Submodule.mkQ_surjective (I ^ n • ⊤ : Submodule R M)
    (eval I M n x)
  rw [← hm]
  rfl

end Naturality

end Comparison

section Ext

variable {P : Type z} [AddCommMonoid P] [Module (AdicCompletion I R) P]

/-- Maps from the completion of a finite module to any completed-ring module agree
if they agree on the original module. Only tensor-generation surjectivity is used. -/
theorem hom_ext_of_finite [Module.Finite R M]
    (F G : AdicCompletion I M →ₗ[AdicCompletion I R] P)
    (h : ∀ m : M, F (of I M m) = G (of I M m)) : F = G := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := ofTensorProduct_surjective_of_finite I M x
  induction y using TensorProduct.inductionOn with
  | tmul a m => simp only [ofTensorProduct_tmul, map_smul, h m]
  | add y y' hy hy' => simp only [map_add, hy, hy']

end Ext

section FiniteProjective

variable (N : Type w) [AddCommGroup N] [Module R N]

open scoped BigOperators

private theorem homComparison_finiteFree (n : ℕ) :
    ∃ E : AdicCompletion I ((Fin n → R) →ₗ[R] N) ≃ₗ[AdicCompletion I R]
      (AdicCompletion I (Fin n → R) →ₗ[AdicCompletion I R] AdicCompletion I N),
      E.toLinearMap = homComparison I (Fin n → R) N := by
  classical
  let eR := LinearEquiv.piRing R N (Fin n) R
  let E : AdicCompletion I ((Fin n → R) →ₗ[R] N) ≃ₗ[AdicCompletion I R]
      (AdicCompletion I (Fin n → R) →ₗ[AdicCompletion I R] AdicCompletion I N) :=
    (congr I eR).trans <|
      (piEquivOfFintype I (fun _ : Fin n => N)).trans <|
        (LinearEquiv.piRing (AdicCompletion I R) (AdicCompletion I N)
          (Fin n) (AdicCompletion I R)).symm.trans <|
          (LinearEquiv.congrLeft (AdicCompletion I N) (AdicCompletion I R) (piEquivFin I n)).symm
  have hcoeff (r : R) : of I R r = algebraMap R (AdicCompletion I R) r := by
    simpa using (AdicCompletion.algebraMap_apply (S := R) I r).symm
  have hscalar (r : R) (x : AdicCompletion I N) : of I R r • x = r • x := by
    rw [hcoeff r]
    exact algebraMap_smul (AdicCompletion I R) r x
  have hcoord (m : Fin n → R) :
      (LinearMap.applyₗ (R := R) (M₂ := N) m : ((Fin n → R) →ₗ[R] N) →ₗ[R] N) =
        ∑ j : Fin n, m j • LinearMap.applyₗ (R := R) (M₂ := N) (Pi.single j 1) := by
    apply LinearMap.ext
    intro f
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    change f m = ∑ j : Fin n, m j • f (Pi.single j 1)
    have hf := congrArg (fun g : (Fin n → R) →ₗ[R] N => g m)
      ((LinearEquiv.piRing R N (Fin n) R).symm_apply_apply f)
    simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply] using hf.symm
  have hmap (F : AdicCompletion I ((Fin n → R) →ₗ[R] N)) (m : Fin n → R) :
      map I (LinearMap.applyₗ (R := R) (M₂ := N) m) F =
        ∑ j : Fin n, m j •
          map I (LinearMap.applyₗ (R := R) (M₂ := N) (Pi.single j 1)) F := by
    rw [hcoord m]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  have hproj (F : AdicCompletion I ((Fin n → R) →ₗ[R] N)) (j : Fin n) :
      piEquivOfFintype I (fun _ : Fin n => N) (congr I eR F) j =
        map I (LinearMap.applyₗ (R := R) (M₂ := N) (Pi.single j 1)) F := by
    rw [piEquivOfFintype_apply, congr_apply]
    change map I (LinearMap.proj j) (map I eR.toLinearMap F) = _
    rw [map_comp_apply]
    rfl
  have hEof (F : AdicCompletion I ((Fin n → R) →ₗ[R] N)) (m : Fin n → R) :
      E F (of I (Fin n → R) m) =
        ∑ j : Fin n, m j •
          map I (LinearMap.applyₗ (R := R) (M₂ := N) (Pi.single j 1)) F := by
    change (LinearEquiv.piRing (AdicCompletion I R) (AdicCompletion I N)
      (Fin n) (AdicCompletion I R)).symm
      (piEquivOfFintype I (fun _ : Fin n => N) (congr I eR F))
      (piEquivFin I n (of I (Fin n → R) m)) = _
    rw [LinearEquiv.piRing_symm_apply, piEquivFin_apply, pi_of]
    apply Finset.sum_congr rfl
    intro j _
    rw [hproj F j, hscalar]
  -- The completed Hom input F is arbitrary. Finite generation is used only in
  -- the source slot to extend agreement on the original finite-free module.
  have hEV : E.toLinearMap = homComparison I (Fin n → R) N := by
    apply LinearMap.ext
    intro F
    apply hom_ext_of_finite I (Fin n → R)
    intro m
    change E F (of I (Fin n → R) m) =
      homComparison I (Fin n → R) N F (of I (Fin n → R) m)
    rw [hEof F m, homComparison_apply_of I (Fin n → R) N F m]
    exact (hmap F m).symm
  exact ⟨E, hEV⟩

variable [Module.Finite R M] [Module.Projective R M]

private theorem homComparison_bijective : Function.Bijective (homComparison I M N) := by
  obtain ⟨n, r, i, _, _, hri⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R M
  obtain ⟨E, hEV⟩ := homComparison_finiteFree I N n
  let a := map I (LinearMap.lcomp R N r)
  let b := map I (LinearMap.lcomp R N i)
  let c := LinearMap.lcomp (AdicCompletion I R) (AdicCompletion I N) (map I r)
  let d := LinearMap.lcomp (AdicCompletion I R) (AdicCompletion I N) (map I i)
  have hpre : LinearMap.lcomp R N i ∘ₗ LinearMap.lcomp R N r = LinearMap.id := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro m
    change f (r (i m)) = f m
    exact congrArg f (LinearMap.congr_fun hri m)
  have hba : b ∘ₗ a = LinearMap.id := by
    dsimp only [a, b]
    rw [map_comp, hpre, map_id]
  have hdc : d ∘ₗ c = LinearMap.id := by
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro x
    change y (map I r (map I i x)) = y x
    simp only [map_comp_apply, hri, map_id, LinearMap.id_apply]
  have hκa (F : AdicCompletion I (M →ₗ[R] N)) :
      homComparison I (Fin n → R) N (a F) = c (homComparison I M N F) :=
    homComparison_precomp I M N r F
  have hκb (F : AdicCompletion I ((Fin n → R) →ₗ[R] N)) :
      homComparison I M N (b F) = d (homComparison I (Fin n → R) N F) :=
    homComparison_precomp I (Fin n → R) N i F
  constructor
  · intro x y hxy
    have hax : a x = a y := by
      apply E.injective
      calc
        E (a x) = homComparison I (Fin n → R) N (a x) := LinearMap.congr_fun hEV _
        _ = c (homComparison I M N x) := hκa x
        _ = c (homComparison I M N y) := congrArg c hxy
        _ = homComparison I (Fin n → R) N (a y) := (hκa y).symm
        _ = E (a y) := (LinearMap.congr_fun hEV _).symm
    calc
      x = b (a x) := (LinearMap.congr_fun hba x).symm
      _ = b (a y) := congrArg b hax
      _ = y := LinearMap.congr_fun hba y
  · intro y
    let z := E.symm (c y)
    refine ⟨b z, ?_⟩
    calc
      homComparison I M N (b z) = d (homComparison I (Fin n → R) N z) := hκb z
      _ = d (E z) := congrArg d (LinearMap.congr_fun hEV z).symm
      _ = d (c y) := congrArg d (E.apply_symm_apply (c y))
      _ = y := LinearMap.congr_fun hdc y

/-- Completion of the original Hom module agrees with Hom over the completed ring
when the original source is finite projective. The target module and the ideal are
arbitrary. Its forward map is the canonical `homComparison`, independent of any
finite-free splitting used to prove bijectivity. -/
def homEquivOfFiniteProjective :
    AdicCompletion I (M →ₗ[R] N) ≃ₗ[AdicCompletion I R]
      (AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N) :=
  LinearEquiv.ofBijective (homComparison I M N) (by
    exact homComparison_bijective I M N)

/-- The forward linear map of the finite-projective Hom equivalence is canonical evaluation. -/
@[simp]
theorem homEquivOfFiniteProjective_toLinearMap :
    (homEquivOfFiniteProjective I M N).toLinearMap = homComparison I M N :=
  rfl

/-- Applying the finite-projective Hom equivalence is canonical completed evaluation. -/
@[simp]
theorem homEquivOfFiniteProjective_apply (F : AdicCompletion I (M →ₗ[R] N)) :
    homEquivOfFiniteProjective I M N F = homComparison I M N F :=
  rfl

/-- The inverse Hom equivalence sends a completed original map to the original map's
canonical image in the completion of Hom. -/
@[simp]
theorem homEquivOfFiniteProjective_symm_map (f : M →ₗ[R] N) :
    (homEquivOfFiniteProjective I M N).symm (map I f) = of I (M →ₗ[R] N) f := by
  apply (homEquivOfFiniteProjective I M N).injective
  simp only [LinearEquiv.apply_symm_apply, homEquivOfFiniteProjective_apply, homComparison_of]

/-- The finite-projective Hom equivalence is contravariantly natural in maps between
finite projective original sources. -/
theorem homEquivOfFiniteProjective_precomp
    {L : Type t} [AddCommGroup L] [Module R L]
    [Module.Finite R L] [Module.Projective R L]
    (g : L →ₗ[R] M) (F : AdicCompletion I (M →ₗ[R] N)) :
    homEquivOfFiniteProjective I L N (map I (LinearMap.lcomp R N g) F) =
      (homEquivOfFiniteProjective I M N F).comp (map I g) :=
  homComparison_precomp I M N g F

/-- The finite-projective Hom equivalence is covariantly natural in arbitrary
original target maps. Only the fixed source is required to be finite projective. -/
theorem homEquivOfFiniteProjective_postcomp
    {P : Type z} [AddCommGroup P] [Module R P]
    (h : N →ₗ[R] P) (F : AdicCompletion I (M →ₗ[R] N)) :
    homEquivOfFiniteProjective I M P (map I (LinearMap.compRight R h) F) =
      (map I h).comp (homEquivOfFiniteProjective I M N F) :=
  homComparison_postcomp I M N h F

end FiniteProjective

end AdicCompletion
