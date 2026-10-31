/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.TensorProduct
public import AdicModules.AdicCompletion.Quotient

import AdicModules.AdicCompletion.LinearMap
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.StdBasis

/-!
# Bases of adic completions from original lifts

Let `I` be any ideal of a commutative ring `R`. A finite basis of the original
first quotient `M / I M`, together with original representatives of its vectors,
gives a basis of the raw completion on those same completed representatives if
every positive original quotient `M / Iⁿ M` is flat over `R / Iⁿ`. Equivalently,
the existing finite linear-combination map on those representatives is bijective.

The construction retains the original index type. Its coordinate API describes
the entire synthesis map, coefficients of completed linear combinations and
original basis lifts, and reconstruction and uniqueness at every original stage,
including precision zero. Normalized first residues of all completed coordinates
are the residue-basis coordinates of the canonical first projection. In particular,
finite free first quotient and flat positive quotients imply that the raw completion
is free over its completed ring.

No finite generation of the ideal, Noetherianity, completeness of the base,
original-module finiteness, flatness, projectivity or separation is assumed.
The original module has only its original scalar action. Nilpotence is used only
for the image of the original ideal in an original power quotient; no evaluation
kernel is identified with an ideal extended to the completion.

## References

The additive quotient-square and nilpotent flat-target criteria are in
`AdicModules.LinearAlgebra.Quotient.Basic` and `.Flat`; the latter uses Nailin
Guan's Mathlib kernel-intersection theorem. The raw completed-map criterion is in
`AdicModules.AdicCompletion.LinearMap`. The whole finite-product synthesis
identity in `AdicModules.AdicCompletion.TensorProduct` transports its conclusion
to the prescribed synthesis map, using Mathlib's finite-product completion API.
The basis and finite linear-combination interfaces follow Mathlib's
`LinearAlgebra/Basis/Defs.lean` and `LinearAlgebra/Finsupp/LinearCombination.lean`.
The quotient coordinate inverse uses the original quotient universal property and
scalar extension along the surjective original coefficient quotient map.
-/

@[expose] public section

noncomputable section

universe uR uM uι

open Module

namespace AdicCompletion

/-- The scalar form of the existing coefficientwise evaluation identity. -/
private theorem eval_smul_eq
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    (n : ℕ) (s : AdicCompletion I R) (x : AdicCompletion I M) :
    eval I M n (s • x) = evalₐ I n s • eval I M n x :=
  (evalₛₗ I M n).map_smulₛₗ s x

/-- The finite synthesis map on specified original lifts is bijective exactly
when every positive original ideal-power quotient is flat over its coefficient quotient.
The sufficient direction passes from the residue basis through the nilpotent
flat-target criterion on original power quotients, then completes the original
synthesis map and transports it along the canonical finite-product equivalence. -/
theorem linearCombination_of_bijective_iff_flat_pow_quotients
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {ι : Type uι} [Fintype ι]
    (b : Basis ι (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (v : ι → M)
    (hv : ∀ i : ι, (I • (⊤ : Submodule R M)).mkQ (v i) = b i) :
    Function.Bijective
      (Fintype.linearCombination (AdicCompletion I R)
        (fun i : ι => AdicCompletion.of I M (v i))) ↔
      ∀ n : ℕ, 0 < n →
        Module.Flat (R ⧸ I ^ n)
          (M ⧸ (I ^ n • (⊤ : Submodule R M))) := by
  classical
  let S := AdicCompletion I R
  let H := AdicCompletion I M
  let F := ι → S
  let Ψ : F →ₗ[S] H := Fintype.linearCombination S (fun i => of I M (v i))
  constructor
  · intro hbij
    let e : F ≃ₗ[S] H := LinearEquiv.ofBijective Ψ hbij
    let : Module.Free S H := Module.Free.of_equiv e
    intro n _
    exact moduleFlat_quotient_of_flat_completion I M n
  · intro hflat
    let P := ι → R
    let f : P →ₗ[R] M := Fintype.linearCombination R v
    let rX : P →+ (ι → R ⧸ I) :=
      { toFun := fun a i => Ideal.Quotient.mk I (a i)
        map_zero' := by
          funext i
          exact _root_.map_zero (Ideal.Quotient.mk I)
        map_add' := by
          intro a c
          funext i
          exact _root_.map_add (Ideal.Quotient.mk I) (a i) (c i) }
    have hrX : Function.Surjective rX := by
      intro a
      refine ⟨fun i => Classical.choose (Ideal.Quotient.mk_surjective (a i)), ?_⟩
      funext i
      exact Classical.choose_spec (Ideal.Quotient.mk_surjective (a i))
    have hkX (a : P) : rX a = 0 ↔ a ∈ I • (⊤ : Submodule R P) := by
      constructor
      · intro ha
        rw [← Finset.univ_sum_single a]
        apply Submodule.sum_mem
        intro i _
        have hi : a i ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (congrFun ha i)
        simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
          (Submodule.smul_mem_smul hi
            (Submodule.mem_top : (Pi.single i (1 : R) : P) ∈
              (⊤ : Submodule R P)))
      · intro ha
        refine Submodule.smul_induction_on ha (fun r hr y _ => ?_)
          (fun y z hy hz => ?_)
        · funext i
          change Ideal.Quotient.mk I (r * y i) = 0
          rw [_root_.map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
        · rw [_root_.map_add, hy, hz, add_zero]
    have hfI : Function.Bijective (f.reduceModIdeal I) := by
      apply LinearMap.bijective_reduceModIdeal_of_addHom_square I f rX
        (I • (⊤ : Submodule R M)).mkQ.toAddMonoidHom hrX hkX
        (fun _ => Submodule.Quotient.mk_eq_zero _)
        b.equivFun.symm.toLinearMap.toAddMonoidHom
        b.equivFun.symm.bijective
      intro a
      change (I • (⊤ : Submodule R M)).mkQ (∑ i, a i • v i) =
        b.equivFun.symm (rX a)
      rw [Basis.equivFun_symm_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hv i]
      rfl
    have hstage (n : ℕ) (hn : 0 < n) :
        Function.Bijective (f.reduceModIdeal (I ^ n)) := by
      let : Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
        hflat n hn
      exact LinearMap.bijective_reduceModIdeal_of_isNilpotent_map (I ^ n) I
        (Ideal.isNilpotent_map_quotient_pow I n) f hfI
    have hmap : Function.Bijective (map I f) :=
      map_bijective_of_reduceModIdeal_bijective I f hstage
    have hcomp : Function.Bijective
        ((map I f).comp
          (piEquivOfFintype I (fun _ : ι => R)).symm.toLinearMap) :=
      hmap.comp (piEquivOfFintype I (fun _ : ι => R)).symm.bijective
    have hwhole :
        (map I f).comp (piEquivOfFintype I (fun _ : ι => R)).symm.toLinearMap = Ψ :=
      map_linearCombination_piEquivOfFintype_symm I M v
    rw [hwhole] at hcomp
    exact hcomp

/-- The basis of the raw completion on specified original lifts of a finite residue
basis, assuming flatness of all positive original ideal-power quotients. -/
noncomputable def basisOfQuotient
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {ι : Type uι} [Finite ι]
    (b : Basis ι (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (v : ι → M)
    (hv : ∀ i : ι, (I • (⊤ : Submodule R M)).mkQ (v i) = b i)
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M)))) :
    Basis ι (AdicCompletion I R) (AdicCompletion I M) :=
  letI : Fintype ι := Fintype.ofFinite ι
  Basis.ofEquivFun
    (LinearEquiv.ofBijective
      (Fintype.linearCombination (AdicCompletion I R)
        (fun i : ι => AdicCompletion.of I M (v i)))
      ((AdicCompletion.linearCombination_of_bijective_iff_flat_pow_quotients
        I b v hv).2 hflat)).symm

/-- The constructed basis vectors are exactly the prescribed completed original lifts. -/
@[simp]
theorem basisOfQuotient_apply
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {ι : Type uι} [Finite ι]
    (b : Basis ι (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (v : ι → M)
    (hv : ∀ i : ι, (I • (⊤ : Submodule R M)).mkQ (v i) = b i)
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M)))) (i : ι) :
    AdicCompletion.basisOfQuotient I b v hv hflat i =
      AdicCompletion.of I M (v i) := by
  classical
  simp only [basisOfQuotient, Basis.coe_ofEquivFun, LinearEquiv.symm_symm,
    LinearEquiv.ofBijective_apply, Fintype.linearCombination_apply_single, one_smul]

/-- The inverse coordinate equivalence is the whole prescribed finite synthesis map. -/
theorem basisOfQuotient_equivFun_symm_toLinearMap
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {ι : Type uι} [Fintype ι]
    (b : Basis ι (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (v : ι → M)
    (hv : ∀ i : ι, (I • (⊤ : Submodule R M)).mkQ (v i) = b i)
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M)))) :
    (AdicCompletion.basisOfQuotient I b v hv hflat).equivFun.symm.toLinearMap =
      Fintype.linearCombination (AdicCompletion I R)
        (fun i : ι => AdicCompletion.of I M (v i)) := by
  apply LinearMap.ext
  intro a
  simp only [LinearEquiv.coe_toLinearMap, Basis.equivFun_symm_apply,
    Fintype.linearCombination_apply, basisOfQuotient_apply]

/-- Coordinates recover every coefficient of a completed finite linear combination. -/
@[simp]
theorem basisOfQuotient_repr_linearCombination_apply
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {ι : Type uι} [Fintype ι]
    (b : Basis ι (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (v : ι → M)
    (hv : ∀ i : ι, (I • (⊤ : Submodule R M)).mkQ (v i) = b i)
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M))))
    (a : ι → AdicCompletion I R) (i : ι) :
    (AdicCompletion.basisOfQuotient I b v hv hflat).repr
      (Fintype.linearCombination (AdicCompletion I R)
        (fun j : ι => AdicCompletion.of I M (v j)) a) i = a i := by
  simpa only [Fintype.linearCombination_apply, basisOfQuotient_apply] using
    congrFun ((basisOfQuotient I b v hv hflat).repr_sum_self a) i

/-- The entire coordinate vector of an original basis lift is the corresponding unit vector. -/
@[simp]
theorem basisOfQuotient_repr_of_lift
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {ι : Type uι} [Finite ι]
    (b : Basis ι (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (v : ι → M)
    (hv : ∀ i : ι, (I • (⊤ : Submodule R M)).mkQ (v i) = b i)
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M)))) (i : ι) :
    (AdicCompletion.basisOfQuotient I b v hv hflat).repr
      (AdicCompletion.of I M (v i)) = Finsupp.single i 1 := by
  simpa only [basisOfQuotient_apply] using
    (basisOfQuotient I b v hv hflat).repr_self i

/-- A completed basis on original vectors has unique evaluated coordinates in every
original ideal-power quotient. The inverse descends from original elements. -/
private theorem linearCombination_eq_eval_iff_of_basis
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {ι : Type uι} [Fintype ι]
    (B : Basis ι (AdicCompletion I R) (AdicCompletion I M))
    (v : ι → M) (hB : ∀ i, B i = of I M (v i))
    (n : ℕ) (x : AdicCompletion I M) (a : ι → R ⧸ I ^ n) :
    Fintype.linearCombination (R ⧸ I ^ n)
        (fun i => (I ^ n • (⊤ : Submodule R M)).mkQ (v i)) a = eval I M n x ↔
      a = fun i => evalₐ I n (B.repr x i) := by
  classical
  let S := AdicCompletion I R
  let H := AdicCompletion I M
  let A := R ⧸ I ^ n
  let N := I ^ n • (⊤ : Submodule R M)
  let Q := M ⧸ N
  let : IsScalarTower R A Q :=
    (Module.isTorsionBySet_quotient_ideal_smul M (I ^ n)).isScalarTower
  let coord (i : ι) : H →ₗ[R] S :=
    ((LinearMap.proj i : (ι → S) →ₗ[S] S).comp B.equivFun.toLinearMap).restrictScalars R
  let f : M →ₗ[R] (ι → A) := LinearMap.pi fun i =>
    (evalₐ I n).toLinearMap.comp ((coord i).comp (of I M))
  have hfker : N ≤ f.ker := by
    intro m hm
    change f m = 0
    refine Submodule.smul_induction_on hm (fun r hr y _ => ?_)
      (fun y z hy hz => ?_)
    · rw [map_smul]
      funext i
      change Ideal.Quotient.mk (I ^ n) r * f y i = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
    · rw [map_add, hy, hz, add_zero]
  let d₀ : Q →ₗ[R] (ι → A) := N.liftQ f hfker
  let d : Q →ₗ[A] (ι → A) := d₀.extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap R A))
  let t : (ι → A) →ₗ[A] Q :=
    Fintype.linearCombination A (fun i => N.mkQ (v i))
  have hdvec (i : ι) : d (N.mkQ (v i)) = Pi.single i 1 := by
    funext j
    change evalₐ I n (B.repr (of I M (v i)) j) = (Pi.single i (1 : A) : ι → A) j
    rw [← hB i, B.repr_self]
    by_cases hij : i = j <;> simp [hij]
  have hdleft (c : ι → A) : d (t c) = c := by
    simp only [t, Fintype.linearCombination_apply, map_sum, map_smul, hdvec]
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
      Finset.univ_sum_single c
  have hreconstruct (y : H) :
      t (fun i => evalₐ I n (B.repr y i)) = eval I M n y := by
    have h := congrArg (eval I M n) (B.sum_repr y)
    simpa only [t, Fintype.linearCombination_apply, map_sum, eval_smul_eq,
      hB, eval_of] using h
  constructor
  · intro h
    change t a = eval I M n x at h
    calc
      a = d (t a) := (hdleft a).symm
      _ = d (eval I M n x) := congrArg d h
      _ = (fun i => evalₐ I n (B.repr x i)) := by
        rw [← hreconstruct x, hdleft]
  · intro h
    rw [h]
    exact hreconstruct x

/-- At every original precision, synthesis equals evaluation exactly for the
coefficientwise evaluations of the constructed basis coordinates. -/
theorem basisOfQuotient_linearCombination_eq_eval_iff
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {ι : Type uι} [Fintype ι]
    (b : Basis ι (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (v : ι → M)
    (hv : ∀ i : ι, (I • (⊤ : Submodule R M)).mkQ (v i) = b i)
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M))))
    (n : ℕ) (x : AdicCompletion I M) (a : ι → R ⧸ I ^ n) :
    Fintype.linearCombination (R ⧸ I ^ n)
        (fun i : ι => (I ^ n • (⊤ : Submodule R M)).mkQ (v i)) a =
        AdicCompletion.eval I M n x ↔
      a = fun i : ι => AdicCompletion.evalₐ I n
        ((AdicCompletion.basisOfQuotient I b v hv hflat).repr x i) :=
  linearCombination_eq_eval_iff_of_basis I (basisOfQuotient I b v hv hflat) v
    (basisOfQuotient_apply I b v hv hflat) n x a

/-- Normalized first residues of completed basis coordinates are the original
residue-basis coordinates of the canonical first projection. -/
@[simp]
theorem basisOfQuotient_evalOneₐ_repr
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {ι : Type uι} [Finite ι]
    (b : Basis ι (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (v : ι → M)
    (hv : ∀ i : ι, (I • (⊤ : Submodule R M)).mkQ (v i) = b i)
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M))))
    (x : AdicCompletion I M) (i : ι) :
    AdicCompletion.evalOneₐ I
        ((AdicCompletion.basisOfQuotient I b v hv hflat).repr x i) =
      b.repr (AdicCompletion.evalOneₛₗ I M x) i := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have he_smul (s : AdicCompletion I R) (y : AdicCompletion I M) :
      evalOneₛₗ I M (s • y) = evalOneₐ I s • evalOneₛₗ I M y :=
    (evalOneₛₗ I M).map_smulₛₗ s y
  have hsum :
      (∑ j : ι, evalOneₐ I ((basisOfQuotient I b v hv hflat).repr x j) • b j) =
        evalOneₛₗ I M x := by
    simpa only [map_sum, he_smul, basisOfQuotient_apply, evalOneₛₗ_of, hv] using
      congrArg (evalOneₛₗ I M) ((basisOfQuotient I b v hv hflat).sum_repr x)
  have hcoord := congrFun (b.repr_sum_self
    (fun j : ι => evalOneₐ I ((basisOfQuotient I b v hv hflat).repr x j))) i
  rw [hsum] at hcoord
  exact hcoord.symm

/-- A finite free original first quotient and flat positive original quotients
make the raw completion free over its completed coefficient ring. -/
theorem moduleFree_of_flat_pow_quotients
    {R : Type uR} [CommRing R] (I : Ideal R)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    [Module.Free (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M)))) :
    Module.Free (AdicCompletion I R) (AdicCompletion I M) := by
  let b := Module.Free.chooseBasis
    (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))
  let v : Module.Free.ChooseBasisIndex
      (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) → M :=
    fun i => Classical.choose
      ((I • (⊤ : Submodule R M)).mkQ_surjective (b i))
  exact Module.Free.of_basis
    (basisOfQuotient I b v
      (fun i => Classical.choose_spec
        ((I • (⊤ : Submodule R M)).mkQ_surjective (b i))) hflat)

end AdicCompletion
