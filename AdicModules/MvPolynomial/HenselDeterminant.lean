/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import AdicModules.Henselian.Basic
import AdicModules.MvPolynomial.Evaluation
import AdicModules.MvPolynomial.JacobianPerturbation
public import Mathlib.LinearAlgebra.Pi

public import AdicModules.MvPolynomial.Hensel
import AdicModules.LinearAlgebra.Matrix.DeterminantPerturbation
import AdicModules.MvPolynomial.Evaluation
import AdicModules.RingTheory.HenselianTransport
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.Ideal
import MultivariatePolynomials.Taylor

/-!
# Strong Hensel lifting for finite polynomial systems

A finite square polynomial system over a commutative semiring, evaluated through
an arbitrary coefficient homomorphism into a Henselian pair `(R, I)`, admits a root
with prescribed target values when its errors lie in `(d²) I`, where `J` is the
evaluated Jacobian and `d = J.det`. The correction is `d • J.adjugate.mulVec z`
for a parameter `z` coordinatewise in `I`, and hence lies in `(d) I`. Evaluation
maps this adjugate neighborhood onto the coordinatewise `(d²) I` neighborhood of
the original value. No regularity assumption on `d` is needed, and the target
values need not come from the source semiring. If the evaluated determinant is
regular, this root is unique in the same correction box, by injectivity of the
original evaluation map on that box.

For a Henselian ideal `M`, if `(d) = M ^ v` with `v ≤ s`, errors in
`M ^ (2 * s + 1)` give a root in the `M ^ (s + 1)` correction box. This root is
unique in the same box when `d` is regular.

The proof applies the first-order Taylor remainder theorem to the adjugate
substitution in a polynomial ring over `R`. Extracting witnesses from principal
ideal products gives a normalized system with value in `I` and identity Jacobian
at zero. The existing unit-Jacobian Hensel theorem supplies its root; forward
evaluation recovers a root of the original system. Neither `d` nor `d²` is
cancelled.

The whole coordinatewise `(d) I` neighborhood has a coupled image: its
value displacements are exactly `(d • J).mulVec x` for `I`-valued vectors `x`.
This follows by choosing a polynomial secant matrix, normalizing with the
adjugate, and applying the adjugate-neighborhood image theorem to the resulting
system with identity Jacobian at zero.

## References

The Taylor input is
`MvPolynomial.eval₂_sub_eval₂_sub_sum_pderiv_mem_sq`.
The normalized system is lifted by
`HenselianRing.existsUnique_root_of_isUnit_det_jacobian`.
-/

@[expose] public section

namespace MvPolynomial

universe u v w

private theorem mulVec_map_adjugate_X
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι R) :
    (J.map (C : R →+* MvPolynomial ι R)).mulVec
        ((J.adjugate.map (C : R →+* MvPolynomial ι R)).mulVec X) =
      fun i => C J.det * X i := by
  have hAdj :
      J.adjugate.map (C : R →+* MvPolynomial ι R) =
        (J.map (C : R →+* MvPolynomial ι R)).adjugate :=
    (C : R →+* MvPolynomial ι R).map_adjugate J
  have hDet :
      (J.map (C : R →+* MvPolynomial ι R)).det = C J.det :=
    ((C : R →+* MvPolynomial ι R).map_det J).symm
  have h := Matrix.mulVec_cramer (J.map (C : R →+* MvPolynomial ι R))
    (X : ι → MvPolynomial ι R)
  rw [Matrix.cramer_eq_adjugate_mulVec, ← hAdj, hDet] at h
  funext i
  simpa only [Pi.smul_apply, smul_eq_mul] using congrFun h i

private theorem mulVec_X_mem_idealOfVars
    {R : Type u} [CommSemiring R] {ι : Type v} [Fintype ι] {η : Type w}
    (A : Matrix η ι (MvPolynomial ι R)) (i : η) :
    A.mulVec X i ∈ idealOfVars ι R := by
  rw [Matrix.mulVec_apply_eq_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact (idealOfVars ι R).mul_mem_left (A i j)
    (Ideal.subset_span (Set.mem_range_self j))

section

variable {R : Type u} [CommSemiring R] {σ : Type v}

private theorem eval_zero_of_mem_idealOfVars_sq
    {p : MvPolynomial σ R} (hp : p ∈ (idealOfVars σ R) ^ 2) :
    eval (fun _ => 0) p = 0 ∧ ∀ j, eval (fun _ => 0) (pderiv j p) = 0 := by
  classical
  have hcoeff := (mem_pow_idealOfVars_iff' 2 p).mp hp
  constructor
  · rw [eval_zero', constantCoeff_eq]
    exact hcoeff 0 (by simp)
  · intro j
    have hj : p.coeff (Finsupp.single j 1) = 0 := hcoeff _ (by simp)
    rw [eval_zero', constantCoeff_eq, coeff_pderiv]
    simpa using hj

private theorem eval_zero_normalized [DecidableEq σ]
    (e : R) (i : σ) {Q : MvPolynomial σ R}
    (hQ : Q ∈ (idealOfVars σ R) ^ 2) :
    eval (fun _ => 0) (C e + X i + Q) = e ∧
      ∀ j, eval (fun _ => 0) (pderiv j (C e + X i + Q)) =
        if i = j then 1 else 0 := by
  obtain ⟨hQ0, hQ1⟩ := eval_zero_of_mem_idealOfVars_sq hQ
  constructor
  · simp only [map_add, eval_C, eval_X, hQ0, add_zero]
  · intro j
    simp only [map_add, pderiv_C, zero_add, hQ1 j, add_zero]
    by_cases hij : i = j
    · subst j
      simp
    · rw [pderiv_X_of_ne hij, map_zero]
      simp [hij]

end

private theorem eval_normalized_system
    {R : Type u} [CommSemiring R] {ι : Type v} [DecidableEq ι]
    (e : ι → R) (Q : ι → MvPolynomial ι R)
    (hQ : ∀ i, Q i ∈ idealOfVars ι R ^ 2) :
    (fun i => eval (fun _ => 0) (C (e i) + X i + Q i)) = e ∧
      (fun i j => eval (fun _ => 0) (pderiv j (C (e i) + X i + Q i))) =
        (1 : Matrix ι ι R) := by
  constructor
  · funext i
    exact (eval_zero_normalized (e i) i (hQ i)).1
  · funext i j
    simpa only [Matrix.one_apply] using (eval_zero_normalized (e i) i (hQ i)).2 j

/-- Extract normalized witnesses from a squared-ideal remainder, without cancelling the
determinant. -/
private theorem exists_normalization_of_remainder_sq
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (J : Matrix ι ι R) (s t : ι → R) (E : ι → MvPolynomial ι R)
    (hs : ∀ i, s i - t i ∈ Ideal.span ({J.det ^ 2} : Set R) * I)
    (hrem : ∀ i, E i - C (s i) -
      (J.map (C : R →+* MvPolynomial ι R)).mulVec
        (fun j => C J.det *
          (J.adjugate.map (C : R →+* MvPolynomial ι R)).mulVec X j) i ∈
        (Ideal.span ({C J.det} : Set (MvPolynomial ι R)) * idealOfVars ι R) ^ 2) :
    ∃ e : ι → R, (∀ i, e i ∈ I) ∧
      ∃ Q : ι → MvPolynomial ι R, (∀ i, Q i ∈ idealOfVars ι R ^ 2) ∧
        ∀ i, E i - C (t i) = C (J.det ^ 2) * (C (e i) + X i + Q i) := by
  have heExists (i : ι) : ∃ e ∈ I, J.det ^ 2 * e = s i - t i :=
    Ideal.mem_span_singleton_mul.mp (hs i)
  let e : ι → R := fun i => Classical.choose (heExists i)
  have heI (i : ι) : e i ∈ I := (Classical.choose_spec (heExists i)).1
  have heEq (i : ι) : J.det ^ 2 * e i = s i - t i :=
    (Classical.choose_spec (heExists i)).2
  have hlinear (i : ι) :
      (J.map (C : R →+* MvPolynomial ι R)).mulVec
        (fun j => C J.det *
          (J.adjugate.map (C : R →+* MvPolynomial ι R)).mulVec X j) i =
        C (J.det ^ 2) * X i := by
    have h := congrFun
      (Matrix.mulVec_smul
        (J.map (C : R →+* MvPolynomial ι R))
        (C J.det : MvPolynomial ι R)
        ((J.adjugate.map (C : R →+* MvPolynomial ι R)).mulVec X)) i
    have hsmul :
        (C J.det : MvPolynomial ι R) •
            ((J.adjugate.map (C : R →+* MvPolynomial ι R)).mulVec X) =
          fun j => C J.det *
            (J.adjugate.map (C : R →+* MvPolynomial ι R)).mulVec X j := by
      funext j
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsmul, mulVec_map_adjugate_X] at h
    simpa only [Pi.smul_apply, smul_eq_mul, pow_two, map_mul, mul_assoc] using h
  have hsq :
      (Ideal.span ({C J.det} : Set (MvPolynomial ι R)) * idealOfVars ι R) ^ 2 =
        Ideal.span ({C (J.det ^ 2)} : Set (MvPolynomial ι R)) *
          idealOfVars ι R ^ 2 := by
    rw [mul_pow, Ideal.span_singleton_pow, map_pow]
  have hQExists (i : ι) :
      ∃ q ∈ idealOfVars ι R ^ 2,
        C (J.det ^ 2) * q = E i - C (s i) - C (J.det ^ 2) * X i := by
    apply Ideal.mem_span_singleton_mul.mp
    rw [← hsq, ← hlinear i]
    exact hrem i
  let Q : ι → MvPolynomial ι R := fun i => Classical.choose (hQExists i)
  have hQmem (i : ι) : Q i ∈ idealOfVars ι R ^ 2 :=
    (Classical.choose_spec (hQExists i)).1
  have hQeq (i : ι) :
      C (J.det ^ 2) * Q i = E i - C (s i) - C (J.det ^ 2) * X i :=
    (Classical.choose_spec (hQExists i)).2
  refine ⟨e, heI, Q, hQmem, ?_⟩
  intro i
  have heC :
      (C (s i) : MvPolynomial ι R) - C (t i) =
        C (J.det ^ 2) * C (e i) := by
    rw [← map_sub, ← heEq i, map_mul]
  calc
    E i - C (t i) =
        (E i - C (s i) - C (J.det ^ 2) * X i) + C (J.det ^ 2) * X i +
          (C (s i) - C (t i)) := by
      rw [sub_add_cancel, sub_add_sub_cancel]
    _ = C (J.det ^ 2) * Q i + C (J.det ^ 2) * X i +
        C (J.det ^ 2) * C (e i) := by rw [← hQeq i, heC]
    _ = C (J.det ^ 2) * (Q i + X i + C (e i)) := by rw [mul_add, mul_add]
    _ = C (J.det ^ 2) * (C (e i) + X i + Q i) := by
      rw [add_comm (Q i + X i) (C (e i)), add_comm (Q i) (X i), ← add_assoc]

end MvPolynomial

namespace HenselianRing

universe u v w

open MvPolynomial
open scoped BigOperators

private theorem exists_root_of_normalized_identity
    {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {ι : Type w} [Fintype ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a t : ι → R)
    (M : Matrix ι ι R) (d : R) (e : ι → R) (Q : ι → MvPolynomial ι R)
    (he : ∀ i, e i ∈ I) (hQ : ∀ i, Q i ∈ idealOfVars ι R ^ 2)
    (hP : ∀ i,
      eval₂ (MvPolynomial.C.comp φ)
          (fun j => MvPolynomial.C (a j) + MvPolynomial.C d *
            ((M.map (MvPolynomial.C : R →+* MvPolynomial ι R)).mulVec X) j)
          (P i) - MvPolynomial.C (t i) =
        MvPolynomial.C (d ^ 2) * (MvPolynomial.C (e i) + X i + Q i)) :
    ∃ z : ι → R, (∀ i, z i ∈ I) ∧
      ∀ i, eval₂ φ (a + d • M.mulVec z) (P i) = t i := by
  classical
  let F : ι → MvPolynomial ι R := fun i => MvPolynomial.C (e i) + X i + Q i
  have hF := MvPolynomial.eval_normalized_system e Q hQ
  have hF0 : ∀ i, eval (fun _ => 0) (F i) ∈ I := by
    intro i
    change eval (fun _ => 0) (MvPolynomial.C (e i) + X i + Q i) ∈ I
    rw [congrFun hF.1 i]
    exact he i
  have hFJ : IsUnit (Matrix.det
      (fun i j => eval (fun _ => 0) (pderiv j (F i)))) := by
    change IsUnit (Matrix.det
      (fun i j => eval (fun _ => 0) (pderiv j (MvPolynomial.C (e i) + X i + Q i))))
    rw [hF.2, Matrix.det_one]
    exact isUnit_one
  obtain ⟨z, hz⟩ :=
    (existsUnique_root_of_isUnit_det_jacobian F (fun _ => 0) hF0 hFJ).exists
  have hzI : ∀ j, z j ∈ I := by
    intro j
    simpa only [sub_zero] using hz.2 j
  let b : ι → R := fun j => a j + d * (M.mulVec z) j
  have hM :
      (M.map (MvPolynomial.C : R →+* MvPolynomial ι R)).map (eval z) = M := by
    funext j k
    exact eval_C (M j k)
  have hX : (eval z) ∘ (X : ι → MvPolynomial ι R) = z := by
    funext j
    exact eval_X j
  have hlin (j : ι) :
      eval z (((M.map (MvPolynomial.C : R →+* MvPolynomial ι R)).mulVec X) j) =
        (M.mulVec z) j := by
    simpa only [hM, hX] using
      (eval z).map_mulVec (M.map (MvPolynomial.C : R →+* MvPolynomial ι R))
        (X : ι → MvPolynomial ι R) j
  have hcoeff :
      (eval z).comp ((MvPolynomial.C : R →+* MvPolynomial ι R).comp φ) = φ := by
    ext c
    exact eval_C (φ c)
  have hsubst :
      (fun j => eval z (MvPolynomial.C (a j) + MvPolynomial.C d *
        ((M.map (MvPolynomial.C : R →+* MvPolynomial ι R)).mulVec X) j)) = b := by
    funext j
    change eval z (MvPolynomial.C (a j) + MvPolynomial.C d *
      ((M.map (MvPolynomial.C : R →+* MvPolynomial ι R)).mulVec X) j) =
        a j + d * (M.mulVec z) j
    simp only [map_add, map_mul, eval_C, hlin]
  refine ⟨z, hzI, ?_⟩
  intro i
  change eval₂ φ b (P i) = t i
  have h := congrArg (eval z) (hP i)
  simp only [map_sub, eval_eval₂, hcoeff, hsubst, eval_C, map_mul] at h
  change eval₂ φ b (P i) - t i = d ^ 2 * eval z (F i) at h
  rw [hz.1 i, mul_zero] at h
  exact sub_eq_zero.mp h

/-- Strong Hensel lifting with an adjugate correction parameter. Errors in
`(d²) I` admit a parameter `z` coordinatewise in `I` whose image under
`d • J.adjugate` corrects the point to the prescribed target values. The coefficient
semiring, target ring, and index universes are independent, and no regularity of
the determinant or coefficient preimages of the target values are required. -/
theorem exists_eval₂_eq_of_sub_mem_det_sq_mul_adjugate
    {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a t : ι → R) :
    let J : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := J.det
    (∀ i, eval₂ φ a (P i) - t i ∈ Ideal.span ({d ^ 2} : Set R) * I) →
      ∃ z : ι → R, (∀ i, z i ∈ I) ∧
        ∀ i, eval₂ φ (a + d • J.adjugate.mulVec z) (P i) = t i := by
  classical
  let J : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
  change (∀ i, eval₂ φ a (P i) - t i ∈ Ideal.span ({J.det ^ 2} : Set R) * I) →
    ∃ z : ι → R, (∀ i, z i ∈ I) ∧
      ∀ i, eval₂ φ (a + J.det • J.adjugate.mulVec z) (P i) = t i
  intro ha
  let L : ι → MvPolynomial ι R :=
    (J.adjugate.map (MvPolynomial.C : R →+* MvPolynomial ι R)).mulVec X
  let c : ι → MvPolynomial ι R := fun j => MvPolynomial.C (a j)
  let polyPoint : ι → MvPolynomial ι R :=
    fun j => MvPolynomial.C (a j) + MvPolynomial.C J.det * L j
  let K : Ideal (MvPolynomial ι R) :=
    Ideal.span ({MvPolynomial.C J.det} : Set (MvPolynomial ι R)) * idealOfVars ι R
  have hdelta (j : ι) : polyPoint j - c j = MvPolynomial.C J.det * L j := by
    dsimp only [polyPoint, c]
    exact add_sub_cancel_left _ _
  have hmem (j : ι) : polyPoint j - c j ∈ K := by
    rw [hdelta]
    exact Ideal.mul_mem_mul (Ideal.subset_span (by simp))
      (MvPolynomial.mulVec_X_mem_idealOfVars
        (J.adjugate.map (MvPolynomial.C : R →+* MvPolynomial ι R)) j)
  have hseed (p : MvPolynomial ι C) :
      eval₂ (MvPolynomial.C.comp φ) c p = MvPolynomial.C (eval₂ φ a p) := by
    exact (eval₂_comp_left
      (MvPolynomial.C : R →+* MvPolynomial ι R) φ a p).symm
  let s : ι → R := fun i => eval₂ φ a (P i)
  let E : ι → MvPolynomial ι R := fun i => eval₂ (MvPolynomial.C.comp φ) polyPoint (P i)
  have hrem (i : ι) : E i - MvPolynomial.C (s i) -
      (J.map (MvPolynomial.C : R →+* MvPolynomial ι R)).mulVec
        (fun j => MvPolynomial.C J.det *
          (J.adjugate.map (MvPolynomial.C : R →+* MvPolynomial ι R)).mulVec X j) i ∈
        K ^ 2 := by
    have hTaylor := MvPolynomial.eval₂_sub_eval₂_sub_sum_pderiv_mem_sq
      K (MvPolynomial.C.comp φ) c polyPoint (P i) (fun j _ => hmem j)
    have hsum :
        (P i).vars.sum (fun j => eval₂ (MvPolynomial.C.comp φ) c (pderiv j (P i)) *
          (polyPoint j - c j)) =
        ∑ j, eval₂ (MvPolynomial.C.comp φ) c (pderiv j (P i)) *
          (polyPoint j - c j) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      rw [pderiv_eq_zero_of_notMem_vars hj, eval₂_zero, zero_mul]
    have hlinear :
        (∑ j, eval₂ (MvPolynomial.C.comp φ) c (pderiv j (P i)) *
          (polyPoint j - c j)) =
        (J.map (MvPolynomial.C : R →+* MvPolynomial ι R)).mulVec
          (fun j => MvPolynomial.C J.det *
            (J.adjugate.map (MvPolynomial.C : R →+* MvPolynomial ι R)).mulVec X j) i := by
      rw [Matrix.mulVec_apply_eq_sum]
      apply Finset.sum_congr rfl
      intro j _
      change eval₂ (MvPolynomial.C.comp φ) c (pderiv j (P i)) * (polyPoint j - c j) =
        MvPolynomial.C (eval₂ φ a (pderiv j (P i))) * (MvPolynomial.C J.det * L j)
      rw [hseed, hdelta]
    rw [hseed (P i), hsum, hlinear] at hTaylor
    exact hTaylor
  obtain ⟨e, heI, Q, hQ, hP⟩ :=
    MvPolynomial.exists_normalization_of_remainder_sq I J s t E ha hrem
  exact exists_root_of_normalized_identity φ P a t J.adjugate J.det e Q heI hQ hP

/-- Strong Hensel existence for a finite square system with errors in `(d²) I`,
where `d` is its evaluated Jacobian determinant. The root differs from the supplied
point by an element of `(d) I` in each coordinate. The coefficient semiring and the
Henselian target ring are independent, the target values are arbitrary, and no
regularity assumption on the determinant is required. -/
theorem exists_eval₂_eq_of_sub_mem_det_sq_mul
    {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a t : ι → R) :
    let J : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := J.det
    (∀ i, eval₂ φ a (P i) - t i ∈ Ideal.span ({d ^ 2} : Set R) * I) →
      ∃ b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
        ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I := by
  intro J d ha
  obtain ⟨z, hzI, hz⟩ := exists_eval₂_eq_of_sub_mem_det_sq_mul_adjugate φ P a t ha
  refine ⟨a + d • J.adjugate.mulVec z, hz, ?_⟩
  intro i
  apply Ideal.mem_span_singleton_mul.mpr
  refine ⟨J.adjugate.mulVec z i, ?_, ?_⟩
  · rw [Matrix.mulVec_apply_eq_sum]
    exact Submodule.sum_mem _ fun j _ => I.mul_mem_left (J.adjugate i j) (hzI j)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]

private theorem eval₂_sub_mem_det_sq_mul_adjugate
    {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    {I : Ideal R} {ι : Type w} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a z : ι → R)
    (hz : ∀ i, z i ∈ I) :
    let J : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := J.det
    ∀ i, eval₂ φ (a + d • J.adjugate.mulVec z) (P i) - eval₂ φ a (P i) ∈
      Ideal.span ({d ^ 2} : Set R) * I := by
  classical
  intro J d i
  let b : ι → R := a + d • J.adjugate.mulVec z
  let K : Ideal R := Ideal.span ({d} : Set R) * I
  have hdelta (j : ι) : b j - a j = d * J.adjugate.mulVec z j := by
    simp only [b, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  have hmem (j : ι) : b j - a j ∈ K := by
    rw [hdelta]
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨J.adjugate.mulVec z j, ?_, rfl⟩
    rw [Matrix.mulVec_apply_eq_sum]
    exact Submodule.sum_mem _ fun k _ => I.mul_mem_left (J.adjugate j k) (hz k)
  have hTaylor := MvPolynomial.eval₂_sub_eval₂_sub_sum_pderiv_mem_sq
    K φ a b (P i) (fun j _ => hmem j)
  have hsum :
      (P i).vars.sum (fun j => eval₂ φ a (pderiv j (P i)) * (b j - a j)) =
        ∑ j, eval₂ φ a (pderiv j (P i)) * (b j - a j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [pderiv_eq_zero_of_notMem_vars hj, eval₂_zero, zero_mul]
  have hlinear :
      (∑ j, eval₂ φ a (pderiv j (P i)) * (b j - a j)) = d ^ 2 * z i := by
    have hdeltaVec : (fun j => b j - a j) = d • J.adjugate.mulVec z := by
      funext j
      exact hdelta j
    change J.mulVec (fun j => b j - a j) i = d ^ 2 * z i
    rw [hdeltaVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, pow_two, mul_assoc, d]
  have hsq : K ^ 2 = Ideal.span ({d ^ 2} : Set R) * I ^ 2 := by
    dsimp only [K]
    rw [mul_pow, Ideal.span_singleton_pow]
  rw [hsum, hlinear, hsq] at hTaylor
  obtain ⟨q, hq, hqeq⟩ := Ideal.mem_span_singleton_mul.mp hTaylor
  have hrem : eval₂ φ b (P i) - eval₂ φ a (P i) - d ^ 2 * z i ∈
      Ideal.span ({d ^ 2} : Set R) * I :=
    Ideal.mem_span_singleton_mul.mpr
      ⟨q, Ideal.pow_le_self (I := I) (n := 2) (by decide) hq, hqeq⟩
  have hlin : d ^ 2 * z i ∈ Ideal.span ({d ^ 2} : Set R) * I :=
    Ideal.mem_span_singleton_mul.mpr ⟨z i, hz i, rfl⟩
  simpa only [sub_add_cancel] using
    (Ideal.span ({d ^ 2} : Set R) * I).add_mem hrem hlin

/-- Evaluation maps the determinant-scaled adjugate neighborhood of a point onto
exactly the coordinatewise `(d²) I` neighborhood of its value. The forward
inclusion is Taylor expansion and the adjugate identity; Henselianity supplies
the reverse inclusion without any regularity assumption on the determinant. -/
theorem image_eval₂_adjugate_neighborhood
    {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a : ι → R) :
    let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := A.det
    (fun b : ι → R => fun i => eval₂ φ b (P i)) ''
        {b : ι → R | ∃ z : ι → R, (∀ i, z i ∈ I) ∧
          b = a + d • A.adjugate.mulVec z} =
      {t : ι → R | ∀ i,
        t i - eval₂ φ a (P i) ∈ Ideal.span ({d ^ 2} : Set R) * I} := by
  intro A d
  ext t
  constructor
  · rintro ⟨b, ⟨z, hz, rfl⟩, rfl⟩
    exact eval₂_sub_mem_det_sq_mul_adjugate φ P a z hz
  · intro ht
    have ha : ∀ i, eval₂ φ a (P i) - t i ∈ Ideal.span ({d ^ 2} : Set R) * I := by
      intro i
      simpa only [neg_sub] using (Ideal.span ({d ^ 2} : Set R) * I).neg_mem (ht i)
    obtain ⟨z, hzI, hz⟩ := exists_eval₂_eq_of_sub_mem_det_sq_mul_adjugate φ P a t ha
    refine ⟨a + d • A.adjugate.mulVec z, ⟨z, hzI, rfl⟩, ?_⟩
    funext i
    exact hz i

/-- For a finite square polynomial system over a Henselian pair with errors in `(d²) I`,
the prescribed fiber in the `(d) I` correction box consists of exactly one point if and
only if the Jacobian at the center has trivial kernel on vectors with coordinates in
`(d) I`. No regularity of the determinant is needed: existence is supplied by
`exists_eval₂_eq_of_sub_mem_det_sq_mul`. -/
theorem existsUnique_eval₂_eq_iff_mulVec_eq_zero_of_sub_mem_det_sq_mul
    {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a t : ι → R) :
    let J : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := J.det
    (∀ i, eval₂ φ a (P i) - t i ∈ Ideal.span ({d ^ 2} : Set R) * I) →
      ((∃! b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
          ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I) ↔
        ∀ z : ι → R, (∀ i, z i ∈ Ideal.span ({d} : Set R) * I) →
          J.mulVec z = 0 → z = 0) := by
  intro J d ha
  have hI : I ≤ Ideal.jacobson (⊥ : Ideal R) := HenselianRing.jac
  have hfiber :=
    MvPolynomial.existsUnique_eval₂_eq_iff_exists_and_mulVec_eq_zero φ P a I t hI
  have hex : ∃ b : ι → R, (∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I) ∧
      (fun i => eval₂ φ b (P i)) = t := by
    obtain ⟨b, hbt, hba⟩ := exists_eval₂_eq_of_sub_mem_det_sq_mul φ P a t ha
    exact ⟨b, hba, funext hbt⟩
  constructor
  · rintro ⟨b, hb, huniq⟩
    apply (hfiber.mp ?_).2
    refine ⟨b, ⟨hb.2, funext hb.1⟩, ?_⟩
    intro c hc
    exact huniq c ⟨fun i => congrFun hc.2 i, hc.1⟩
  · intro hker
    obtain ⟨b, hb, huniq⟩ := hfiber.mpr ⟨hex, hker⟩
    refine ⟨b, ⟨fun i => congrFun hb.2 i, hb.1⟩, ?_⟩
    intro c hc
    exact huniq c ⟨hc.2, funext hc.1⟩

/-- A finite square polynomial system with errors in `(d²) I` has a unique root
in the `(d) I` correction box when its evaluated Jacobian determinant `d` is regular.
Regularity is required only for uniqueness; existence is supplied by
`exists_eval₂_eq_of_sub_mem_det_sq_mul`. The source is a commutative semiring,
the coefficient homomorphism is arbitrary, and the target values lie in the
Henselian target ring without any source-image restriction. -/
theorem existsUnique_eval₂_eq_of_sub_mem_det_sq_mul
    {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a t : ι → R) :
    let J : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := J.det
    IsRegular d →
      (∀ i, eval₂ φ a (P i) - t i ∈ Ideal.span ({d ^ 2} : Set R) * I) →
        ∃! b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
          ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I := by
  dsimp only
  intro hd ha
  apply (existsUnique_eval₂_eq_iff_mulVec_eq_zero_of_sub_mem_det_sq_mul φ P a t ha).mpr
  intro z _ hJz
  exact Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero
    hd.mem_nonZeroDivisors hJz

universe uCoeff uTarget uIndex

/-- If the evaluated Jacobian determinant generates `M ^ v`, errors in
`M ^ (2 * v + k)` give a root in the `M ^ (v + k)` correction box for every
positive `k`. This is the ideal-power form of
`exists_eval₂_eq_of_sub_mem_det_sq_mul`: Henselianity of `M ^ k` follows from
that of `M`, and no regularity of the determinant is required. -/
theorem exists_eval₂_eq_of_sub_mem_pow_two_mul_add
    {C : Type uCoeff} [CommSemiring C]
    {R : Type uTarget} [CommRing R]
    {M : Ideal R} [HenselianRing R M]
    {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C)
    (a t : ι → R) (v k : ℕ) :
    let J : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := J.det
    0 < k →
      Ideal.span ({d} : Set R) = M ^ v →
        (∀ i, eval₂ φ a (P i) - t i ∈ M ^ (2 * v + k)) →
          ∃ b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
            ∀ i, b i - a i ∈ M ^ (v + k) := by
  intro J d hk hspan ha
  let : HenselianRing R (M ^ k) :=
    HenselianRing.of_le (I := M ^ k) (J := M)
      (Ideal.pow_le_self (I := M) (n := k) (by omega))
  have hbox : Ideal.span ({d} : Set R) * M ^ k = M ^ (v + k) := by
    rw [hspan, ← pow_add]
  have herr : Ideal.span ({d ^ 2} : Set R) * M ^ k = M ^ (2 * v + k) := by
    calc
      Ideal.span ({d ^ 2} : Set R) * M ^ k =
          Ideal.span ({d} : Set R) ^ 2 * M ^ k := by
        rw [Ideal.span_singleton_pow]
      _ = (M ^ v) ^ 2 * M ^ k := by rw [hspan]
      _ = M ^ (v + v + k) := by rw [pow_two, ← pow_add, ← pow_add]
      _ = M ^ (2 * v + k) := by congr 1; omega
  have ha' : ∀ i, eval₂ φ a (P i) - t i ∈
      Ideal.span ({d ^ 2} : Set R) * M ^ k := by
    simpa only [herr] using ha
  have hroot : ∃ b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
      ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * M ^ k :=
    HenselianRing.exists_eval₂_eq_of_sub_mem_det_sq_mul (I := M ^ k) φ P a t ha'
  simpa only [hbox] using hroot

/-- For a Henselian pair, a residual in `M ^ (2 * v + k)` has a unique root in the
`M ^ (v + k)` neighbourhood exactly when the evaluated Jacobian has zero kernel
on that same neighbourhood. Here `k > 0` and the determinant generates `M ^ v`. -/
theorem existsUnique_eval₂_eq_iff_mulVec_eq_zero_of_sub_mem_pow_two_mul_add
    {C : Type uCoeff} [CommSemiring C]
    {R : Type uTarget} [CommRing R]
    {M : Ideal R} [HenselianRing R M]
    {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C)
    (a t : ι → R) (v k : ℕ) :
    let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := A.det
    0 < k →
      Ideal.span ({d} : Set R) = M ^ v →
        (∀ i, eval₂ φ a (P i) - t i ∈ M ^ (2 * v + k)) →
          ((∃! b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
              ∀ i, b i - a i ∈ M ^ (v + k)) ↔
            ∀ z : ι → R, (∀ i, z i ∈ M ^ (v + k)) →
              A.mulVec z = 0 → z = 0) := by
  dsimp only
  intro hk hd hP
  let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
  let d : R := A.det
  change Ideal.span ({d} : Set R) = M ^ v at hd
  let : HenselianRing R (M ^ k) :=
    HenselianRing.of_le (Ideal.pow_le_self (ne_of_gt hk))
  have hbox : Ideal.span ({d} : Set R) * M ^ k = M ^ (v + k) := by
    rw [hd, ← pow_add]
  have hbox₂ : Ideal.span ({d ^ 2} : Set R) * M ^ k = M ^ (2 * v + k) := by
    rw [← Ideal.span_singleton_pow, hd, ← pow_mul, ← pow_add, Nat.mul_comm v 2]
  dsimp only [d, A] at hbox hbox₂
  simpa only [hbox] using
    (existsUnique_eval₂_eq_iff_mulVec_eq_zero_of_sub_mem_det_sq_mul
      (I := M ^ k) φ P a t (by simpa only [hbox₂] using hP))

/-- A determinant ideal `M ^ v` and errors in `M ^ (2 * s + 1)` give a root in the
`M ^ (s + 1)` correction box when `v ≤ s`, without regularity of the determinant. -/
theorem exists_eval₂_eq_of_sub_mem_pow
    {C : Type uCoeff} [CommSemiring C]
    {R : Type uTarget} [CommRing R]
    {M : Ideal R} [HenselianRing R M]
    {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C)
    (a t : ι → R) (s v : ℕ) :
    let J : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := J.det
    v ≤ s →
      Ideal.span ({d} : Set R) = M ^ v →
        (∀ i, eval₂ φ a (P i) - t i ∈ M ^ (2 * s + 1)) →
          ∃ b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
            ∀ i, b i - a i ∈ M ^ (s + 1) := by
  intro J d hv hspan ha
  let k : ℕ := s + 1 - v
  have hk : 0 < k := by
    dsimp only [k]
    omega
  have hvk : v + k = s + 1 := by
    dsimp only [k]
    omega
  have hprec : 2 * v + k ≤ 2 * s + 1 := by
    dsimp only [k]
    omega
  have ha' : ∀ i, eval₂ φ a (P i) - t i ∈ M ^ (2 * v + k) := by
    intro i
    exact Ideal.pow_le_pow_right (I := M) hprec (ha i)
  have hroot : ∃ b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
      ∀ i, b i - a i ∈ M ^ (v + k) :=
    exists_eval₂_eq_of_sub_mem_pow_two_mul_add φ P a t v k hk hspan ha'
  simpa only [hvk] using hroot

/-- If the evaluated Jacobian determinant is regular, the root with corrections in
`M ^ (s + 1)` is unique under the same determinant-ideal and error bounds. -/
theorem existsUnique_eval₂_eq_of_sub_mem_pow
    {C : Type uCoeff} [CommSemiring C]
    {R : Type uTarget} [CommRing R]
    {M : Ideal R} [HenselianRing R M]
    {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C)
    (a t : ι → R) (s v : ℕ) :
    let J : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := J.det
    v ≤ s →
      Ideal.span ({d} : Set R) = M ^ v →
        IsRegular d →
          (∀ i, eval₂ φ a (P i) - t i ∈ M ^ (2 * s + 1)) →
            ∃! b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
              ∀ i, b i - a i ∈ M ^ (s + 1) := by
  dsimp only
  intro hvs hd hreg hres
  let k : ℕ := s + 1 - v
  have hk : 0 < k := by
    dsimp [k]
    omega
  have hvk : v + k = s + 1 := by
    dsimp [k]
    omega
  have hres' : ∀ i, eval₂ φ a (P i) - t i ∈ M ^ (2 * v + k) := by
    intro i
    exact Ideal.pow_le_pow_right
      (show 2 * v + k ≤ 2 * s + 1 by omega) (hres i)
  have hcriterion :=
    existsUnique_eval₂_eq_iff_mulVec_eq_zero_of_sub_mem_pow_two_mul_add
      φ P a t v k hk hd hres'
  rw [← hvk]
  apply hcriterion.mpr
  intro z _ hz
  exact Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero
    hreg.mem_nonZeroDivisors hz

/-- Intersecting an adjugate neighborhood with the Jacobian preimage of a finer
ideal gives exactly that precision in the polynomial image. This follows from
`image_eval₂_adjugate_neighborhood` at the inverse-image subideal under
multiplication by the square of the Jacobian determinant. -/
theorem image_eval₂_adjugate_neighborhood_inter_jacobian_preimage
    {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a : ι → R)
    (J : Ideal R) :
    let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := A.det
    J ≤ Ideal.span ({d ^ 2} : Set R) * I →
      (fun b : ι → R => fun i => eval₂ φ b (P i)) ''
        {b : ι → R |
          (∃ z : ι → R, (∀ i, z i ∈ I) ∧
            b = a + d • A.adjugate.mulVec z) ∧
          (∀ i, A.mulVec (b - a) i ∈ J)} =
        {t : ι → R | ∀ i, t i - eval₂ φ a (P i) ∈ J} := by
  intro A d hJ
  let m : R →ₗ[R] R := LinearMap.mulLeft R (d ^ 2)
  let K : Ideal R := I ⊓ Submodule.comap m J
  have hmul (L : Ideal R) :
      Submodule.map m L = Ideal.span ({d ^ 2} : Set R) * L := by
    ext x
    change (∃ y, y ∈ L ∧ m y = x) ↔ _
    simp only [m, LinearMap.mulLeft_apply, Ideal.mem_span_singleton_mul]
  have hmK : Ideal.span ({d ^ 2} : Set R) * K = J := by
    calc
      Ideal.span ({d ^ 2} : Set R) * K = Submodule.map m K := (hmul K).symm
      _ = Submodule.map m I ⊓ J :=
        (Submodule.map_inf_eq_map_inf_comap (f := m) (p := I) (p' := J)).symm
      _ = J := inf_eq_right.mpr (by rw [hmul I]; exact hJ)
  have hAE (z : ι → R) :
      A.mulVec (d • A.adjugate.mulVec z) = d ^ 2 • z := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    change d • (d • z) = d ^ 2 • z
    rw [smul_smul, pow_two]
  have hsource :
      {b : ι → R |
        (∃ z : ι → R, (∀ i, z i ∈ I) ∧
          b = a + d • A.adjugate.mulVec z) ∧
        (∀ i, A.mulVec (b - a) i ∈ J)} =
      {b : ι → R | ∃ z : ι → R, (∀ i, z i ∈ K) ∧
        b = a + d • A.adjugate.mulVec z} := by
    ext b
    constructor
    · rintro ⟨⟨z, hz, hb⟩, h⟩
      refine ⟨z, ?_, hb⟩
      intro i
      change z i ∈ I ∧ m (z i) ∈ J
      refine ⟨hz i, ?_⟩
      have hi := h i
      rw [hb, add_sub_cancel_left, hAE] at hi
      exact hi
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, fun i => (hz i).1, rfl⟩, ?_⟩
      intro i
      rw [add_sub_cancel_left, hAE]
      exact (hz i).2
  let : HenselianRing R K := HenselianRing.of_le (show K ≤ I from inf_le_left)
  rw [hsource, ← hmK]
  exact image_eval₂_adjugate_neighborhood (I := K) φ P a

/-- Polynomial evaluation is a bijection from the adjugate-scaled neighborhood of `a`
onto the coordinatewise translated `(det A)² I` neighborhood when the evaluated
Jacobian determinant is a non-zero-divisor in the target ring.

Surjectivity holds without the regularity assumption; regularity gives injectivity
on the larger coordinatewise `(det A)I` neighborhood. -/
theorem bijOn_eval₂_adjugate_neighborhood
    {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a : ι → R) :
    let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := A.det
    d ∈ nonZeroDivisors R →
      Set.BijOn (fun b : ι → R => fun i => eval₂ φ b (P i))
        {b : ι → R | ∃ z : ι → R, (∀ i, z i ∈ I) ∧
          b = a + d • A.adjugate.mulVec z}
        {t : ι → R | ∀ i,
          t i - eval₂ φ a (P i) ∈ Ideal.span ({d ^ 2} : Set R) * I} := by
  intro A d hd
  have hinj :
      Set.InjOn (fun b : ι → R => fun i => eval₂ φ b (P i))
        {b : ι → R | ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I} :=
    (MvPolynomial.injOn_eval₂_iff_mulVec_eq_zero φ P a I
      (HenselianRing.jac (R := R) (I := I))).2
      (fun z _ hz =>
        Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hd hz)
  have himage := image_eval₂_adjugate_neighborhood (I := I) φ P a
  refine ⟨?_, hinj.mono ?_, ?_⟩
  · intro b hb
    rw [← himage]
    exact ⟨b, hb, rfl⟩
  · rintro b ⟨z, hz, rfl⟩ i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
    apply Ideal.mul_mem_mul (Ideal.subset_span (by simp))
    change (∑ j, A.adjugate i j * z j) ∈ I
    exact I.sum_mem fun j _ => I.mul_mem_left _ (hz j)
  · intro t ht
    rw [← himage] at ht
    exact ht

universe uC uR uσ

section CoordinatePerturbation

variable {σ : Type uσ} {R : Type uR} [CommSemiring R] [Fintype σ]

-- H = X + (B.map C).mulVec (E.mulVec X), written as finite sums.
-- Every correction term has an explicit coordinate variable as a factor.
private noncomputable def coordinatePerturbation
    (B : Matrix σ σ R) (E : Matrix σ σ (MvPolynomial σ R))
    (i : σ) : MvPolynomial σ R :=
  X i + ∑ k, ∑ l, C (B i k) * E k l * X l

-- The X_l factor suffices: this does not need E(0) = 0.
private theorem coordinatePerturbation_eval_zero
    (B : Matrix σ σ R) (E : Matrix σ σ (MvPolynomial σ R)) (i : σ) :
    (coordinatePerturbation B E i).eval₂ (RingHom.id R) (fun _ => 0) = 0 := by
  simp only [coordinatePerturbation, eval₂_add, eval₂_sum, eval₂_mul,
    eval₂_X, mul_zero, Finset.sum_const_zero, add_zero]

private theorem coordinatePerturbation_pderiv_eval_zero [DecidableEq σ]
    (B : Matrix σ σ R) (E : Matrix σ σ (MvPolynomial σ R))
    (hE : ∀ k l, (E k l).eval₂ (RingHom.id R) (fun _ => 0) = 0)
    (i j : σ) :
    (pderiv j (coordinatePerturbation B E i)).eval₂
        (RingHom.id R) (fun _ => 0) = if i = j then 1 else 0 := by
  have hterm (k l : σ) :
      (pderiv j (C (B i k) * E k l * X l)).eval₂
        (RingHom.id R) (fun _ => 0) = 0 := by
    -- Differentiate only the outer product. The first summand has X_l(0),
    -- and the second has E_kl(0). No value of a derivative of E is assumed.
    rw [pderiv_mul]
    simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, hE,
      mul_zero, zero_mul, add_zero]
  have hcorrection :
      (pderiv j (∑ k, ∑ l, C (B i k) * E k l * X l)).eval₂
        (RingHom.id R) (fun _ => 0) = 0 := by
    simp only [map_sum, eval₂_sum, hterm, Finset.sum_const_zero]
  simp only [coordinatePerturbation, map_add, eval₂_add]
  rw [hcorrection, add_zero]
  by_cases hij : i = j
  · subst j
    rw [pderiv_X_self, eval₂_one]
    simp
  · rw [pderiv_X_of_ne hij, eval₂_zero]
    simp only [hij, ite_false]

-- Ideal preservation does not require vanishing at zero or Henselianity.
private theorem coordinatePerturbation_eval_mem
    (B : Matrix σ σ R) (E : Matrix σ σ (MvPolynomial σ R))
    (K : Ideal R) (z : σ → R) (hz : ∀ l, z l ∈ K) (i : σ) :
    (coordinatePerturbation B E i).eval₂ (RingHom.id R) z ∈ K := by
  rw [coordinatePerturbation, eval₂_add, eval₂_X]
  apply K.add_mem (hz i)
  rw [eval₂_sum]
  apply K.sum_mem
  intro k hk
  rw [eval₂_sum]
  apply K.sum_mem
  intro l hl
  rw [eval₂_mul, eval₂_mul, eval₂_C, eval₂_X]
  -- Ideals are closed under multiplication by arbitrary coefficients.
  simpa only [RingHom.id_apply, smul_eq_mul] using
    (K.smul_mem (B i k * (E k l).eval₂ (RingHom.id R) z) (hz l))

end CoordinatePerturbation

private theorem det_mulVec_normalization
    {R : Type uR} [CommRing R] {σ : Type uσ} [Fintype σ] [DecidableEq σ]
    (A E : Matrix σ σ R) (x : σ → R) :
    (A + A.det • E).mulVec (A.det • x) =
      (A.det • A).mulVec (x + A.adjugate.mulVec (E.mulVec x)) := by
  symm
  calc
    (A.det • A).mulVec (x + A.adjugate.mulVec (E.mulVec x)) =
        A.det • (A.mulVec x + A.mulVec (A.adjugate.mulVec (E.mulVec x))) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_add]
    _ = A.det • (A.mulVec x + A.det • E.mulVec x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    _ = (A + A.det • E).mulVec (A.det • x) := by
      rw [Matrix.add_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.smul_mulVec, smul_add]

-- The polynomial secant matrix, and hence this system, is chosen before the point x.
private theorem exists_det_normalization
    {C : Type uC} [CommSemiring C] {R : Type uR} [CommRing R]
    {σ : Type uσ} [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) :
    let A : Matrix σ σ R := Matrix.of fun i j => (pderiv j (F i)).eval₂ φ a
    let d : R := A.det
    ∃ H : σ → MvPolynomial σ R,
      (∀ i, eval₂ (RingHom.id R) (0 : σ → R) (H i) = 0) ∧
      (Matrix.of fun i j => eval₂ (RingHom.id R) (0 : σ → R)
        (pderiv j (H i))) = (1 : Matrix σ σ R) ∧
      (∀ (K : Ideal R) (x : σ → R), (∀ i, x i ∈ K) →
        ∀ i, eval₂ (RingHom.id R) x (H i) ∈ K) ∧
      ∀ x : σ → R,
        (fun i => eval₂ φ (a + d • x) (F i) - eval₂ φ a (F i)) =
          (d • A).mulVec (fun i => eval₂ (RingHom.id R) x (H i)) := by
  classical
  dsimp only
  let A : Matrix σ σ R := Matrix.of fun i j => (pderiv j (F i)).eval₂ φ a
  let d : R := A.det
  let S := MvPolynomial σ R
  let κ : R →+* S := MvPolynomial.C
  let ε : S →+* R := eval₂Hom (RingHom.id R) (0 : σ → R)
  let J : Ideal S := RingHom.ker ε
  let aS : σ → S := fun i => κ (a i)
  let bS : σ → S := fun i => aS i + κ d * X i
  have hb (i : σ) : bS i - aS i ∈ Ideal.span {κ d} * J := by
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨X i, ?_, ?_⟩
    · change ε (X i) = 0
      change eval₂ (RingHom.id R) (0 : σ → R) (X i) = 0
      exact eval₂_X _ _ i
    · simp [bS]
  have hc (i : σ) : aS i - aS i ∈ Ideal.span {κ d} * J := by simp
  obtain ⟨E, hE, hsec⟩ :=
    exists_eval₂_sub_eq_mulVec_of_sub_mem_span_mul (κ.comp φ) F aS bS aS (κ d) J hb hc
  have hEzero (i j : σ) : eval₂ (RingHom.id R) (0 : σ → R) (E i j) = 0 := by
    exact hE i j
  let H : σ → S := coordinatePerturbation A.adjugate E
  have hzero (i : σ) : eval₂ (RingHom.id R) (0 : σ → R) (H i) = 0 :=
    coordinatePerturbation_eval_zero A.adjugate E i
  have hjac : (Matrix.of fun i j => eval₂ (RingHom.id R) (0 : σ → R)
      (pderiv j (H i))) = (1 : Matrix σ σ R) := by
    ext i j
    exact coordinatePerturbation_pderiv_eval_zero A.adjugate E hEzero i j
  have hpreserve (K : Ideal R) (x : σ → R) (hx : ∀ i, x i ∈ K) (i : σ) :
      eval₂ (RingHom.id R) x (H i) ∈ K :=
    coordinatePerturbation_eval_mem A.adjugate E K x hx i
  refine ⟨H, hzero, hjac, hpreserve, ?_⟩
  intro x
  let t : S →+* R := eval₂Hom (RingHom.id R) x
  have htC (r : R) : t (MvPolynomial.C r) = r := by
    change eval₂ (RingHom.id R) x (MvPolynomial.C r) = r
    exact eval₂_C _ _ r
  have htκ (r : R) : t (κ r) = r := htC r
  have htX (i : σ) : t (X i) = x i := by
    change eval₂ (RingHom.id R) x (X i) = x i
    exact eval₂_X _ _ i
  have hcoeff : t.comp (κ.comp φ) = φ := by
    ext r
    exact htκ (φ r)
  have heval (g : MvPolynomial σ C) (b : σ → S) :
      t (eval₂ (κ.comp φ) b g) = eval₂ φ (fun i => t (b i)) g := by
    rw [eval₂_comp_left, hcoeff]
    simp only [Function.comp_def]
  have hta : (fun i => t (aS i)) = a := by
    ext i
    exact htκ (a i)
  have htb : (fun i => t (bS i)) = a + d • x := by
    ext i
    simp only [bS, aS, map_add, map_mul, htκ, htX, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
  have hmatrix :
      ((Matrix.of fun i j => eval₂ (κ.comp φ) aS (pderiv j (F i))) +
          κ d • E).map t = A + d • E.map t := by
    ext i j
    change t (eval₂ (κ.comp φ) aS (pderiv j (F i)) + κ d * E i j) =
      eval₂ φ a (pderiv j (F i)) + d * t (E i j)
    rw [map_add, map_mul, heval, hta, htκ]
  have hvect : t ∘ (fun i => bS i - aS i) = d • x := by
    ext i
    change t (bS i - aS i) = d * x i
    simp only [bS, map_mul, htκ, htX, add_sub_cancel_left]
  have hspec :
      (fun i => eval₂ φ (a + d • x) (F i) - eval₂ φ a (F i)) =
        (A + d • E.map t).mulVec (d • x) := by
    ext i
    have hi := congrArg (fun v : σ → S => t (v i)) hsec
    change t (eval₂ (κ.comp φ) bS (F i) - eval₂ (κ.comp φ) aS (F i)) =
      t ((((Matrix.of fun j k => eval₂ (κ.comp φ) aS (pderiv k (F j))) +
        κ d • E).mulVec (fun j => bS j - aS j)) i) at hi
    rw [map_sub, heval, heval, htb, hta, RingHom.map_mulVec, hmatrix, hvect] at hi
    exact hi
  have hH : (fun i => eval₂ (RingHom.id R) x (H i)) =
      x + A.adjugate.mulVec ((E.map t).mulVec x) := by
    ext i
    change t (coordinatePerturbation A.adjugate E i) =
      (x + A.adjugate.mulVec ((E.map t).mulVec x)) i
    simp only [coordinatePerturbation, map_add, map_sum, map_mul, htC, htX,
      Pi.add_apply, Matrix.mulVec_apply_eq_sum, Finset.mul_sum, mul_assoc]
    rfl
  rw [hH]
  exact hspec.trans (det_mulVec_normalization A (E.map t) x)

private theorem exists_preimage_of_jacobian_eq_one
    {R : Type uR} [CommRing R] {σ : Type uσ} [Finite σ] [DecidableEq σ]
    {I : Ideal R} [HenselianRing R I]
    (H : σ → MvPolynomial σ R)
    (hzero : ∀ i, eval₂ (RingHom.id R) (0 : σ → R) (H i) = 0)
    (hjac : (Matrix.of fun i j => eval₂ (RingHom.id R) (0 : σ → R)
      (pderiv j (H i))) = (1 : Matrix σ σ R))
    (v : σ → R) (hv : ∀ i, v i ∈ I) :
    ∃ x : σ → R, (∀ i, x i ∈ I) ∧
      (fun i => eval₂ (RingHom.id R) x (H i)) = v := by
  let _ := Fintype.ofFinite σ
  let J : Matrix σ σ R := Matrix.of fun i j =>
    eval₂ (RingHom.id R) (0 : σ → R) (pderiv j (H i))
  have hJ : J = 1 := hjac
  have himage := image_eval₂_adjugate_neighborhood (I := I) (RingHom.id R) H
    (0 : σ → R)
  change (fun b : σ → R => fun i => eval₂ (RingHom.id R) b (H i)) ''
    {b : σ → R | ∃ z : σ → R, (∀ i, z i ∈ I) ∧
      b = (0 : σ → R) + J.det • J.adjugate.mulVec z} =
    {t : σ → R | ∀ i, t i - eval₂ (RingHom.id R) (0 : σ → R) (H i) ∈
      Ideal.span ({J.det ^ 2} : Set R) * I} at himage
  rw [hJ, Matrix.det_one] at himage
  have hmem : v ∈ {t : σ → R | ∀ i,
      t i - eval₂ (RingHom.id R) (0 : σ → R) (H i) ∈
        Ideal.span ({(1 : R) ^ 2} : Set R) * I} := by
    intro i
    simp only [hzero, sub_zero, one_pow]
    exact Ideal.mem_span_singleton_mul.mpr ⟨v i, hv i, one_mul _⟩
  rw [← himage] at hmem
  obtain ⟨x, ⟨z, hz, hx⟩, heval⟩ := hmem
  have hxz : x = z := by simpa using hx
  exact ⟨x, by simpa only [hxz] using hz, heval⟩

/-- Evaluation maps the coordinatewise `(d) I` neighborhood of a point exactly
onto the translate of the image of `I`-valued vectors under `d` times the
Jacobian. The target is a coupled linear image, not in general a product of
coordinate ideals. No regularity hypothesis on the determinant is required. -/
theorem image_eval₂_det_neighborhood
    {C : Type uC} [CommSemiring C] {R : Type uR} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {σ : Type uσ} [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) :
    let A : Matrix σ σ R := Matrix.of fun i j => (pderiv j (F i)).eval₂ φ a
    let d : R := A.det
    (fun b : σ → R => fun i => (F i).eval₂ φ b) ''
        {b : σ → R | ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I} =
      {y : σ → R | ∃ x : σ → R, (∀ i, x i ∈ I) ∧
        (fun i => y i - (F i).eval₂ φ a) = (d • A).mulVec x} := by
  classical
  dsimp only
  let A : Matrix σ σ R := Matrix.of fun i j => (pderiv j (F i)).eval₂ φ a
  let d : R := A.det
  obtain ⟨H, hzero, hjac, hpreserve, hidentity⟩ :=
    exists_det_normalization φ F a
  change (fun b : σ → R => fun i => (F i).eval₂ φ b) ''
    {b : σ → R | ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I} =
    {y : σ → R | ∃ x : σ → R, (∀ i, x i ∈ I) ∧
      (fun i => y i - (F i).eval₂ φ a) = (d • A).mulVec x}
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    choose x hx hdx using fun i => (Ideal.mem_span_singleton_mul).mp (hb i)
    have hbform : b = a + d • x := by
      ext i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
        (eq_add_of_sub_eq (hdx i).symm).trans (add_comm _ _)
    refine ⟨fun i => eval₂ (RingHom.id R) x (H i), hpreserve I x hx, ?_⟩
    simpa only [hbform] using hidentity x
  · rintro ⟨v, hv, hy⟩
    obtain ⟨x, hx, hHx⟩ := exists_preimage_of_jacobian_eq_one H hzero hjac v hv
    refine ⟨a + d • x, ?_, ?_⟩
    · intro i
      apply Ideal.mem_span_singleton_mul.mpr
      exact ⟨x i, hx i, by simp⟩
    · ext i
      have heq := congrFun (hidentity x) i
      rw [hHx] at heq
      have htarget := congrFun hy i
      exact sub_left_injective (heq.trans htarget.symm)

/-- A submodule containing the quadratic error restricts the image of the whole
coordinatewise `(d) I` neighborhood by the same linearized condition. The target
increments still form a coupled image under `d` times the Jacobian. -/
theorem image_eval₂_det_neighborhood_inf
    {C : Type uC} [CommSemiring C] {R : Type uR} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {σ : Type uσ} [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R)
    (N : Submodule R (σ → R)) :
    let A : Matrix σ σ R := Matrix.of fun i j => (pderiv j (F i)).eval₂ φ a
    let d : R := A.det
    Submodule.pi Set.univ
        (fun _ : σ => (Ideal.span ({d ^ 2} : Set R) * I ^ 2 : Submodule R R)) ≤ N →
      (fun b : σ → R => fun i => (F i).eval₂ φ b) ''
          {b : σ → R | (∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I) ∧
            A.mulVec (b - a) ∈ N} =
        {y : σ → R | (y - fun i => (F i).eval₂ φ a) ∈ N ∧
          ∃ x : σ → R, (∀ i, x i ∈ I) ∧
            (y - fun i => (F i).eval₂ φ a) = (d • A).mulVec x} := by
  classical
  intro A d hN
  have herror (b : σ → R)
      (hb : ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I) :
      ((fun i => (F i).eval₂ φ b) - (fun i => (F i).eval₂ φ a) -
        A.mulVec (b - a)) ∈ N := by
    apply hN
    apply Submodule.mem_pi.mpr
    intro i _
    exact MvPolynomial.eval₂_sub_sub_mulVec_mem_span_sq_mul φ F a b d I hb i
  have hwhole := image_eval₂_det_neighborhood (I := I) φ F a
  apply Set.ext
  intro y
  constructor
  · rintro ⟨b, ⟨hb, hAb⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa only [sub_add_cancel] using N.add_mem (herror b hb) hAb
    · have hmem : (fun i => (F i).eval₂ φ b) ∈
          (fun b : σ → R => fun i => (F i).eval₂ φ b) ''
            {b : σ → R | ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I} :=
        ⟨b, hb, rfl⟩
      rw [hwhole] at hmem
      exact hmem
  · rintro ⟨hyN, x, hx, hxy⟩
    have hmem : y ∈ {y : σ → R | ∃ x : σ → R, (∀ i, x i ∈ I) ∧
        (fun i => y i - (F i).eval₂ φ a) = (d • A).mulVec x} := ⟨x, hx, hxy⟩
    rw [← hwhole] at hmem
    obtain ⟨b, hb, hby⟩ := hmem
    refine ⟨b, ⟨hb, ?_⟩, hby⟩
    have hyN' : ((fun i => (F i).eval₂ φ b) - fun i => (F i).eval₂ φ a) ∈ N := by
      rw [← hby] at hyN
      exact hyN
    simpa only [sub_sub_cancel] using N.sub_mem hyN' (herror b hb)

end HenselianRing


namespace HenselianRing

universe uCoupledCoeff uCoupledTarget uCoupledIndex

open MvPolynomial


/-- The nonlinear error on an adjugate neighborhood lies in the coordinate submodule
for the square of the ideal, scaled by the square of the Jacobian determinant. -/
theorem eval₂_sub_sub_mulVec_mem_det_sq_mul
    {C : Type uCoupledCoeff} [CommSemiring C]
    {R : Type uCoupledTarget} [CommRing R]
    {I : Ideal R}
    {ι : Type uCoupledIndex} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a z : ι → R)
    (hz : ∀ i, z i ∈ I) :
    let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := A.det
    ((fun i => eval₂ φ (a + d • A.adjugate.mulVec z) (P i)) -
      (fun i => eval₂ φ a (P i)) - A.mulVec (d • A.adjugate.mulVec z)) ∈
      Submodule.pi Set.univ
        (fun _ : ι => (Ideal.span ({d ^ 2} : Set R) * (I * I) : Submodule R R)) := by
  classical
  let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
  let d : R := A.det
  have hb : ∀ i, (a + d • A.adjugate.mulVec z) i - a i ∈
      Ideal.span {d} * I := by
    intro i
    refine Ideal.mem_span_singleton_mul.mpr ⟨(A.adjugate.mulVec z) i, ?_, ?_⟩
    · change (∑ k, A.adjugate i k * z k) ∈ I
      exact I.sum_mem fun k _ => I.mul_mem_left _ (hz k)
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  have h := MvPolynomial.eval₂_sub_sub_mulVec_mem_span_sq_mul
    φ P a (a + d • A.adjugate.mulVec z) d I hb
  have hA : (Matrix.of fun j i => (pderiv i (P j)).eval₂ φ a) = A := by
    ext j i
    rfl
  rw [hA] at h
  apply Submodule.mem_pi.mpr
  intro i _
  change eval₂ φ (a + d • A.adjugate.mulVec z) (P i) - eval₂ φ a (P i) -
    A.mulVec (d • A.adjugate.mulVec z) i ∈ Ideal.span {d ^ 2} * (I * I)
  simpa only [Pi.add_apply, add_sub_cancel_left, pow_two] using h i


/-- Restricting an adjugate neighborhood by a linear submodule condition restricts its
polynomial image by the same condition, provided the submodule contains the quadratic error. -/
theorem image_eval₂_adjugate_neighborhood_inf
    {C : Type uCoupledCoeff} [CommSemiring C]
    {R : Type uCoupledTarget} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {ι : Type uCoupledIndex} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a : ι → R)
    (N : Submodule R (ι → R)) :
    let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := A.det
    Submodule.pi Set.univ
        (fun _ : ι => (Ideal.span ({d ^ 2} : Set R) * (I * I) : Submodule R R)) ≤ N →
      (fun b : ι → R => fun i => eval₂ φ b (P i)) ''
          {b : ι → R | (∃ z : ι → R, (∀ i, z i ∈ I) ∧
            b = a + d • A.adjugate.mulVec z) ∧ A.mulVec (b - a) ∈ N} =
        {t : ι → R | (t - fun i => eval₂ φ a (P i)) ∈
          N ⊓ Submodule.pi Set.univ
            (fun _ : ι => (Ideal.span ({d ^ 2} : Set R) * I : Submodule R R))} := by
  classical
  let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
  let d : R := A.det
  change Submodule.pi Set.univ
      (fun _ : ι => (Ideal.span ({d ^ 2} : Set R) * (I * I) : Submodule R R)) ≤ N →
    (fun b : ι → R => fun i => eval₂ φ b (P i)) ''
        {b : ι → R | (∃ z : ι → R, (∀ i, z i ∈ I) ∧
          b = a + d • A.adjugate.mulVec z) ∧ A.mulVec (b - a) ∈ N} =
      {t : ι → R | (t - fun i => eval₂ φ a (P i)) ∈
        N ⊓ Submodule.pi Set.univ
          (fun _ : ι => (Ideal.span ({d ^ 2} : Set R) * I : Submodule R R))}
  intro hN
  have error_mem (b : ι → R)
      (hb : ∃ z : ι → R, (∀ i, z i ∈ I) ∧ b = a + d • A.adjugate.mulVec z) :
      ((fun i => eval₂ φ b (P i)) - (fun i => eval₂ φ a (P i)) -
        A.mulVec (b - a)) ∈ N := by
    apply hN
    obtain ⟨z, hz, rfl⟩ := hb
    simpa only [add_sub_cancel_left] using
      eval₂_sub_sub_mulVec_mem_det_sq_mul φ P a z hz
  apply Set.Subset.antisymm
  · rintro t ⟨b, ⟨hb, hlinear⟩, rfl⟩
    have hupper : ∀ i,
        eval₂ φ b (P i) - eval₂ φ a (P i) ∈ Ideal.span ({d ^ 2} : Set R) * I := by
      have hmem : (fun i => eval₂ φ b (P i)) ∈
          (fun c : ι → R => fun i => eval₂ φ c (P i)) ''
            {c : ι → R | ∃ z : ι → R, (∀ i, z i ∈ I) ∧
              c = a + d • A.adjugate.mulVec z} := ⟨b, hb, rfl⟩
      rw [image_eval₂_adjugate_neighborhood φ P a] at hmem
      exact hmem
    refine ⟨?_, Submodule.mem_pi.mpr (fun i _ => hupper i)⟩
    change ((fun i => eval₂ φ b (P i)) - (fun i => eval₂ φ a (P i))) ∈ N
    simpa only [sub_add_cancel] using N.add_mem (error_mem b hb) hlinear
  · intro t ht
    have hupper : ∀ i,
        t i - eval₂ φ a (P i) ∈ Ideal.span ({d ^ 2} : Set R) * I :=
      fun i => (Submodule.mem_pi.mp ht.2) i (Set.mem_univ i)
    have hmem : t ∈ (fun b : ι → R => fun i => eval₂ φ b (P i)) ''
        {b : ι → R | ∃ z : ι → R, (∀ i, z i ∈ I) ∧
          b = a + d • A.adjugate.mulVec z} := by
      rw [image_eval₂_adjugate_neighborhood φ P a]
      exact hupper
    obtain ⟨b, hb, hbt⟩ := hmem
    refine ⟨b, ⟨hb, ?_⟩, hbt⟩
    have heval : ((fun i => eval₂ φ b (P i)) - (fun i => eval₂ φ a (P i))) ∈ N := by
      change (fun i => eval₂ φ b (P i)) = t at hbt
      rw [hbt]
      exact ht.1
    simpa using N.sub_mem heval (error_mem b hb)

/-- Evaluation is a bijection on the proper adjugate neighborhood with a linearized
submodule constraint, onto the corresponding translated target. The submodule contains
the coordinatewise quadratic error, and the evaluated determinant is regular. -/
theorem bijOn_eval₂_adjugate_neighborhood_inf
    {C : Type uCoupledCoeff} [CommSemiring C]
    {R : Type uCoupledTarget} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {ι : Type uCoupledIndex} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a : ι → R)
    (N : Submodule R (ι → R)) :
    let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := A.det
    d ∈ nonZeroDivisors R →
      Submodule.pi Set.univ
          (fun _ : ι => (Ideal.span ({d ^ 2} : Set R) * (I * I) : Submodule R R)) ≤ N →
        Set.BijOn (fun b : ι → R => fun i => eval₂ φ b (P i))
          {b : ι → R | (∃ z : ι → R, (∀ i, z i ∈ I) ∧
            b = a + d • A.adjugate.mulVec z) ∧ A.mulVec (b - a) ∈ N}
          {t : ι → R | (t - fun i => eval₂ φ a (P i)) ∈
            N ⊓ Submodule.pi Set.univ
              (fun _ : ι => (Ideal.span ({d ^ 2} : Set R) * I : Submodule R R))} := by
  dsimp only
  intro hd hN
  rw [← image_eval₂_adjugate_neighborhood_inf (I := I) φ P a N hN]
  exact ((bijOn_eval₂_adjugate_neighborhood (I := I) φ P a hd).injOn.mono
    fun _ hb => hb.1).bijOn_image

/-- Evaluation is bijective from the determinant box constrained by a submodule onto its
coupled image exactly when the evaluated Jacobian has no nonzero kernel vector in the full
determinant displacement box. The submodule need only contain the coordinatewise ideal
`(d²)I²`; no regularity assumption on the determinant is required. -/
public theorem bijOn_eval₂_det_neighborhood_inf_iff_mulVec_eq_zero
    {C : Type*} [CommSemiring C] {R : Type*} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R)
    (N : Submodule R (σ → R)) :
    let A : Matrix σ σ R := Matrix.of fun i j => (pderiv j (F i)).eval₂ φ a
    let d : R := A.det
    Submodule.pi Set.univ
        (fun _ : σ => (Ideal.span ({d ^ 2} : Set R) * I ^ 2 : Submodule R R)) ≤ N →
      (Set.BijOn (fun b : σ → R => fun i => (F i).eval₂ φ b)
          {b : σ → R | (∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I) ∧
            A.mulVec (b - a) ∈ N}
          {y : σ → R | (y - fun i => (F i).eval₂ φ a) ∈ N ∧
            ∃ x : σ → R, (∀ i, x i ∈ I) ∧
              (y - fun i => (F i).eval₂ φ a) = (d • A).mulVec x} ↔
        ∀ δ : σ → R, (∀ i, δ i ∈ Ideal.span ({d} : Set R) * I) →
          A.mulVec δ = 0 → δ = 0) := by
  classical
  dsimp only
  intro hN
  let A : Matrix σ σ R := Matrix.of fun i j => (pderiv j (F i)).eval₂ φ a
  let d : R := A.det
  let f : (σ → R) → (σ → R) := fun b i => (F i).eval₂ φ b
  let B : Set (σ → R) :=
    {b | (∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I) ∧
      A.mulVec (b - a) ∈ N}
  let T : Set (σ → R) :=
    {y | (y - f a) ∈ N ∧ ∃ x : σ → R, (∀ i, x i ∈ I) ∧
      y - f a = (d • A).mulVec x}
  change Set.BijOn f B T ↔
    ∀ δ : σ → R, (∀ i, δ i ∈ Ideal.span ({d} : Set R) * I) →
      A.mulVec δ = 0 → δ = 0
  have himage : f '' B = T := image_eval₂_det_neighborhood_inf φ F a N hN
  have hinj : Set.InjOn f B ↔
      ∀ δ : σ → R, (∀ i, δ i ∈ Ideal.span ({d} : Set R) * I) →
        A.mulVec δ = 0 → δ = 0 :=
    MvPolynomial.injOn_eval₂_det_neighborhood_inter_preimage_iff_of_zero_mem
      φ F a I (HenselianRing.jac (R := R) (I := I)) (N : Set (σ → R)) N.zero_mem
  constructor
  · intro hbij
    exact hinj.mp hbij.injOn
  · intro hker
    refine ⟨?_, hinj.mpr hker, ?_⟩
    · intro b hb
      rw [← himage]
      exact ⟨b, hb, rfl⟩
    · intro y hy
      have hyimage : y ∈ f '' B := by
        rw [himage]
        exact hy
      exact hyimage

end HenselianRing


namespace MvPolynomial

universe uPreimageCoeff uPreimageTarget uPreimageIndex

open scoped BigOperators Pointwise

/-- The sum of a constrained proper adjugate neighborhood and the Jacobian kernel
inside its scalar box is the intersection of that box with a polynomial preimage.
The translated target imposes both an additive subgroup constraint and determinant-square
precision. Only containment of the quadratic remainder in the subgroup is required;
the determinant need not be regular, and no Henselian hypothesis is needed. -/
theorem adjugate_neighborhood_add_ker_eq_inter_preimage
    {C : Type uPreimageCoeff} {R : Type uPreimageTarget} {ι : Type uPreimageIndex}
    [CommSemiring C] [CommRing R] [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (φ : C →+* R)
    (P : ι → MvPolynomial ι C) (a : ι → R)
    (N : AddSubgroup (ι → R)) :
    let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := A.det
    (Submodule.pi Set.univ
      (fun _ : ι => Ideal.span ({d ^ 2} : Set R) * (I * I))).toAddSubgroup ≤ N →
      {b : ι → R |
        (∃ z : ι → R, (∀ i, z i ∈ I) ∧
          b = a + d • A.adjugate.mulVec z) ∧
        A.mulVec (b - a) ∈ N} +
      {κ : ι → R |
        (∀ i, κ i ∈ Ideal.span ({d} : Set R) * I) ∧ A.mulVec κ = 0} =
      {b : ι → R |
        ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I} ∩
      (fun b : ι → R => fun i : ι => eval₂ φ b (P i)) ⁻¹'
      {t : ι → R |
        t - (fun i : ι => eval₂ φ a (P i)) ∈
          N ⊓ (Submodule.pi Set.univ
            (fun _ : ι => Ideal.span ({d ^ 2} : Set R) * I)).toAddSubgroup} := by
  classical
  intro A d hN
  let F : (ι → R) → (ι → R) := fun b i => eval₂ φ b (P i)
  let V : Ideal R → Submodule R (ι → R) := fun J =>
    Submodule.pi Set.univ (fun _ : ι => (J : Submodule R R))
  let H : Ideal R := Ideal.span ({d} : Set R) * I
  let L : Ideal R := Ideal.span ({d ^ 2} : Set R) * I
  let Q : Ideal R := Ideal.span ({d ^ 2} : Set R) * (I * I)
  have hQL : Q ≤ L := Ideal.mul_mono le_rfl Ideal.mul_le_left
  have hVL : V Q ≤ V L := Submodule.pi_mono (fun _ _ => hQL)
  have herror (b : ι → R) (hb : ∀ i, b i - a i ∈ H) :
      F b - F a - A.mulVec (b - a) ∈ N ⊓ (V L).toAddSubgroup := by
    have hmat : Matrix.of (fun i j => eval₂ φ a (pderiv j (P i))) = A := by
      funext i j
      rfl
    have hsub : (fun i => b i - a i) = b - a := by
      funext i
      rfl
    have he : F b - F a - A.mulVec (b - a) ∈ V Q := by
      apply Submodule.mem_pi.mpr
      intro j _
      change (F b - F a - A.mulVec (b - a)) j ∈ (Q : Ideal R)
      have hr := MvPolynomial.eval₂_sub_sub_mulVec_mem_span_sq_mul φ P a b d I hb j
      rw [hmat, hsub] at hr
      simpa only [F, Q, pow_two, Pi.sub_apply] using hr
    exact ⟨hN he, hVL he⟩
  have hshift (b : ι → R) (hb : ∀ i, b i - a i ∈ H) :
      F b - F a ∈ N ⊓ (V L).toAddSubgroup ↔
        A.mulVec (b - a) ∈ N ⊓ (V L).toAddSubgroup := by
    constructor
    · intro h
      have hm := (N ⊓ (V L).toAddSubgroup).sub_mem h (herror b hb)
      have heq : (F b - F a) - (F b - F a - A.mulVec (b - a)) =
          A.mulVec (b - a) := by abel
      rwa [heq] at hm
    · intro h
      simpa only [sub_add_cancel] using
        (N ⊓ (V L).toAddSubgroup).add_mem (herror b hb) h
  have hscaled (x : ι → R) :
      x ∈ V L ↔
        x ∈ (fun z : ι → R => (A.det * d) • z) '' {z | ∀ i, z i ∈ I} := by
    constructor
    · intro hx
      have hx' : ∀ i, ∃ r ∈ I, d ^ 2 * r = x i := fun i =>
        Ideal.mem_span_singleton_mul.mp ((Submodule.mem_pi.mp hx) i (Set.mem_univ i))
      choose z hz hzx using hx'
      refine ⟨z, hz, ?_⟩
      funext i
      simpa only [Pi.smul_apply, smul_eq_mul, pow_two] using hzx i
    · rintro ⟨z, hz, rfl⟩
      apply Submodule.mem_pi.mpr
      intro i _
      apply Ideal.mem_span_singleton_mul.mpr
      refine ⟨z i, hz i, ?_⟩
      change d ^ 2 * z i = (d * d) * z i
      rw [pow_two]
  have hlinear (x : ι → R) :
      A.mulVec x ∈ V L ↔
        x ∈ (fun z : ι → R => d • A.adjugate.mulVec z) '' {z | ∀ i, z i ∈ I} +
          {κ : ι → R | A.mulVec κ = 0} := by
    rw [hscaled]
    change x ∈ A.mulVec ⁻¹'
      ((fun z : ι → R => (A.det * d) • z) '' {z | ∀ i, z i ∈ I}) ↔ _
    rw [Matrix.mulVec_preimage_smul_image_add_ker A d _]
  have hbox (z : ι → R) (hz : ∀ i, z i ∈ I) :
      ∀ i, (d • A.adjugate.mulVec z) i ∈ H := by
    intro i
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨(A.adjugate.mulVec z) i, ?_, rfl⟩
    change ∑ j, A.adjugate i j * z j ∈ I
    apply I.sum_mem
    intro j _
    exact I.mul_mem_left _ (hz j)
  ext b
  constructor
  · rintro ⟨p, ⟨⟨z, hz, hpz⟩, hpn⟩, κ, ⟨hκbox, hκker⟩, rfl⟩
    have hp : p - a = d • A.adjugate.mulVec z := by rw [hpz]; abel
    have hdelta : p + κ - a = (p - a) + κ := by abel
    have hpbox : p - a ∈ V H := by
      apply Submodule.mem_pi.mpr
      intro i _
      rw [hp]
      exact hbox z hz i
    have hκbox' : κ ∈ V H := Submodule.mem_pi.mpr (fun i _ => hκbox i)
    have hb : ∀ i, (p + κ) i - a i ∈ H := by
      have hm : p + κ - a ∈ V H := by
        rw [hdelta]
        exact (V H).add_mem hpbox hκbox'
      exact fun i => (Submodule.mem_pi.mp hm) i (Set.mem_univ i)
    have hlin : A.mulVec (p + κ - a) = A.mulVec (p - a) := by
      rw [hdelta, Matrix.mulVec_add, hκker, add_zero]
    refine ⟨hb, (hshift (p + κ) hb).mpr ⟨?_, ?_⟩⟩
    · rwa [hlin]
    · apply (hlinear (p + κ - a)).mpr
      refine ⟨d • A.adjugate.mulVec z, ⟨z, hz, rfl⟩, κ, hκker, ?_⟩
      rw [hdelta, hp]
  · rintro ⟨hb, ht⟩
    have hl := (hshift b hb).mp ht
    obtain ⟨v, ⟨z, hz, rfl⟩, κ, hκker, hdelta⟩ := (hlinear (b - a)).mp hl.2
    change d • A.adjugate.mulVec z + κ = b - a at hdelta
    have hκeq : κ = (b - a) - d • A.adjugate.mulVec z := by
      apply (eq_sub_iff_add_eq).mpr
      exact (add_comm κ (d • A.adjugate.mulVec z)).trans hdelta
    have hκbox : ∀ i, κ i ∈ H := by
      intro i
      rw [hκeq]
      exact H.sub_mem (hb i) (hbox z hz i)
    have hlin : A.mulVec (a + d • A.adjugate.mulVec z - a) =
        A.mulVec (b - a) := by
      calc
        A.mulVec (a + d • A.adjugate.mulVec z - a) =
            A.mulVec (d • A.adjugate.mulVec z) := by congr 1; abel
        _ = A.mulVec (d • A.adjugate.mulVec z + κ) := by
          rw [Matrix.mulVec_add, hκker, add_zero]
        _ = A.mulVec (b - a) := congrArg A.mulVec hdelta
    refine ⟨a + d • A.adjugate.mulVec z, ⟨⟨z, hz, rfl⟩, ?_⟩,
      κ, ⟨hκbox, hκker⟩, ?_⟩
    · rw [hlin]
      exact hl.1
    · change (a + d • A.adjugate.mulVec z) + κ = b
      rw [add_assoc, hdelta]
      abel

/-- A proper adjugate neighborhood, cut out by a submodule condition on the linear
increment, is the intersection of its scalar box with the polynomial preimage of the
corresponding translated target. The target also imposes determinant-square precision.

Only regularity of the evaluated Jacobian determinant and containment of the quadratic
remainder in the submodule are required; no Henselian hypothesis is needed. -/
theorem adjugate_neighborhood_eq_inter_preimage
    {C : Type uPreimageCoeff} {R : Type uPreimageTarget} {ι : Type uPreimageIndex}
    [CommSemiring C] [CommRing R] [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (φ : C →+* R)
    (P : ι → MvPolynomial ι C) (a : ι → R)
    (N : Submodule R (ι → R)) :
    let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := A.det
    d ∈ nonZeroDivisors R →
      Submodule.pi Set.univ
        (fun _ : ι => Ideal.span ({d ^ 2} : Set R) * (I * I)) ≤ N →
      {b : ι → R |
        (∃ z : ι → R, (∀ i, z i ∈ I) ∧
          b = a + d • A.adjugate.mulVec z) ∧
        A.mulVec (b - a) ∈ N} =
      {b : ι → R |
        ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I} ∩
      (fun b : ι → R => fun i : ι => eval₂ φ b (P i)) ⁻¹'
      {t : ι → R |
        t - (fun i : ι => eval₂ φ a (P i)) ∈
          N ⊓ Submodule.pi Set.univ
            (fun _ : ι => Ideal.span ({d ^ 2} : Set R) * I)} := by
  classical
  intro A d hd hN
  have hker (κ : ι → R) (hκ : A.mulVec κ = 0) : κ = 0 := by
    have hm : κ ∈ A.mulVec ⁻¹'
        ((fun z : ι → R => (A.det * (0 : R)) • z) '' {0}) := by
      refine ⟨0, by simp, ?_⟩
      simpa only [mul_zero, zero_smul] using hκ.symm
    rw [Matrix.mulVec_preimage_smul_image A 0 {0} hd] at hm
    obtain ⟨z, _, hzκ⟩ := hm
    simpa only [zero_smul] using hzκ.symm
  have hN' : (Submodule.pi Set.univ
      (fun _ : ι => Ideal.span ({d ^ 2} : Set R) * (I * I))).toAddSubgroup ≤
        N.toAddSubgroup := fun _ hx => hN hx
  have hsum :
      {b : ι → R |
        (∃ z : ι → R, (∀ i, z i ∈ I) ∧
          b = a + d • A.adjugate.mulVec z) ∧
        A.mulVec (b - a) ∈ N} +
      {κ : ι → R |
        (∀ i, κ i ∈ Ideal.span ({d} : Set R) * I) ∧ A.mulVec κ = 0} =
      {b : ι → R |
        (∃ z : ι → R, (∀ i, z i ∈ I) ∧
          b = a + d • A.adjugate.mulVec z) ∧
        A.mulVec (b - a) ∈ N} := by
    ext b
    constructor
    · rintro ⟨p, hp, κ, hκ, hpb⟩
      have hp' : p = b := by simpa only [hker κ hκ.2, add_zero] using hpb
      exact hp' ▸ hp
    · intro hb
      exact ⟨b, hb, 0, ⟨fun _ => Ideal.zero_mem _, by simp⟩, add_zero b⟩
  calc
    _ = _ := hsum.symm
    _ = _ := adjugate_neighborhood_add_ker_eq_inter_preimage I φ P a N.toAddSubgroup hN'

end MvPolynomial
