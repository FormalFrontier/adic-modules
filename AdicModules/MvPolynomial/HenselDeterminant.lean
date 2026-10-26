/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.MvPolynomial.Hensel
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
with prescribed target values when its errors lie in `(d²) I`, where `d` is the
evaluated Jacobian determinant. The correction lies in `(d) I`. No regularity
assumption on `d` is needed, and the target values need not come from the source
semiring. If the evaluated determinant is regular, this root is unique in the
same correction box, by injectivity of the original evaluation map on that box.

For a Henselian ideal `M`, if `(d) = M ^ v` with `v ≤ s`, errors in
`M ^ (2 * s + 1)` give a root in the `M ^ (s + 1)` correction box. This root is
unique in the same box when `d` is regular.

The proof applies the first-order Taylor remainder theorem to the adjugate
substitution in a polynomial ring over `R`. Extracting witnesses from principal
ideal products gives a normalized system with value in `I` and identity Jacobian
at zero. The existing unit-Jacobian Hensel theorem supplies its root; forward
evaluation recovers a root of the original system. Neither `d` nor `d²` is
cancelled.

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
    ∃ b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
      ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I := by
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
  refine ⟨b, ?_, ?_⟩
  · intro i
    have h := congrArg (eval z) (hP i)
    simp only [map_sub, eval_eval₂, hcoeff, hsubst, eval_C, map_mul] at h
    change eval₂ φ b (P i) - t i = d ^ 2 * eval z (F i) at h
    rw [hz.1 i, mul_zero] at h
    exact sub_eq_zero.mp h
  · intro i
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨(M.mulVec z) i, ?_, ?_⟩
    · rw [Matrix.mulVec_apply_eq_sum]
      exact Submodule.sum_mem _ fun j _ => I.mul_mem_left (M i j) (hzI j)
    · simp only [b, add_sub_cancel_left]

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
  classical
  let J : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
  change (∀ i, eval₂ φ a (P i) - t i ∈ Ideal.span ({J.det ^ 2} : Set R) * I) →
    ∃ b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
      ∀ i, b i - a i ∈ Ideal.span ({J.det} : Set R) * I
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
  obtain ⟨b, hb⟩ := exists_eval₂_eq_of_sub_mem_det_sq_mul φ P a t ha
  refine ⟨b, hb, ?_⟩
  intro c hc
  have hI : I ≤ Ideal.jacobson (⊥ : Ideal R) := HenselianRing.jac
  apply MvPolynomial.injOn_eval₂_of_mem_nonZeroDivisors_det_jacobian
    φ I hI P a hd.mem_nonZeroDivisors hc.2 hb.2
  funext i
  exact (hc.1 i).trans (hb.1 i).symm

universe uCoeff uTarget uIndex

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
  let e : ℕ := s + 1 - v
  have he : e ≠ 0 := by
    dsimp only [e]
    omega
  let : HenselianRing R (M ^ e) :=
    HenselianRing.of_le (I := M ^ e) (J := M)
      (Ideal.pow_le_self (I := M) (n := e) he)
  have hve : v + e = s + 1 := by
    dsimp only [e]
    omega
  have hbox : Ideal.span ({d} : Set R) * M ^ e = M ^ (s + 1) := by
    rw [hspan, ← pow_add M v e, hve]
  have herr : Ideal.span ({d ^ 2} : Set R) * M ^ e = M ^ (s + v + 1) := by
    calc
      Ideal.span ({d ^ 2} : Set R) * M ^ e =
          Ideal.span ({d} : Set R) * (Ideal.span ({d} : Set R) * M ^ e) := by
        rw [← Ideal.span_singleton_pow d 2, pow_two, Ideal.mul_assoc]
      _ = M ^ v * M ^ (s + 1) := by rw [hbox, hspan]
      _ = M ^ (v + (s + 1)) := (pow_add M v (s + 1)).symm
      _ = M ^ (s + v + 1) := by congr 1; omega
  have ha' : ∀ i, eval₂ φ a (P i) - t i ∈
      Ideal.span ({d ^ 2} : Set R) * M ^ e := by
    intro i
    rw [herr]
    exact Ideal.pow_le_pow_right (I := M)
      (m := s + v + 1) (n := 2 * s + 1) (by omega) (ha i)
  have hroot : ∃ b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
      ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * M ^ e :=
    HenselianRing.exists_eval₂_eq_of_sub_mem_det_sq_mul (I := M ^ e) φ P a t ha'
  simpa only [hbox] using hroot

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
  intro J d hv hspan hd ha
  let e : ℕ := s + 1 - v
  have he : e ≠ 0 := by
    dsimp only [e]
    omega
  let : HenselianRing R (M ^ e) :=
    HenselianRing.of_le (I := M ^ e) (J := M)
      (Ideal.pow_le_self (I := M) (n := e) he)
  have hve : v + e = s + 1 := by
    dsimp only [e]
    omega
  have hbox : Ideal.span ({d} : Set R) * M ^ e = M ^ (s + 1) := by
    rw [hspan, ← pow_add M v e, hve]
  have herr : Ideal.span ({d ^ 2} : Set R) * M ^ e = M ^ (s + v + 1) := by
    calc
      Ideal.span ({d ^ 2} : Set R) * M ^ e =
          Ideal.span ({d} : Set R) * (Ideal.span ({d} : Set R) * M ^ e) := by
        rw [← Ideal.span_singleton_pow d 2, pow_two, Ideal.mul_assoc]
      _ = M ^ v * M ^ (s + 1) := by rw [hbox, hspan]
      _ = M ^ (v + (s + 1)) := (pow_add M v (s + 1)).symm
      _ = M ^ (s + v + 1) := by congr 1; omega
  have ha' : ∀ i, eval₂ φ a (P i) - t i ∈
      Ideal.span ({d ^ 2} : Set R) * M ^ e := by
    intro i
    rw [herr]
    exact Ideal.pow_le_pow_right (I := M)
      (m := s + v + 1) (n := 2 * s + 1) (by omega) (ha i)
  have hroot : ∃! b : ι → R, (∀ i, eval₂ φ b (P i) = t i) ∧
      ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * M ^ e :=
    HenselianRing.existsUnique_eval₂_eq_of_sub_mem_det_sq_mul
      (I := M ^ e) φ P a t hd ha'
  simpa only [hbox] using hroot

end HenselianRing
