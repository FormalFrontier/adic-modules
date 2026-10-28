/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.MvPolynomial.HenselDeterminant
import AdicModules.MvPolynomial.JacobianPerturbation
import Mathlib.Tactic

/-!
# A sufficient image criterion for Henselian polynomial systems

A target difference in the Jacobian image of the determinant box admits a root
in that box. The proof uses
`MvPolynomial.exists_eval₂_sub_eq_mulVec_of_sub_mem_span_mul` to change the
approximate point, `Matrix.associated_det_of_sub_mem_span_mul` to preserve the
determinant ideal, and `HenselianRing.exists_eval₂_eq_of_sub_mem_det_sq_mul` to
obtain the root over the original Henselian ideal.
-/

open scoped BigOperators

@[expose] public section
namespace HenselianRing
universe u v w
open Classical in
/-- A target in the Jacobian image of the determinant box has a root in that box.

The Henselian hypothesis is imposed on the original ideal, and no regularity
assumption on the Jacobian determinant is needed. -/
theorem exists_eval₂_eq_of_sub_eq_mulVec
    {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    {σ : Type w} [Fintype σ] {I : Ideal R} [HenselianRing R I]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a t : σ → R) :
    let A : Matrix σ σ R := fun i j =>
      MvPolynomial.eval₂ φ a (MvPolynomial.pderiv j (F i))
    let J : Ideal R := Ideal.span ({A.det} : Set R) * I
    (∃ η : σ → R, (∀ i, η i ∈ J) ∧
      (fun i => t i - MvPolynomial.eval₂ φ a (F i)) = A.mulVec η) →
      ∃ b : σ → R, (∀ i, MvPolynomial.eval₂ φ b (F i) = t i) ∧
        ∀ i, b i - a i ∈ J := by
  classical
  dsimp only
  let A : Matrix σ σ R := fun i j =>
    MvPolynomial.eval₂ φ a (MvPolynomial.pderiv j (F i))
  let d : R := A.det
  let J : Ideal R := Ideal.span ({d} : Set R) * I
  rintro ⟨η, hη, ht⟩
  change ∀ i, η i ∈ J at hη
  change (fun i => t i - MvPolynomial.eval₂ φ a (F i)) = A.mulVec η at ht
  let c : σ → R := fun i => a i + η i
  have hca : (fun i => c i - a i) = η := by
    funext i
    dsimp [c]
    ring
  have hc : ∀ i, c i - a i ∈ J := by
    intro i
    rw [congrFun hca i]
    exact hη i
  have ha : ∀ i, a i - a i ∈ J := by
    intro i
    simp
  have hmulVec : ∀ {τ : Type w} (M : Matrix τ σ R) i, M.mulVec η i ∈ J := by
    intro τ M i
    change ∑ j, M i j * η j ∈ J
    exact J.sum_mem fun j _ => J.mul_mem_left _ (hη j)
  -- The secant formula moves the approximate point into the squared-error ideal.
  obtain ⟨E, _, hE⟩ :=
    MvPolynomial.exists_eval₂_sub_eq_mulVec_of_sub_mem_span_mul φ F a c a d I hc ha
  change (fun i => MvPolynomial.eval₂ φ c (F i) - MvPolynomial.eval₂ φ a (F i)) =
    (A + d • E).mulVec (fun i => c i - a i) at hE
  rw [hca] at hE
  have hres : ∀ i, MvPolynomial.eval₂ φ c (F i) - t i = d * E.mulVec η i := by
    intro i
    have hi := congrFun hE i
    rw [Matrix.add_mulVec, Matrix.smul_mulVec] at hi
    change MvPolynomial.eval₂ φ c (F i) - MvPolynomial.eval₂ φ a (F i) =
      A.mulVec η i + d * E.mulVec η i at hi
    calc
      MvPolynomial.eval₂ φ c (F i) - t i =
          (MvPolynomial.eval₂ φ c (F i) - MvPolynomial.eval₂ φ a (F i)) -
            (t i - MvPolynomial.eval₂ φ a (F i)) := by ring
      _ = d * E.mulVec η i := by rw [hi, congrFun ht i]; ring
  have hres_mem : ∀ i, MvPolynomial.eval₂ φ c (F i) - t i ∈
      Ideal.span ({d ^ 2} : Set R) * I := by
    intro i
    obtain ⟨z, hz, hzη⟩ := Ideal.mem_span_singleton_mul.mp (hmulVec E i)
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨z, hz, ?_⟩
    rw [hres i, ← hzη]
    ring
  -- Apply the same polynomial secant formula to the derivative family.
  let B : Matrix σ σ R := fun i j =>
    MvPolynomial.eval₂ φ c (MvPolynomial.pderiv j (F i))
  obtain ⟨D, _, hD⟩ :=
    MvPolynomial.exists_eval₂_sub_eq_mulVec_of_sub_mem_span_mul φ
      (fun k : σ × σ => MvPolynomial.pderiv k.2 (F k.1)) a c a d I hc ha
  rw [hca] at hD
  have hBA : ∀ i j, B i j - A i j ∈ Ideal.span ({A.det} : Set R) * I := by
    intro i j
    have hij := congrFun hD (i, j)
    change B i j - A i j = _ at hij
    rw [hij]
    exact hmulVec _ (i, j)
  have hassoc : Associated B.det A.det :=
    Matrix.associated_det_of_sub_mem_span_mul B A I HenselianRing.jac hBA
  have hspan : Ideal.span ({B.det} : Set R) = Ideal.span ({d} : Set R) := by
    apply le_antisymm
    · exact Ideal.span_singleton_le_span_singleton.mpr hassoc.symm.dvd
    · exact Ideal.span_singleton_le_span_singleton.mpr hassoc.dvd
  have hspan_sq : Ideal.span ({B.det ^ 2} : Set R) * I =
      Ideal.span ({d ^ 2} : Set R) * I := by
    have hp := congrArg (fun K : Ideal R => K ^ 2) hspan
    have hs : Ideal.span ({B.det ^ 2} : Set R) =
        Ideal.span ({d ^ 2} : Set R) := by
      calc
        Ideal.span ({B.det ^ 2} : Set R) = (Ideal.span ({B.det} : Set R)) ^ 2 :=
          (Ideal.span_singleton_pow B.det 2).symm
        _ = (Ideal.span ({d} : Set R)) ^ 2 := hp
        _ = Ideal.span ({d ^ 2} : Set R) := Ideal.span_singleton_pow d 2
    exact congrArg (fun K : Ideal R => K * I) hs
  obtain ⟨b, hb, hbc⟩ :=
    HenselianRing.exists_eval₂_eq_of_sub_mem_det_sq_mul (I := I) φ F c t (by
      intro i
      change MvPolynomial.eval₂ φ c (F i) - t i ∈
        Ideal.span ({B.det ^ 2} : Set R) * I
      rw [hspan_sq]
      exact hres_mem i)
  refine ⟨b, hb, ?_⟩
  intro i
  change b i - a i ∈ J
  have hbci := hbc i
  change b i - c i ∈ Ideal.span ({B.det} : Set R) * I at hbci
  rw [hspan] at hbci
  have hsum : b i - a i = (b i - c i) + (c i - a i) := by ring
  rw [hsum]
  exact J.add_mem hbci (hc i)

end HenselianRing

@[expose] public section

namespace HenselianRing

universe u₁ v₁ w₁

open Classical in
/-- A target is attained with coordinate corrections in `J = (det A) I` if and only if its
value displacement is the Jacobian image of a vector whose coordinates lie in `J`. -/
theorem exists_eval₂_eq_iff_exists_sub_eq_mulVec
    {C : Type u₁} [CommSemiring C] {R : Type v₁} [CommRing R]
    {σ : Type w₁} [Fintype σ] {I : Ideal R} [HenselianRing R I]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a t : σ → R) :
    let A : Matrix σ σ R := fun i j =>
      MvPolynomial.eval₂ φ a (MvPolynomial.pderiv j (F i))
    let J : Ideal R := Ideal.span ({A.det} : Set R) * I
    (∃ b : σ → R, (∀ i, MvPolynomial.eval₂ φ b (F i) = t i) ∧
      ∀ i, b i - a i ∈ J) ↔
    (∃ η : σ → R, (∀ i, η i ∈ J) ∧
      (fun i => t i - MvPolynomial.eval₂ φ a (F i)) = A.mulVec η) := by
  dsimp only
  constructor
  · rintro ⟨b, hb_eval, hb_box⟩
    obtain ⟨η, hη, hdisplacement⟩ :=
      MvPolynomial.exists_eval₂_sub_eq_jacobian_mulVec_of_sub_mem_span_det_mul
        φ F a I b hb_box
    refine ⟨η, hη, ?_⟩
    have hA :
        Matrix.of (fun i j => MvPolynomial.eval₂ φ a (MvPolynomial.pderiv j (F i))) =
          (fun i j => MvPolynomial.eval₂ φ a (MvPolynomial.pderiv j (F i))) := by
      funext i j
      rfl
    rw [hA] at hdisplacement
    simpa only [hb_eval] using hdisplacement
  · exact HenselianRing.exists_eval₂_eq_of_sub_eq_mulVec φ F a t

end HenselianRing
