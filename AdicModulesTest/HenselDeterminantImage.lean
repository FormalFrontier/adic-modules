/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.MvPolynomial.HenselDeterminant

/-!
# Roots from a coupled Jacobian-image witness

The determinant-neighborhood image theorem turns a witness in the coupled
linear image of an ideal into a root in the whole coordinate neighborhood.
The coefficient homomorphism and the center are arbitrary.
-/

open MvPolynomial

universe uC uR uσ

example {C : Type uC} [CommSemiring C] {R : Type uR} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {σ : Type uσ} [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R)
    (x : σ → R) (hx : ∀ i, x i ∈ I)
    (hroot : let A : Matrix σ σ R :=
        Matrix.of fun i j => (pderiv j (F i)).eval₂ φ a
      (fun i => -(F i).eval₂ φ a) = (A.det • A).mulVec x) :
    ∃ b : σ → R,
      (∀ i, b i - a i ∈ Ideal.span
        ({(Matrix.of fun i j => (pderiv j (F i)).eval₂ φ a).det} : Set R) * I) ∧
      ∀ i, (F i).eval₂ φ b = 0 := by
  have himage := HenselianRing.image_eval₂_det_neighborhood (I := I) φ F a
  have hmem : (0 : σ → R) ∈
      {y : σ → R | ∃ v : σ → R, (∀ i, v i ∈ I) ∧
        (fun i => y i - (F i).eval₂ φ a) =
          ((Matrix.of fun i j => (pderiv j (F i)).eval₂ φ a).det •
            (Matrix.of fun i j => (pderiv j (F i)).eval₂ φ a)).mulVec v} := by
    exact ⟨x, hx, by simpa only [Pi.zero_apply, zero_sub] using hroot⟩
  rw [← himage] at hmem
  obtain ⟨b, hb, hvalue⟩ := hmem
  exact ⟨b, hb, fun i => congrFun hvalue i⟩
