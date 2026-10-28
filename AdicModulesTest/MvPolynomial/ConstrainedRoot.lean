/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.MvPolynomial.HenselDeterminant

/-!
# Roots with a linearized submodule constraint

A coupled linear witness for the negative initial value gives a polynomial root
in the whole determinant neighborhood with the prescribed linearized constraint.
-/

@[expose] public section

universe uC uR uσ

open MvPolynomial

/-- A root can be chosen in the determinant neighborhood while its linearized
increment belongs to any submodule containing the quadratic error. -/
private theorem exists_root_mem_det_neighborhood_inf
    {C : Type uC} [CommSemiring C] {R : Type uR} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {σ : Type uσ} [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R)
    (N : Submodule R (σ → R)) :
    let A : Matrix σ σ R := Matrix.of fun i j => (pderiv j (F i)).eval₂ φ a
    let d : R := A.det
    Submodule.pi Set.univ
        (fun _ : σ => (Ideal.span ({d ^ 2} : Set R) * I ^ 2 : Submodule R R)) ≤ N →
      -(fun i => (F i).eval₂ φ a) ∈ N →
      (∃ x : σ → R, (∀ i, x i ∈ I) ∧
        -(fun i => (F i).eval₂ φ a) = (d • A).mulVec x) →
      ∃ b : σ → R, (∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I) ∧
        (fun i => (F i).eval₂ φ b) = 0 ∧ A.mulVec (b - a) ∈ N := by
  intro A d hN ha hx
  have hzero : (0 : σ → R) ∈
      (fun b : σ → R => fun i => (F i).eval₂ φ b) ''
        {b : σ → R | (∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I) ∧
          A.mulVec (b - a) ∈ N} := by
    rw [HenselianRing.image_eval₂_det_neighborhood_inf φ F a N hN]
    exact ⟨by simpa only [zero_sub] using ha, by simpa only [zero_sub] using hx⟩
  obtain ⟨b, ⟨hb, hAb⟩, hroot⟩ := hzero
  exact ⟨b, hb, hroot, hAb⟩
