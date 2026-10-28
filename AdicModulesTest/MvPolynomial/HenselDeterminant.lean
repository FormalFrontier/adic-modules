/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuttle
-/
module

import AdicModules.MvPolynomial.HenselDeterminant

/-! # Target-ideal precision in polynomial adjugate neighborhoods -/

open MvPolynomial

universe u v w

/- A target of any finer ideal precision has a preimage satisfying both the
adjugate-neighborhood and Jacobian-preimage restrictions. -/
example {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a : ι → R)
    (J₀ : Ideal R) (t : ι → R) :
    let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := A.det
    J₀ ≤ Ideal.span ({d ^ 2} : Set R) * I →
      (∀ i, t i - eval₂ φ a (P i) ∈ J₀) →
      ∃ b : ι → R,
        (∃ z : ι → R, (∀ i, z i ∈ I) ∧
          b = a + d • A.adjugate.mulVec z) ∧
        (∀ i, A.mulVec (b - a) i ∈ J₀) ∧
        ∀ i, eval₂ φ b (P i) = t i := by
  intro A d hJ₀ ht
  have ht' : t ∈ {s : ι → R | ∀ i, s i - eval₂ φ a (P i) ∈ J₀} := ht
  rw [← HenselianRing.image_eval₂_adjugate_neighborhood_inter_jacobian_preimage
    (I := I) φ P a J₀ hJ₀] at ht'
  obtain ⟨b, hb, hbt⟩ := ht'
  exact ⟨b, hb.1, hb.2, fun i => congrFun hbt i⟩
