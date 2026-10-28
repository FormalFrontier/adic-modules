module

import AdicModules.MvPolynomial.HenselDeterminant

@[expose] public section

universe uC uR uι

open MvPolynomial

/-- The coupled image theorem applies to an arbitrary submodule, retaining both the
adjugate source witness and the linear restriction on the source. -/
example {C : Type uC} [CommSemiring C] {R : Type uR} [CommRing R]
    {I : Ideal R} [HenselianRing R I]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a : ι → R)
    (N : Submodule R (ι → R))
    (hN : let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
      Submodule.pi Set.univ
        (fun _ : ι => (Ideal.span ({A.det ^ 2} : Set R) * (I * I) : Submodule R R)) ≤ N) :
    let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := A.det
    (fun b : ι → R => fun i => eval₂ φ b (P i)) ''
        {b : ι → R | (∃ z : ι → R, (∀ i, z i ∈ I) ∧
          b = a + d • A.adjugate.mulVec z) ∧ A.mulVec (b - a) ∈ N} =
      {t : ι → R | (t - fun i => eval₂ φ a (P i)) ∈
        N ⊓ Submodule.pi Set.univ
          (fun _ : ι => (Ideal.span ({d ^ 2} : Set R) * I : Submodule R R))} := by
  exact HenselianRing.image_eval₂_adjugate_neighborhood_inf φ P a N hN
