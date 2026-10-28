/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.MvPolynomial.HenselDeterminant
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic

/-! # Unique preimages in a constrained proper adjugate neighborhood -/

open MvPolynomial

universe u v w

example {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    {I : Ideal R} [HenselianRing R I] {ι : Type w} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (P : ι → MvPolynomial ι C) (a : ι → R)
    (N : Submodule R (ι → R)) :
    let A : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
    let d : R := A.det
    (hd : d ∈ nonZeroDivisors R) →
      (hN : Submodule.pi Set.univ
        (fun _ : ι => (Ideal.span ({d ^ 2} : Set R) * (I * I) : Submodule R R)) ≤ N) →
        let h := HenselianRing.bijOn_eval₂_adjugate_neighborhood_inf
          (I := I) φ P a N hd hN
        ∀ y, ∃! b, h.mapsTo.restrict _ _ _ b = y := by
  dsimp only
  intro hd hN
  exact (HenselianRing.bijOn_eval₂_adjugate_neighborhood_inf
    (I := I) φ P a N hd hN).bijective.existsUnique
