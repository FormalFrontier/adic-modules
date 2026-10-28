/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.MvPolynomial.Evaluation
import AdicModules.MvPolynomial.HenselDeterminant
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Set.Image

/-!
# Images of kernel-thickened adjugate neighborhoods

The preimage characterization identifies the values attained on a constrained proper
adjugate neighborhood plus the small Jacobian kernel with the values attained on the
scalar box that lie in the target. This is an image cut, not a surjectivity assertion
onto the target, and does not require a regular determinant.
-/

public section

open scoped Pointwise

universe u v w

example {C : Type u} {R : Type v} {ι : Type w}
    [CommSemiring C] [CommRing R] [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (φ : C →+* R)
    (P : ι → MvPolynomial ι C) (a : ι → R)
    (N : AddSubgroup (ι → R)) :
    let A : Matrix ι ι R :=
      fun i j => MvPolynomial.eval₂ φ a (MvPolynomial.pderiv j (P i))
    let d : R := A.det
    let F : (ι → R) → (ι → R) := fun b i => MvPolynomial.eval₂ φ b (P i)
    (Submodule.pi Set.univ
      (fun _ : ι => Ideal.span ({d ^ 2} : Set R) * (I * I))).toAddSubgroup ≤ N →
      F '' ({b : ι → R |
        (∃ z : ι → R, (∀ i, z i ∈ I) ∧
          b = a + d • A.adjugate.mulVec z) ∧
        A.mulVec (b - a) ∈ N} +
      {κ : ι → R |
        (∀ i, κ i ∈ Ideal.span ({d} : Set R) * I) ∧ A.mulVec κ = 0}) =
      (F '' {b : ι → R |
        ∀ i, b i - a i ∈ Ideal.span ({d} : Set R) * I}) ∩
      {t : ι → R |
        t - F a ∈ N ⊓ (Submodule.pi Set.univ
          (fun _ : ι => Ideal.span ({d ^ 2} : Set R) * I)).toAddSubgroup} := by
  intro A d F hN
  rw [MvPolynomial.adjugate_neighborhood_add_ker_eq_inter_preimage I φ P a N hN]
  exact Set.image_inter_preimage F _ _
