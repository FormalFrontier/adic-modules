/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import AdicModules

/-!
# Injectivity on a Jacobian-scaled box

Evaluation is injective on the subtype of the box
`{b | ∀ i, b i - a i ∈ Ideal.span {d} * I}`, where `d` is the Jacobian
determinant at `a`, when `d` and every `1 + x` with `x ∈ I` are regular.
-/

universe u v w

namespace MvPolynomial

example
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R]
    [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C)
    (a : σ → R) (I : Ideal R)
    (hI : ∀ x : R, x ∈ I → IsRegular (1 + x)) :
    let M : Matrix σ σ R :=
      Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
    let d : R := M.det
    let J : Ideal R := Ideal.span {d} * I
    IsRegular d →
      Function.Injective
        (fun b : {b : σ → R // ∀ i, b i - a i ∈ J} =>
          fun i => (F i).eval₂ φ b.val) := by
  dsimp only
  intro hd b c hbc
  apply Subtype.ext
  exact injOn_eval₂_of_isRegular_det_of_isRegular_one_add
    φ F a I hI hd b.property c.property hbc

end MvPolynomial
