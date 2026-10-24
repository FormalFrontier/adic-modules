/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.WittVector.Frobenius

/-!
# Witt Frobenius and perfect coefficient rings

For a prime `p` and a commutative ring `R` of characteristic `p`, the canonical
Frobenius endomorphism of `WittVector p R` is bijective exactly when `R` is
perfect. The coefficient ring need not be a field or a domain.

The endomorphism here is `WittVector.frobenius`, whose coefficients in
characteristic `p` are the `p`th powers of the original coefficients. It is not
the ordinary ring Frobenius applied to the Witt-vector ring. The characteristic
hypothesis is Mathlib's exact `CharP R p`; for prime `p` it excludes the zero
ring, which has characteristic one.

## References

This API uses Mathlib's Witt Frobenius, its characteristic-`p` coefficient
formula, and its `PerfectRing` class. The perfect-coefficient implication is
already provided by `WittVector.frobenius_bijective` in Mathlib.
-/

@[expose] public section

universe u

namespace WittVector

/-- Over a commutative coefficient ring of prime characteristic, the canonical
Witt Frobenius is bijective if and only if the coefficient ring is perfect. -/
theorem frobenius_bijective_iff (p : ℕ) (R : Type u)
    [Fact p.Prime] [CommRing R] [CharP R p] :
    Function.Bijective (@WittVector.frobenius p R _ _) ↔ PerfectRing R p := by
  constructor
  · intro h
    have hcoeff : Function.Bijective
        (WittVector.coeff : WittVector p R → ℕ → R) :=
      ⟨fun _ _ hxy => WittVector.ext (congrFun hxy),
        fun a => ⟨WittVector.mk p a, WittVector.coeff_mk p a⟩⟩
    have hcomm :
        (WittVector.coeff : WittVector p R → ℕ → R) ∘ WittVector.frobenius =
          (fun a : ℕ → R => (fun x : R => x ^ p) ∘ a) ∘ WittVector.coeff := by
      funext x n
      exact WittVector.coeff_frobenius_charP p x n
    have hpost : Function.Bijective
        (fun a : ℕ → R => (fun x : R => x ^ p) ∘ a) := by
      apply (Function.Bijective.of_comp_iff _ hcoeff).mp
      rw [← hcomm]
      exact Function.Bijective.comp hcoeff h
    exact ⟨⟨(Function.injective_comp_left_iff (α := ℕ)).mp hpost.1,
      (Function.surjective_comp_left_iff (α := ℕ)).mp hpost.2⟩⟩
  · intro hp
    have : PerfectRing R p := hp
    exact WittVector.frobenius_bijective p R

end WittVector
