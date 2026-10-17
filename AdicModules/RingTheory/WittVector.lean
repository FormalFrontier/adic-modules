/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.RingTheory.WittVector.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.WittVector.Compare

/-!
# Characteristic zero and prime multiplication in Witt vectors

For a prime `p` and a commutative ring `R` of characteristic `p`, `WittVector p R`
has characteristic zero. The proof uses Mathlib's comparison with the `p`-adic
integers over `ZMod p`, followed by injective functoriality for the canonical map
`ZMod p →+* R`.

No perfectness, field, reducedness or finiteness assumption is needed.
Nontriviality of `R` follows from `CharP R p` and primality of `p`, so it is not
an additional hypothesis. The instance supplies the usual characteristic-zero
API, including `Nat.cast_inj`, `Nat.cast_ne_zero` and `Int.cast_injective`.

Multiplication by `p` has a more sensitive dependence on the coefficient ring:
its kernel consists of Witt vectors whose coefficients have zero `p`-th power.
Consequently, `p` is a regular element of `WittVector p R` exactly when `R` is
reduced. This criterion allows reduced rings with zero divisors and does not
require perfectness.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition, I §8, (8.3), for the characteristic-zero assertion in the perfect-field
  setting.
* Mathlib's `RingTheory/WittVector/Compare.lean` (Johan Commelin and Robert Y. Lewis)
  for the comparison with the `p`-adic integers, and
  `RingTheory/WittVector/Basic.lean` for coefficientwise functoriality.
* Mathlib's `RingTheory/WittVector/Identities.lean`, `Frobenius.lean` and
  `Verschiebung.lean` for the prime-multiplication and Frobenius identities, and
  `Algebra/CharP/Reduced.lean` for injectivity of Frobenius on reduced rings.
* Mathlib's `RingTheory/WittVector/Complete.lean` for the perfect-coefficient
  zero-kernel criterion with which the coefficientwise criterion is compared.
-/

@[expose] public section

universe u

namespace WittVector

/-- Witt vectors over any commutative ring of prime characteristic have characteristic
zero. This generalizes the characteristic-zero assertion for perfect coefficient fields
in Fesenko–Vostokov, I §8, (8.3). -/
instance charZero (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p] :
    CharZero (WittVector p R) := by
  letI : CharZero (WittVector p (ZMod p)) :=
    charZero_of_injective_ringHom (f := (equiv p).symm.toRingHom) (equiv p).symm.injective
  exact charZero_of_injective_ringHom
    (f := map (p := p) (ZMod.castHom (dvd_refl p) R))
    (map_injective _ (ZMod.castHom_injective R))

variable {p : ℕ} [Fact p.Prime] {k : Type u} [CommRing k] [CharP k p]

/-- A Witt vector over a ring of characteristic `p` is killed by multiplication by `p`
exactly when every coefficient has zero `p`-th power. -/
theorem mul_p_eq_zero_iff_coeff_pow_eq_zero (x : WittVector p k) :
    x * (p : WittVector p k) = 0 ↔ ∀ n : ℕ, x.coeff n ^ p = 0 := by
  constructor
  · intro h n
    simpa only [mul_charP_coeff_succ, zero_coeff] using
      congrArg (fun y : WittVector p k => y.coeff (n + 1)) h
  · intro h
    apply WittVector.ext
    intro n
    cases n with
    | zero => rw [mul_charP_coeff_zero, zero_coeff]
    | succ n => rw [mul_charP_coeff_succ, zero_coeff, h n]

/-- The prime `p` is a regular element of the Witt vector ring exactly when the
coefficient ring is reduced. No perfectness or domain hypothesis is required. -/
theorem isRegular_p_iff_isReduced :
    IsRegular (p : WittVector p k) ↔ IsReduced k := by
  constructor
  · intro hreg
    apply (isReduced_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mpr
    intro a ha
    have hx : (mk p fun _ : ℕ => a) * (p : WittVector p k) = 0 := by
      apply (mul_p_eq_zero_iff_coeff_pow_eq_zero _).mpr
      intro n
      simpa only [coeff_mk] using ha
    have hzero : (mk p fun _ : ℕ => a) = (0 : WittVector p k) :=
      hreg.right (by simpa only [zero_mul] using hx)
    simpa only [coeff_mk, zero_coeff] using
      congrArg (fun x : WittVector p k => x.coeff 0) hzero
  · intro hk
    letI : IsReduced k := hk
    have hker (x : WittVector p k) (hx : x * (p : WittVector p k) = 0) : x = 0 := by
      apply WittVector.ext
      intro n
      rw [zero_coeff]
      exact eq_zero_of_pow_eq_zero
        ((mul_p_eq_zero_iff_coeff_pow_eq_zero x).mp hx n)
    have hright : IsRightRegular (p : WittVector p k) := by
      intro x y hxy
      exact sub_eq_zero.mp (hker (x - y) (by
        rw [sub_mul]
        exact sub_eq_zero.mpr hxy))
    refine ⟨?_, hright⟩
    intro x y hxy
    apply hright
    simpa only [mul_comm] using hxy

end WittVector
