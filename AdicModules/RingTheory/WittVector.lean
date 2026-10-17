/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.WittVector.TeichmullerSeries
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.WittVector.Compare

/-!
# Characteristic zero and prime multiplication and Teichmüller expansions in Witt vectors

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

For reduced coefficient rings, `teichmuller_expansion_unique` states uniqueness of
the digits in two Teichmüller expansions approximating the same Witt vector
modulo every positive power of `p`. Reducedness makes Frobenius injective, allowing
digits to be recovered from their iterated `p`-th powers. The statement requires
neither perfectness nor a topology and does not assert existence of an expansion
for every Witt vector.

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
* Mathlib's `RingTheory/WittVector/TeichmullerSeries.lean` (Jiedong Jiang) for
  finite-sum and Teichmüller-term coefficient formulas.
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

/-- Two Teichmüller digit sequences approximating the same Witt vector modulo every
positive power of `p` are equal over a reduced coefficient ring. -/
theorem teichmuller_expansion_unique {p : ℕ} [Fact p.Prime] {R : Type u}
    [CommRing R] [CharP R p] [IsReduced R]
    (x : WittVector p R) (a b : ℕ → R)
    (ha : ∀ n : ℕ, (p : WittVector p R) ^ (n + 1) ∣
      x - ∑ i ∈ Finset.range (n + 1),
        teichmuller p (a i) * (p : WittVector p R) ^ i)
    (hb : ∀ n : ℕ, (p : WittVector p R) ^ (n + 1) ∣
      x - ∑ i ∈ Finset.range (n + 1),
        teichmuller p (b i) * (p : WittVector p R) ^ i) :
    a = b := by
  classical
  have coeff_approx (c : ℕ → R) (n : ℕ)
      (hc : (p : WittVector p R) ^ (n + 1) ∣
        x - ∑ i ∈ Finset.range (n + 1),
          teichmuller p (c i) * (p : WittVector p R) ^ i) :
      x.coeff n = c n ^ (p ^ n) := by
    -- Multiples of p^(n+1) have zero coefficients through degree n.
    have hlow : ∀ i < n + 1,
        x.coeff i =
          (∑ j ∈ Finset.range (n + 1),
            teichmuller p (c j) * (p : WittVector p R) ^ j).coeff i := by
      apply le_coeff_eq_iff_le_sub_coeff_eq_zero.mpr
      obtain ⟨y, hy⟩ := hc
      intro i hi
      rw [hy, mul_comm]
      exact mul_pow_charP_coeff_zero y hi
    rw [hlow n (Nat.lt_succ_self n)]
    -- The Teichmüller terms have disjoint coefficient supports.
    rw [sum_coeff_eq_coeff_sum]
    · rw [Finset.sum_eq_single_of_mem n
        (Finset.mem_range.mpr (Nat.lt_succ_self n))]
      · exact teichmuller_mul_pow_coeff n (c n)
      · intro i _ hin
        exact teichmuller_mul_pow_coeff_of_ne (c i) hin.symm
    · intro m
      refine ⟨fun i j => ?_⟩
      apply Subtype.ext
      have hi : m = i.1 := by
        by_contra hmi
        exact i.2.2 (teichmuller_mul_pow_coeff_of_ne (c i.1) hmi)
      have hj : m = j.1 := by
        by_contra hmj
        exact j.2.2 (teichmuller_mul_pow_coeff_of_ne (c j.1) hmj)
      exact hi.symm.trans hj
  funext n
  apply _root_.iterateFrobenius_inj R p n
  change a n ^ (p ^ n) = b n ^ (p ^ n)
  exact (coeff_approx a n (ha n)).symm.trans (coeff_approx b n (hb n))

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
