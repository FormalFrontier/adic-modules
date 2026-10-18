/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.WittVector.TeichmullerSeries
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Domain

/-!
# Characteristic zero, units, locality, reducedness and prime-power multiplication and Teichmüller expansions in Witt vectors

For a prime `p` and a commutative ring `R` of characteristic `p`, `WittVector p R`
has characteristic zero. The proof uses Mathlib's comparison with the `p`-adic
integers over `ZMod p`, followed by injective functoriality for the canonical map
`ZMod p →+* R`.

No perfectness, field, reducedness or finiteness assumption is needed.
Nontriviality of `R` follows from `CharP R p` and primality of `p`, so it is not
an additional hypothesis. The instance supplies the usual characteristic-zero
API, including `Nat.cast_inj`, `Nat.cast_ne_zero` and `Int.cast_injective`.

For prime `p` and a commutative ring `R` with `CharP R p`, the unit criterion
states `IsUnit x ↔ IsUnit (x.coeff 0)`. For coefficient fields this becomes
`IsUnit x ↔ x.coeff 0 ≠ 0`. Under the same prime-characteristic
commutative-ring hypotheses, the locality criterion states
`IsLocalRing (WittVector p R) ↔ IsLocalRing R`. Neither the generic unit
criterion nor the locality criterion requires a field or perfectness.

Both the prime-multiplication statements and the uniqueness statement below
also assume prime `p`, `[CommRing R]` and `[CharP R p]`; uniqueness additionally
assumes `[IsReduced R]` and does not require perfectness.

For any prime `p` and commutative ring `R`, `WittVector.isReduced_iff` states that
`WittVector p R` is reduced if and only if `R` is reduced. This equivalence has no
characteristic, nontriviality, domain, perfectness or completeness hypothesis;
in particular, it includes the zero ring.

For the prime-multiplication criterion, assume that `R` has characteristic `p`.

Multiplication by `p ^ n` has a more sensitive dependence on the coefficient ring:
for every natural `n`, including zero, its kernel consists of Witt vectors whose
coefficients have zero `(p ^ n)`-th power. The multiplication-by-`p` criterion is
the specialization at `n = 1`.
Consequently, `p` is a regular element of `WittVector p R` exactly when `R` is
reduced. This criterion allows reduced rings with zero divisors and does not
require perfectness.

For reduced coefficient rings of characteristic `p`, `teichmuller_expansion_unique` states uniqueness of
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
* Mathlib's `RingTheory/WittVector/DiscreteValuationRing.lean` (Robert Y. Lewis,
  Heather Macbeth and Johan Commelin) for the generic unit constructor
  `WittVector.mkUnit` and its field consequence, and
  `RingTheory/WittVector/Teichmuller.lean` for the surjective constant-coefficient map.
* Mathlib's `RingTheory/LocalRing/Basic.lean` (Kenny Lau, Chris Hughes and
  Mario Carneiro) for the local-ring unit criteria and descent along a surjective
  ring homomorphism.
* Mathlib's `RingTheory/WittVector/Teichmuller.lean` (Johan Commelin) for
  `WittVector.teichmuller`, used to reflect reducedness to the coefficient ring.
* Mathlib's `RingTheory/WittVector/Domain.lean` (Robert Y. Lewis) for the
  characteristic-`p` Witt-vector domain instance, and
  `RingTheory/WittVector/Basic.lean` (Johan Commelin and Robert Y. Lewis) for
  `WittVector.ghostEquiv` when `p` is invertible.
* Mathlib's `RingTheory/Nilpotent/Lemmas.lean` (Oliver Nash) for
  `nilpotent_iff_mem_prime`, the all-prime-ideal nilpotence criterion.

The reducedness proof here combines the two field cases through fraction fields
of prime quotients. The all-prime-ideal test makes each coefficient nilpotent,
so reducedness of the coefficient ring makes it zero.
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

/-- A Witt vector over a commutative ring of prime characteristic is a unit exactly
when its constant coefficient is a unit. This characterizes the vectors represented
by Mathlib's `WittVector.mkUnit` without a field hypothesis. -/
theorem isUnit_iff_isUnit_coeff_zero {p : ℕ} [Fact p.Prime] {R : Type u}
    [CommRing R] [CharP R p] (x : WittVector p R) :
    IsUnit x ↔ IsUnit (x.coeff 0) := by
  constructor
  · intro hx
    simpa only [constantCoeff_apply] using
      (constantCoeff : WittVector p R →+* R).isUnit_map hx
  · rintro ⟨a, ha⟩
    exact ⟨mkUnit ha.symm, coe_mkUnit ha.symm⟩

/-- Over a field of prime characteristic, a Witt vector is a unit exactly when its
constant coefficient is nonzero. The reverse implication is Mathlib's
`WittVector.isUnit_of_coeff_zero_ne_zero`. -/
theorem isUnit_iff_coeff_zero_ne_zero {p : ℕ} [Fact p.Prime] {k : Type u}
    [Field k] [CharP k p] (x : WittVector p k) :
    IsUnit x ↔ x.coeff 0 ≠ 0 := by
  exact (isUnit_iff_isUnit_coeff_zero x).trans isUnit_iff_ne_zero

/-- For a commutative ring of prime characteristic, its Witt vector ring is local
exactly when the coefficient ring is local. -/
theorem isLocalRing_iff {p : ℕ} [Fact p.Prime] {R : Type u}
    [CommRing R] [CharP R p] :
    IsLocalRing (WittVector p R) ↔ IsLocalRing R := by
  constructor
  · intro h
    letI := h
    letI : Nontrivial R := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
    exact IsLocalRing.of_surjective' (constantCoeff : WittVector p R →+* R)
      (constantCoeff_surjective p)
  · intro h
    letI := h
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro x
    simp only [isUnit_iff_isUnit_coeff_zero]
    change IsUnit (constantCoeff x) ∨ IsUnit (constantCoeff (1 - x))
    simpa only [map_sub, map_one] using
      IsLocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff x)

/-- For a prime `p`, the Witt vectors over a commutative ring are reduced if and only
if the coefficient ring is reduced, without any characteristic or nontriviality assumption. -/
theorem isReduced_iff {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] :
    IsReduced (WittVector p R) ↔ IsReduced R := by
  classical
  constructor
  · intro hW
    letI : IsReduced (WittVector p R) := hW
    constructor
    intro r hr
    have ht : IsNilpotent (teichmuller p r) := by
      rcases hr with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [← map_pow, hn, teichmuller_zero]
    have hz : teichmuller p r = 0 := ht.eq_zero
    simpa only [teichmuller_coeff_zero, zero_coeff] using
      congrArg (fun w : WittVector p R => w.coeff 0) hz
  · intro hR
    letI : IsReduced R := hR
    have hfield : ∀ (K : Type u) [Field K], IsReduced (WittVector p K) := by
      intro K hK
      by_cases hp : (p : K) = 0
      · letI : CharP K p :=
          (CharP.charP_iff_prime_eq_zero (R := K) (Fact.out : p.Prime)).2 hp
        letI : IsDomain (WittVector p K) := inferInstance
        infer_instance
      · letI : Invertible (p : K) := invertibleOfNonzero hp
        exact isReduced_of_injective (ghostEquiv p K).toRingHom
          (ghostEquiv p K).injective
    constructor
    intro x hx
    apply WittVector.ext
    intro n
    rw [zero_coeff]
    apply IsNilpotent.eq_zero
    apply nilpotent_iff_mem_prime.mpr
    intro P hP
    letI : P.IsPrime := hP
    let f : R →+* FractionRing (R ⧸ P) :=
      (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P)
    letI : IsReduced (WittVector p (FractionRing (R ⧸ P))) :=
      hfield (FractionRing (R ⧸ P))
    have hmap : map (p := p) f x = 0 := (hx.map (map (p := p) f)).eq_zero
    have hcoeff : f (x.coeff n) = 0 := (map_eq_zero_iff f).mp hmap n
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))
    simpa only [f, RingHom.comp_apply, map_zero] using hcoeff

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

/-- A Witt vector over a ring of characteristic `p` is killed by multiplication by
`p ^ n` exactly when every coefficient has zero `(p ^ n)`-th power. -/
theorem mul_p_pow_eq_zero_iff_coeff_pow_eq_zero (x : WittVector p k) (n : ℕ) :
    x * (p : WittVector p k) ^ n = 0 ↔ ∀ i : ℕ, x.coeff i ^ (p ^ n) = 0 := by
  constructor
  · intro h i
    simpa only [mul_pow_charP_coeff_succ, zero_coeff] using
      congrArg (fun y : WittVector p k => y.coeff (i + n)) h
  · intro h
    apply WittVector.ext
    intro i
    rw [zero_coeff]
    by_cases hi : i < n
    · exact mul_pow_charP_coeff_zero x hi
    · rw [← Nat.sub_add_cancel (Nat.le_of_not_gt hi), mul_pow_charP_coeff_succ,
        h (i - n)]

/-- A Witt vector over a ring of characteristic `p` is killed by multiplication by `p`
exactly when every coefficient has zero `p`-th power. -/
theorem mul_p_eq_zero_iff_coeff_pow_eq_zero (x : WittVector p k) :
    x * (p : WittVector p k) = 0 ↔ ∀ n : ℕ, x.coeff n ^ p = 0 := by
  simpa only [pow_one] using mul_p_pow_eq_zero_iff_coeff_pow_eq_zero x 1

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
