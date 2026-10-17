/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.RingTheory.Valuation.Basic
import AdicModules.LinearAlgebra.SModEq.Pow
import AdicModulesTest.ValuationPowerModel
import Mathlib.Algebra.CharP.Quotient
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Finite power estimates for normalized additive valuations

Let `v : AddValuation K (WithTop ℤ)` be normalized by an element `π : K` of value one.
The canonical integer ring is `(AddValuation.toValuation v).valuationSubring`, with its
inclusion into `K` and its canonical residue field. Integral field elements are
represented in this subring, rather than in a proposition asserting an integers property.

For prime residue characteristic `p`, the finite estimate has every positive starting
depth `m` and every natural iterate `n`. Completeness, a topology, and perfectness of the
residue field are not needed. The normalization at `π` is the integer normalization of
a discrete valuation: merely having codomain `WithTop ℤ` would not identify the powers
of the maximal ideal with the thresholds `m`.

The multiplicative valuation takes values in `Multiplicative ((WithTop ℤ)ᵒᵈ)`.
Its order is reversed, additive infinity corresponds to multiplicative zero, and its
closed unit ball is exactly the integral elements. The residue characteristic only
forces a lower bound of one on `v p`; no equality `v p = 1` is imposed.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition
  (2002), Chapter I, §7, Lemma (7.2), p. 22; the normalization is from Chapter I, §3
  and the fixed uniformizer convention in §5.
* Mathlib's valuation, valuation-subring, principal-ideal, and residue-characteristic
  APIs provide the canonical algebraic objects. The power-congruence iteration is
  `SModEq.pow_pow_add`, extending Kenny Lau's `SModEq.pow_pow_add_one` from starting
  depth one to arbitrary positive starting depth.
-/

@[expose] public section

universe u

namespace AddValuation

variable {K : Type u} [Field K] (v : AddValuation K (WithTop ℤ))

/-- The canonical integer ring has the integers property for this valuation. -/
private theorem canonical_integers :
    (AddValuation.toValuation v).Integers ((AddValuation.toValuation v).valuationSubring) :=
  Valuation.valuationSubring.integers (AddValuation.toValuation v)

/-- The multiplicative value retains the order dual and the infinite additive value. -/
private theorem multiplicative_value (x : K) :
    (AddValuation.toValuation v) x =
      Multiplicative.ofAdd (OrderDual.toDual (v x)) :=
  AddValuation.toValuation_apply v x

/-- An integral field element has a representative in the canonical integer ring. -/
private theorem integral_input (α : K) (hα : 0 ≤ v α) :
    ∃ a : (AddValuation.toValuation v).valuationSubring,
      algebraMap ((AddValuation.toValuation v).valuationSubring) K a = α :=
  (canonical_integers v).exists_of_le_one
    (show (AddValuation.toValuation v) α ≤ 1 from hα)

/-- The algebra map is the inclusion of the canonical subtype. -/
private theorem inclusion_apply (a : (AddValuation.toValuation v).valuationSubring) :
    algebraMap ((AddValuation.toValuation v).valuationSubring) K a = (a : K) :=
  ValuationSubring.algebraMap_apply ((AddValuation.toValuation v).valuationSubring) a

/-- Differences of powers in the integer ring map to the corresponding field expression. -/
private theorem inclusion_pow_sub (a b : (AddValuation.toValuation v).valuationSubring) (N : ℕ) :
    algebraMap ((AddValuation.toValuation v).valuationSubring) K (a ^ N - b ^ N) =
      (a : K) ^ N - (b : K) ^ N := by
  rw [_root_.map_sub, _root_.map_pow, _root_.map_pow, inclusion_apply, inclusion_apply]

/-- The inclusion respects the natural-number cast used in the power congruence. -/
private theorem inclusion_natCast (p : ℕ) :
    algebraMap ((AddValuation.toValuation v).valuationSubring) K
      (p : (AddValuation.toValuation v).valuationSubring) = (p : K) :=
  map_natCast (algebraMap ((AddValuation.toValuation v).valuationSubring) K) p

/-- The canonical residue map is the quotient by this receiver's maximal ideal. -/
private theorem residue_apply (a : (AddValuation.toValuation v).valuationSubring) :
    IsLocalRing.residue ((AddValuation.toValuation v).valuationSubring) a =
      Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal ((AddValuation.toValuation v).valuationSubring)) a :=
  rfl

/-- Residue characteristic places the natural-number cast in the maximal ideal. -/
private theorem residue_characteristic_mem (p : ℕ)
    [CharP (IsLocalRing.ResidueField ((AddValuation.toValuation v).valuationSubring)) p] :
    (p : (AddValuation.toValuation v).valuationSubring) ∈
      IsLocalRing.maximalIdeal ((AddValuation.toValuation v).valuationSubring) := by
  apply (IsLocalRing.residue_eq_zero_iff
    (p : (AddValuation.toValuation v).valuationSubring)).mp
  simp only [_root_.map_natCast, CharP.cast_eq_zero]

/-- The principal-span value law is applied to the canonical receiver and inclusion. -/
private theorem principal_ideal_values (ϖ : (AddValuation.toValuation v).valuationSubring) :
    (Ideal.span {ϖ} : Set (AddValuation.toValuation v).valuationSubring) =
      {z : (AddValuation.toValuation v).valuationSubring |
        (AddValuation.toValuation v)
            (algebraMap ((AddValuation.toValuation v).valuationSubring) K z) ≤
          (AddValuation.toValuation v)
            (algebraMap ((AddValuation.toValuation v).valuationSubring) K ϖ)} :=
  (canonical_integers v).coe_span_singleton_eq_setOfPred_le_v_algebraMap ϖ

/-- A positive extended integer is at least one, including at infinity. -/
private theorem value_pos_iff_one_le (γ : WithTop ℤ) :
    0 < γ ↔ 1 ≤ γ := by
  cases γ with
  | top =>
    exact ⟨fun _ => le_top, fun _ => WithTop.coe_lt_top (0 : ℤ)⟩
  | coe z =>
    change ((0 : ℤ) : WithTop ℤ) < (z : WithTop ℤ) ↔
      ((1 : ℤ) : WithTop ℤ) ≤ (z : WithTop ℤ)
    rw [WithTop.coe_lt_coe, WithTop.coe_le_coe]
    exact Int.add_one_le_iff.symm

/-- Principal-ideal membership is an additive value threshold on the canonical subring. -/
private theorem principal_ideal_mem_iff
    (ϖ a : (AddValuation.toValuation v).valuationSubring) :
    a ∈ Ideal.span {ϖ} ↔ v (ϖ : K) ≤ v (a : K) := by
  change a ∈ (Ideal.span {ϖ} : Set (AddValuation.toValuation v).valuationSubring) ↔ _
  rw [principal_ideal_values v ϖ]
  change v (algebraMap ((AddValuation.toValuation v).valuationSubring) K ϖ) ≤
      v (algebraMap ((AddValuation.toValuation v).valuationSubring) K a) ↔
    v (ϖ : K) ≤ v (a : K)
  rw [inclusion_apply, inclusion_apply]

/-- An element of value one generates the canonical maximal ideal. -/
private theorem maximalIdeal_eq_span
    (ϖ : (AddValuation.toValuation v).valuationSubring)
    (hϖ : v (ϖ : K) = (1 : WithTop ℤ)) :
    IsLocalRing.maximalIdeal ((AddValuation.toValuation v).valuationSubring) =
      Ideal.span {ϖ} := by
  ext a
  rw [Valuation.mem_maximalIdeal_iff (v := AddValuation.toValuation v),
    principal_ideal_mem_iff v ϖ a]
  change 0 < v (a : K) ↔ v (ϖ : K) ≤ v (a : K)
  rw [hϖ, value_pos_iff_one_le]

/-- Every power of the canonical maximal ideal is its integral value threshold. -/
private theorem maximalIdeal_pow_mem_iff
    (ϖ : (AddValuation.toValuation v).valuationSubring)
    (hϖ : v (ϖ : K) = (1 : WithTop ℤ)) (m : ℕ)
    (a : (AddValuation.toValuation v).valuationSubring) :
    a ∈ (IsLocalRing.maximalIdeal ((AddValuation.toValuation v).valuationSubring)) ^ m ↔
      (m : WithTop ℤ) ≤ v (a : K) := by
  rw [maximalIdeal_eq_span v ϖ hϖ, Ideal.span_singleton_pow,
    principal_ideal_mem_iff v (ϖ ^ m) a]
  have hpow : v ((ϖ ^ m : (AddValuation.toValuation v).valuationSubring) : K) =
      (m : WithTop ℤ) := by
    rw [← inclusion_apply v (ϖ ^ m), _root_.map_pow, inclusion_apply,
      v.map_pow, hϖ, nsmul_one]
  rw [hpow]

/-- Positive-depth power congruences in the canonical integer ring. -/
private theorem integer_power_congruence (p : ℕ)
    [CharP (IsLocalRing.ResidueField ((AddValuation.toValuation v).valuationSubring)) p]
    {m : ℕ} (hm : 0 < m)
    {a b : (AddValuation.toValuation v).valuationSubring}
    (h : a ≡ b [SMOD
      (IsLocalRing.maximalIdeal ((AddValuation.toValuation v).valuationSubring)) ^ m]) (n : ℕ) :
    a ^ (p ^ n) ≡ b ^ (p ^ n) [SMOD
      (IsLocalRing.maximalIdeal ((AddValuation.toValuation v).valuationSubring)) ^ (m + n)] :=
  SModEq.pow_pow_add (residue_characteristic_mem v p) (Nat.ne_of_gt hm) h n

/-- Integral field elements gain at least one unit of additive value at each iterated
`p`-th power, from every positive integral starting depth. The element `π` records the
integer normalization of the discrete valuation, not an unramifiedness condition on `p`.
The zeroth iterate and zero or equal inputs are included. This is the finite estimate of
Fesenko–Vostokov, I §7, Lemma (7.2), without the ambient completeness assumption. -/
private theorem pow_pow_sub_lower_bound (π : K) (hπ : v π = (1 : WithTop ℤ))
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField ((AddValuation.toValuation v).valuationSubring)) p]
    (α β : K) (hα : 0 ≤ v α) (hβ : 0 ≤ v β)
    (m n : ℕ) (hm : 0 < m) (h : (m : WithTop ℤ) ≤ v (α - β)) :
    ((m + n : ℕ) : WithTop ℤ) ≤ v (α ^ (p ^ n) - β ^ (p ^ n)) := by
  obtain ⟨ϖ, hϖ⟩ := integral_input v π (by rw [hπ]; exact zero_le_one)
  obtain ⟨a, ha⟩ := integral_input v α hα
  obtain ⟨b, hb⟩ := integral_input v β hβ
  have hϖv : v (ϖ : K) = (1 : WithTop ℤ) := by
    rw [← inclusion_apply v ϖ, hϖ, hπ]
  have hab : a ≡ b [SMOD
      (IsLocalRing.maximalIdeal ((AddValuation.toValuation v).valuationSubring)) ^ m] := by
    apply SModEq.sub_mem.mpr
    apply (maximalIdeal_pow_mem_iff v ϖ hϖv m (a - b)).mpr
    rw [← inclusion_apply v (a - b), _root_.map_sub, ha, hb]
    exact h
  have hpow := integer_power_congruence v p hm hab n
  have hvalue := (maximalIdeal_pow_mem_iff v ϖ hϖv (m + n)
    (a ^ (p ^ n) - b ^ (p ^ n))).mp (SModEq.sub_mem.mp hpow)
  rw [← inclusion_apply v (a ^ (p ^ n) - b ^ (p ^ n)),
    inclusion_pow_sub v a b (p ^ n)] at hvalue
  rw [← inclusion_apply v a, ← inclusion_apply v b, ha, hb] at hvalue
  exact hvalue

/-- The estimate applied to the distinct canonical integral units `1, 4` over `ℚ_[3]`. -/
private theorem threeAdic_power_lower_bound :
    (2 : WithTop ℤ) ≤ Padic.addValuation
      ((1 : ℚ_[3]) ^ (3 ^ 1 : ℕ) - 4 ^ (3 ^ 1 : ℕ)) := by
  obtain ⟨hchar, hπ, _, _, _, _, hα, hβ, _, hdiff, _⟩ :=
    ValuationPowerModel.canonicalQ3_inputs
  letI := hchar
  have hα' : 0 ≤ Padic.addValuation (1 : ℚ_[3]) := by
    simpa only [_root_.map_one] using hα
  have hβ' : 0 ≤ Padic.addValuation (4 : ℚ_[3]) := by
    simpa only [_root_.map_ofNat] using hβ
  have hdiff' : (1 : WithTop ℤ) ≤ Padic.addValuation ((1 : ℚ_[3]) - 4) := by
    simpa only [_root_.map_one, _root_.map_ofNat] using hdiff.ge
  simpa using pow_pow_sub_lower_bound Padic.addValuation (3 : ℚ_[3]) hπ 3
    (1 : ℚ_[3]) 4 hα' hβ' 1 1 (by decide) hdiff'

end AddValuation
