/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Polynomial.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree

/-!
# Hensel lifting and irreducible reduction over the 5-adic integers

Modulo the maximal ideal of `ℤ_[5]`, the polynomial `X² - 6` factors as `(X - 1)(X + 1)`.
The factors are coprime because their roots are distinct in the residue field `ZMod 5`.
We apply coprime Hensel lifting and retain both the factorization over `ℤ_[5]` and the prescribed
reductions. A zero-ring example also exercises completeness for the top ideal.

Mathlib's p-adic residue-field equivalence and adic-completeness instance supply the coefficient
ring infrastructure; the factorization is obtained from the general theorem, not supplied in
advance over `ℤ_[5]`.

Independently, `X² - 5` is irreducible over `ℚ_[5]`: a square root would have an integer
valuation whose double is 1. Mathlib's monic-map lemma gives irreducibility over `ℤ_[5]`.
Its reduction is `X²`, a nonirreducible positive power of the monic irreducible `X`.
These model proofs do not use the general irreducible-reduction theorem. A subsequent
application obtains a monic irreducible power from that theorem, while a linear example
also exhibits exponent 1.
-/

public section

noncomputable section

open Polynomial

namespace AdicModulesTest.Polynomial.Hensel

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

local notation "I₅" => IsLocalRing.maximalIdeal ℤ_[5]
local notation "F₅" => ℤ_[5] ⧸ I₅

private lemma six_eq_one : (6 : F₅) = 1 := by
  apply (PadicInt.residueField (p := 5)).injective
  calc
    _ = (6 : ZMod 5) := map_ofNat (PadicInt.residueField (p := 5)) 6
    _ = 1 := by decide
    _ = _ := (map_one (PadicInt.residueField (p := 5))).symm

private lemma residue_coprime : IsCoprime (X - C (1 : F₅)) (X + C (1 : F₅)) := by
  have hfive : (5 : F₅) = 0 := by
    calc
      5 = (6 : F₅) - 1 := by ring
      _ = 0 := by rw [six_eq_one, sub_self]
  refine ⟨C 2, C 3, ?_⟩
  calc
    _ = C (5 : F₅) * X + 1 := by simp only [C_ofNat, C_1]; ring
    _ = 1 := by rw [hfive, C_0, zero_mul, zero_add]

private lemma residue_factorization :
    (X ^ 2 - C (6 : ℤ_[5])).map (Ideal.Quotient.mk I₅) =
      (X - C (1 : F₅)) * (X + C (1 : F₅)) := by
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    map_ofNat, six_eq_one]
  simp only [C_1]
  ring

/-- The two distinct residue factors of `X² - 6` lift to coprime monic factors over `ℤ_[5]`,
with reductions `X - 1` and `X + 1` modulo the maximal ideal. -/
theorem padicInt_five_X_sq_sub_six :
    ∃ g h : ℤ_[5][X], g.Monic ∧ h.Monic ∧ IsCoprime g h ∧
      X ^ 2 - C (6 : ℤ_[5]) = g * h ∧
      g.map (Ideal.Quotient.mk I₅) = X - C (1 : F₅) ∧
      h.map (Ideal.Quotient.mk I₅) = X + C (1 : F₅) := by
  exact Polynomial.exists_monic_factorization_of_isAdicComplete I₅
    (monic_X_pow_sub_C _ (by decide)) (monic_X_sub_C _) (monic_X_add_C _)
    residue_coprime residue_factorization

-- Completeness for the top ideal is possible for a zero ring; monicity is not nonzeroness there.
private theorem zmod_one_factorization : ∃ g h : (ZMod 1)[X], g.Monic ∧ h.Monic ∧ IsCoprime g h ∧
    (0 : (ZMod 1)[X]) = g * h ∧
    g.map (Ideal.Quotient.mk (⊤ : Ideal (ZMod 1))) = 0 ∧
    h.map (Ideal.Quotient.mk (⊤ : Ideal (ZMod 1))) = 0 := by
  exact Polynomial.exists_monic_factorization_of_isAdicComplete ⊤
    (monic_zero_iff_subsingleton.mpr inferInstance)
    (monic_zero_iff_subsingleton.mpr inferInstance)
    (monic_zero_iff_subsingleton.mpr inferInstance)
    ⟨0, 0, Subsingleton.elim _ _⟩
    (Subsingleton.elim _ _)

/-- The polynomial `X² - 5` is irreducible over `ℚ₅`, since the valuation of a square is even. -/
theorem padic_five_X_sq_sub_five_irreducible :
    Irreducible (X ^ 2 - C (5 : ℚ_[5])) := by
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro b hb
  have h := congrArg Padic.valuation hb
  rw [Padic.valuation_pow,
    show (5 : ℚ_[5]) = ((5 : ℕ) : ℚ_[5]) by rfl, Padic.valuation_p] at h
  norm_num at h
  omega

/-- Monicity and irreducibility over `ℚ₅` give irreducibility of `X² - 5` over `ℤ₅`. -/
theorem padicInt_five_X_sq_sub_five_irreducible :
    Irreducible (X ^ 2 - C (5 : ℤ_[5])) := by
  refine Monic.irreducible_of_irreducible_map (algebraMap ℤ_[5] ℚ_[5])
    (X ^ 2 - C (5 : ℤ_[5])) (monic_X_pow_sub_C _ (by decide)) ?_
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  exact padic_five_X_sq_sub_five_irreducible

private lemma five_eq_zero : (5 : F₅) = 0 := by
  apply (PadicInt.residueField (p := 5)).injective
  calc
    _ = (5 : ZMod 5) := map_ofNat (PadicInt.residueField (p := 5)) 5
    _ = 0 := by decide
    _ = _ := (map_zero (PadicInt.residueField (p := 5))).symm

-- The maximal-ideal and adic-completeness hypotheses are supplied by Mathlib, not assumed.
private theorem padicInt_five_maximalIdeal_isMaximal : Ideal.IsMaximal I₅ := inferInstance
private theorem padicInt_five_isAdicComplete_maximalIdeal : IsAdicComplete I₅ ℤ_[5] := inferInstance

/-- Independently of irreducible-reduction lifting, the reduction of `X² - 5` is `X²`, with
monic irreducible base `X` and positive exponent 2. In particular it is not irreducible. -/
theorem padicInt_five_X_sq_sub_five_reduction :
    (X ^ 2 - C (5 : ℤ_[5])).Monic ∧
      (X : F₅[X]).Monic ∧ Irreducible (X : F₅[X]) ∧ 0 < (2 : ℕ) ∧
      (X ^ 2 - C (5 : ℤ_[5])).map (Ideal.Quotient.mk I₅) = (X : F₅[X]) ^ 2 ∧
      ¬ Irreducible ((X ^ 2 - C (5 : ℤ_[5])).map (Ideal.Quotient.mk I₅)) := by
  have hred : (X ^ 2 - C (5 : ℤ_[5])).map (Ideal.Quotient.mk I₅) =
      (X : F₅[X]) ^ 2 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      map_ofNat, five_eq_zero, C_0, sub_zero]
  refine ⟨monic_X_pow_sub_C _ (by decide), monic_X, irreducible_X, by decide, hred, ?_⟩
  rw [hred]
  exact not_irreducible_pow (by decide)

/-- Applying irreducible reduction to `X² - 5` over `ℤ₅`. This application uses the general
statement; the explicit exponent-2 reduction and irreducibility hypotheses are proved above. -/
theorem padicInt_five_X_sq_sub_five_irreducible_reduction :
    ∃ (q : F₅[X]) (e : ℕ), q.Monic ∧ Irreducible q ∧ 0 < e ∧
      (X ^ 2 - C (5 : ℤ_[5])).map (Ideal.Quotient.mk I₅) = q ^ e := by
  exact Polynomial.exists_monic_irreducible_pow_of_isAdicComplete I₅
    (monic_X_pow_sub_C _ (by decide)) padicInt_five_X_sq_sub_five_irreducible

-- A linear irreducible has an irreducible reduction: exponent 1 is also possible.
private theorem padicInt_five_X_reduction_one : (X : ℤ_[5][X]).Monic ∧ Irreducible (X : ℤ_[5][X]) ∧
    (X : F₅[X]).Monic ∧ Irreducible (X : F₅[X]) ∧
    (X : ℤ_[5][X]).map (Ideal.Quotient.mk I₅) = (X : F₅[X]) ^ 1 := by
  exact ⟨monic_X, irreducible_X, monic_X, irreducible_X, by simp⟩

-- Global factor lifting over `ℤ₅` follows from adic completeness, independently of
-- irreducible reduction. Only the output coprimality of the complete-ring theorem is discarded.
private theorem padicInt_five_monic_factorization :
    ∀ (F : ℤ_[5][X]) (g₀ h₀ : F₅[X]),
      F.Monic → g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ →
      F.map (Ideal.Quotient.mk I₅) = g₀ * h₀ →
      ∃ g h : ℤ_[5][X], g.Monic ∧ h.Monic ∧ F = g * h ∧
        g.map (Ideal.Quotient.mk I₅) = g₀ ∧
        h.map (Ideal.Quotient.mk I₅) = h₀ := by
  intro F g₀ h₀ hF hg₀ hh₀ hcop hfac
  obtain ⟨g, h, hgm, hhm, _, hgh, hg, hh⟩ :=
    Polynomial.exists_monic_factorization_of_isAdicComplete I₅ hF hg₀ hh₀ hcop hfac
  exact ⟨g, h, hgm, hhm, hgh, hg, hh⟩

-- Apply the global factor-lifting criterion to the same ramified polynomial.
private theorem padicInt_five_X_sq_sub_five_irreducible_reduction_of_monic_factorization :
    ∃ (q : F₅[X]) (e : ℕ), q.Monic ∧ Irreducible q ∧ 0 < e ∧
      (X ^ 2 - C (5 : ℤ_[5])).map (Ideal.Quotient.mk I₅) = q ^ e := by
  exact Polynomial.exists_monic_irreducible_pow_of_monic_factorization I₅
    padicInt_five_monic_factorization (monic_X_pow_sub_C _ (by decide))
    padicInt_five_X_sq_sub_five_irreducible

-- The class is constructed from the independent global family, not inferred from completeness.
private theorem padicInt_five_henselian_of_monic_factorization : HenselianRing ℤ_[5] I₅ :=
  HenselianRing.of_monic_factorization I₅ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    padicInt_five_monic_factorization

/-- The class obtained from global factor lifting supplies a root of `X² - 6` congruent to 1.
The evaluation error and unit residue derivative are checked independently of the root. -/
theorem padicInt_five_X_sq_sub_six_root_of_monic_factorization :
    ∃ a : ℤ_[5], (X ^ 2 - C (6 : ℤ_[5])).IsRoot a ∧ a - 1 ∈ I₅ := by
  have herr : (X ^ 2 - C (6 : ℤ_[5])).eval 1 ∈ I₅ := by
    have heval : (X ^ 2 - C (6 : ℤ_[5])).eval 1 = -(5 : ℤ_[5]) := by norm_num
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [heval, map_neg, map_ofNat, five_eq_zero, neg_zero]
  have hd : (X ^ 2 - C (6 : ℤ_[5])).derivative.eval 1 = 2 := by norm_num
  have hder : IsUnit (Ideal.Quotient.mk I₅
      ((X ^ 2 - C (6 : ℤ_[5])).derivative.eval 1)) := by
    rw [hd, map_ofNat]
    refine isUnit_iff_exists_inv.mpr ⟨(3 : F₅), ?_⟩
    calc
      (2 : F₅) * 3 = 5 + 1 := by ring
      _ = 1 := by rw [five_eq_zero, zero_add]
  exact @HenselianRing.is_henselian ℤ_[5] _ I₅
    padicInt_five_henselian_of_monic_factorization (X ^ 2 - C (6 : ℤ_[5]))
    (monic_X_pow_sub_C _ (by decide)) 1 herr hder

-- At the top ideal the quotient is zero and the global family is trivial (use F and 1),
-- but a nontrivial ring cannot satisfy the Jacobson field of the Henselian class.
private theorem zmod_two_not_henselian_top : ¬ HenselianRing (ZMod 2) ⊤ := by
  intro h
  have hj : Ideal.jacobson (⊥ : Ideal (ZMod 2)) = ⊤ := eq_top_iff.mpr h.jac
  exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp hj)

-- The simple-root class is obtained from the canonical maximal-ideal completion instance.
local instance : HenselianLocalRing ℤ_[5] := HenselianRing.toHenselianLocalRing ℤ_[5]

private lemma nonmonic_simple_root_data :
    (5 : ℤ_[5]) ≠ 0 ∧ (5 : ℤ_[5]) ∈ I₅ ∧
      ¬ IsUnit (C (5 : ℤ_[5]) * X ^ 2 + X + C 5).leadingCoeff := by
  have hne : (5 : ℤ_[5]) ≠ 0 := by norm_num
  have hmem : (5 : ℤ_[5]) ∈ I₅ := Ideal.Quotient.eq_zero_iff_mem.mp (by
    simpa only [map_ofNat] using five_eq_zero)
  have hdegree : (C (5 : ℤ_[5]) * X ^ 2 + X + C 5).natDegree = 2 := by
    compute_degree!
  have hlc : (C (5 : ℤ_[5]) * X ^ 2 + X + C 5).leadingCoeff = 5 := by
    rw [leadingCoeff, hdegree]
    simp [coeff_X]
  refine ⟨hne, hmem, ?_⟩
  rw [hlc, ← IsLocalRing.residue_ne_zero_iff_isUnit]
  exact not_not.mpr ((IsLocalRing.residue_eq_zero_iff _).mpr hmem)

/-- The nonmonic polynomial `5X² + X + 5` has a root congruent to zero in `ℤ₅`.
Its initial error is nonzero and its leading coefficient is a nonunit, so the monic
simple-root theorem does not apply directly. -/
theorem padicInt_five_nonmonic_simple_root :
    ¬ IsUnit (C (5 : ℤ_[5]) * X ^ 2 + X + C 5).leadingCoeff ∧
      (C (5 : ℤ_[5]) * X ^ 2 + X + C 5).eval 0 ≠ 0 ∧
      ∃ b : ℤ_[5], (C (5 : ℤ_[5]) * X ^ 2 + X + C 5).eval b = 0 ∧
        IsLocalRing.residue ℤ_[5] b = 0 := by
  obtain ⟨hne, hmem, hlc⟩ := nonmonic_simple_root_data
  have heval : (C (5 : ℤ_[5]) * X ^ 2 + X + C 5).eval 0 = 5 := by simp
  refine ⟨hlc, by rwa [heval], ?_⟩
  obtain ⟨b, hb, hbr⟩ := HenselianLocalRing.exists_root_residue
    (C (5 : ℤ_[5]) * X ^ 2 + X + C 5) 0 (by rwa [heval]) (by simp)
  exact ⟨b, hb, by simpa only [map_zero] using hbr⟩

end AdicModulesTest.Polynomial.Hensel
