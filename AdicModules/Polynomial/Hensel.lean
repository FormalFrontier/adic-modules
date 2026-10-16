/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.Ring

/-!
# Hensel factor lifting and irreducible reduction

For a Henselian local ring, a simple root modulo the maximal ideal lifts for every polynomial,
not only for a monic polynomial. A reciprocal-polynomial substitution reduces to Mathlib's
monic simple-root theorem, using its Taylor expansion and coefficient-reflection API. This
argument inverts only units and works in the presence of zero divisors. The all-polynomial
criterion is equivalent to the stock monic definition of `HenselianLocalRing`.

A coprime monic factorization modulo an ideal lifts to a coprime monic factorization over
any commutative ring complete and separated for that ideal. The factors have their prescribed
reductions. No local-ring, Noetherian, finite-generation or proper-ideal hypothesis is needed.

The proof uses Mathlib's universal coprime factorization ring, which is étale, and the lifting
property of formally smooth algebras over adically complete rings. These constructions are due
to Andrew Yang and to Judith Ludwig and Christian Merten, respectively.

## Implementation notes

For a proper ideal, monicity preserves degrees on reduction, so the universal ring can be used
with the degrees of the given factors. Completeness for the top ideal forces the coefficient
ring to be a subsingleton; this case is treated separately. We do not assert uniqueness of the
lifts or construct a chosen factorization.

For any commutative ring and maximal ideal, a global monic factor-lifting property implies
that every monic irreducible polynomial reduces to a positive power of a monic irreducible
polynomial. The property quantifies over all monic polynomials, including reducible ones,
and asks that coprime monic residue factors lift with both prescribed reductions. The proof
extracts the largest power of one normalized irreducible factor. Its coprime complement lifts,
so irreducibility forces that complement to be 1. This argument allows zero divisors and
requires neither locality nor completeness; the adically complete result is a corollary.

The global input is the source's factor-lifting property in quotient form, not a new class
or an asserted equivalence with Mathlib's simple-root `HenselianRing` or `HenselianLocalRing`
classes. For a valuation domain with fraction field `F`, Mathlib's
`Polynomial.Monic.irreducible_of_irreducible_map` supplies integer-polynomial irreducibility
from field irreducibility. Compare the Henselian valuation-field formulation in Exercise 4;
no whole-source coverage is asserted.

For an ideal contained in the Jacobson radical, the same global factor-lifting family
constructs `HenselianRing R I`. A simple residue root gives a monic linear factor coprime
to its complement; its monic lift still has degree one and supplies the required root.
The Jacobson-containment hypothesis supplies the other field of Mathlib's class. It cannot
be replaced by properness: a product of two algebraically closed fields has the global
factor-lifting property at the kernel of either projection, but this ideal is not contained
in the Jacobson radical. No converse or equivalence is asserted.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  AMS, 2002, Chapter II, §1, Corollary 1 (coprime Hensel lifting over complete discrete
  valuation rings). The theorem here is stated for arbitrary adically complete rings.
* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  AMS, 2002, Chapter II, §1, Exercise 4, p. 38 (irreducible reduction over Henselian
  valuation fields).
* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  AMS, 2002, Chapter II, §1, Corollary 2, p. 37 (the factor-to-simple-root argument).
  The construction here applies to arbitrary commutative rings and ideals contained
  in the Jacobson radical. Mathlib's Henselian classes were formalized by Johan Commelin.
* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  AMS, 2002, Chapter II, §1, Corollary 3, p. 37 (small-error root lifting for monic
  polynomials over complete discrete valuation rings). The ideal-theoretic root estimate
  below extends this to arbitrary polynomials over Henselian pairs. Corollary 4 applies
  the root estimate to neighborhoods of powers.
* Mathlib's `Polynomial.UniversalCoprimeFactorizationRing.homEquiv` and
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`.
* Mathlib's monic Hensel formalization by Johan Commelin, and its polynomial Taylor expansion
  and reflection API. The reciprocal-polynomial reduction is due to Formal Frontier Agents.
-/

@[expose] public section

universe u

namespace Polynomial

/-- Coprime monic factors modulo `I` lift to coprime monic factors over an `I`-adically
complete commutative ring, with the prescribed reductions. This is the coprime factor form
of Hensel's lemma; compare Fesenko–Vostokov, *Local Fields and Their Extensions*, II, §1,
Corollary 1 for complete discrete valuation rings. The proof uses Mathlib's étale universal
coprime factorization ring and formally smooth lifting over adically complete rings. -/
theorem exists_monic_factorization_of_isAdicComplete
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {f : R[X]} {g₀ h₀ : (R ⧸ I)[X]}
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hfac : f.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃ g h : R[X], g.Monic ∧ h.Monic ∧ IsCoprime g h ∧ f = g * h ∧
      g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀ := by
  classical
  by_cases hI : I = ⊤
  · subst I
    have : Subsingleton R :=
      IsAdicComplete.subsingleton (R := R) R (inferInstance : IsAdicComplete (⊤ : Ideal R) R)
    exact ⟨1, 1, monic_one, monic_one, isCoprime_one_left,
      Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hn : f.natDegree = g₀.natDegree + h₀.natDegree := by
    simpa only [hf.natDegree_map, hg₀.natDegree_mul hh₀] using congrArg natDegree hfac
  let p : MonicDegreeEq R f.natDegree := .mk f hf rfl
  let q₀ : {q : MonicDegreeEq (R ⧸ I) g₀.natDegree × MonicDegreeEq (R ⧸ I) h₀.natDegree //
      q.1.1 * q.2.1 = p.1.map (algebraMap R (R ⧸ I)) ∧ IsCoprime q.1.1 q.2.1} :=
    ⟨(.mk g₀ hg₀ rfl, .mk h₀ hh₀ rfl), hfac.symm, hcop⟩
  let φ := (UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I)
    g₀.natDegree h₀.natDegree hn p).symm q₀
  obtain ⟨ψ, hψ⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete φ
  let q := UniversalCoprimeFactorizationRing.homEquiv R g₀.natDegree h₀.natDegree hn p ψ
  have hφ : UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I)
      g₀.natDegree h₀.natDegree hn p φ = q₀ := Equiv.apply_symm_apply _ _
  have hg := UniversalCoprimeFactorizationRing.homEquiv_comp_fst
    R g₀.natDegree h₀.natDegree hn p ψ (Ideal.Quotient.mkₐ R I)
  have hh := UniversalCoprimeFactorizationRing.homEquiv_comp_snd
    R g₀.natDegree h₀.natDegree hn p ψ (Ideal.Quotient.mkₐ R I)
  rw [hψ, hφ] at hg hh
  refine ⟨q.1.1.1, q.1.2.1, q.1.1.monic, q.1.2.monic, q.2.2, ?_, ?_, ?_⟩
  · simpa only [Algebra.algebraMap_self, Polynomial.map_id, p, MonicDegreeEq.mk_coe]
      using q.2.1.symm
  · exact congrArg Subtype.val hg.symm
  · exact congrArg Subtype.val hh.symm

/-- If every coprime monic factorization modulo a maximal ideal `I` lifts to monic factors
with both prescribed reductions, then every monic irreducible polynomial reduces to a positive
power of a single monic irreducible polynomial. The lifting hypothesis ranges over all monic
polynomials in `R[X]`, including reducible ones; it does not require coprimality of the lifts.
No domain, local-ring, completeness, Noetherian or residue-field finiteness hypothesis is imposed.

Compare Fesenko–Vostokov, *Local Fields and Their Extensions*, II, §1, Exercise 4, p. 38,
whose Henselian valuation fields satisfy this global monic factor-lifting property. The
adically complete case is supplied by `exists_monic_factorization_of_isAdicComplete`, using
Mathlib's universal coprime factorization ring and formally smooth lifting. -/
theorem exists_monic_irreducible_pow_of_monic_factorization
    {R : Type u} [CommRing R] (I : Ideal R) [I.IsMaximal]
    (hLift : ∀ (F : R[X]) (g₀ h₀ : (R ⧸ I)[X]),
      F.Monic → g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ →
      F.map (Ideal.Quotient.mk I) = g₀ * h₀ →
      ∃ g h : R[X], g.Monic ∧ h.Monic ∧ F = g * h ∧
        g.map (Ideal.Quotient.mk I) = g₀ ∧
        h.map (Ideal.Quotient.mk I) = h₀)
    {f : R[X]} (hf : f.Monic) (hirr : Irreducible f) :
    ∃ (q : (R ⧸ I)[X]) (e : ℕ), q.Monic ∧ Irreducible q ∧ 0 < e ∧
      f.map (Ideal.Quotient.mk I) = q ^ e := by
  classical
  let := Ideal.Quotient.field I
  let F := f.map (Ideal.Quotient.mk I)
  have hF : F.Monic := hf.map _
  have hFu : ¬ IsUnit F := not_isUnit_of_natDegree_pos F (by
    simpa only [F, hf.natDegree_map] using hf.natDegree_pos_of_not_isUnit hirr.not_isUnit)
  obtain ⟨q, hq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hF.ne_zero hFu
  obtain ⟨hqi, hqm, hqd⟩ := (Polynomial.mem_normalizedFactors_iff hF.ne_zero).mp hq
  -- Separate the largest power of this irreducible from its coprime complement.
  obtain ⟨e, a, hqa, hfac⟩ := WfDvdMonoid.max_power_factor hF.ne_zero hqi
  have he : 0 < e := by
    by_contra h
    have he0 : e = 0 := Nat.eq_zero_of_not_pos h
    exact hqa (by simpa [hfac, he0] using hqd)
  have ham : a.Monic := (hqm.pow e).of_mul_monic_left (hfac ▸ hF)
  obtain ⟨g, h, hgm, hhm, hgh, hg, hh⟩ :=
    hLift f (q ^ e) a hf (hqm.pow e) ham
      ((hqi.coprime_iff_not_dvd.mpr hqa).pow_left) hfac
  -- The lift of the positive power cannot be a unit, so the other lift is 1.
  have ha : a = 1 := by
    rcases hirr.isUnit_or_isUnit hgh with hgu | hhu
    · have hqpow : q ^ e = 1 := by
        rw [← hg, hgm.eq_one_of_isUnit hgu, Polynomial.map_one]
      exact (hqi.not_isUnit (isUnit_of_dvd_one (hqpow ▸ dvd_pow_self q he.ne'))).elim
    · rw [← hh, hhm.eq_one_of_isUnit hhu, Polynomial.map_one]
  exact ⟨q, e, hqm, hqi, he, by simpa [ha] using hfac⟩

/-- A monic irreducible polynomial over a commutative ring complete for a maximal ideal
reduces to a positive power of a single monic irreducible polynomial. No domain, Noetherian
or residue-field finiteness hypothesis is imposed on the coefficient ring.

Compare Fesenko–Vostokov, *Local Fields and Their Extensions*, II, §1, Exercise 4, p. 38:
the source assumes a Henselian valuation field and irreducibility over that field. Here the
coefficient ring need not be a valuation ring, but is assumed adically complete. In the
complete discretely valued case, the source's field irreducibility supplies coefficient-ring
irreducibility through Mathlib's `Polynomial.Monic.irreducible_of_irreducible_map`.
The reduction need not itself be irreducible. -/
theorem exists_monic_irreducible_pow_of_isAdicComplete
    {R : Type u} [CommRing R] (I : Ideal R) [I.IsMaximal] [IsAdicComplete I R]
    {f : R[X]} (hf : f.Monic) (hirr : Irreducible f) :
    ∃ (q : (R ⧸ I)[X]) (e : ℕ), q.Monic ∧ Irreducible q ∧ 0 < e ∧
      f.map (Ideal.Quotient.mk I) = q ^ e := by
  apply exists_monic_irreducible_pow_of_monic_factorization I ?_ hf hirr
  intro F g₀ h₀ hF hg₀ hh₀ hcop hfac
  obtain ⟨g, h, hgm, hhm, _, hgh, hg, hh⟩ :=
    exists_monic_factorization_of_isAdicComplete I hF hg₀ hh₀ hcop hfac
  exact ⟨g, h, hgm, hhm, hgh, hg, hh⟩

end Polynomial

namespace HenselianRing

open Polynomial

/-- An ideal contained in the Jacobson radical is Henselian if every coprime monic
factorization modulo that ideal lifts to monic factors with both prescribed reductions.
The lifting hypothesis ranges over all monic polynomials, including reducible ones, and
requires no coprimality of the lifts. No locality, completeness, domain or residue-field
hypothesis is needed. Properness follows from Jacobson containment when the ring is nontrivial;
the zero ring is also allowed.

The Jacobson-containment hypothesis is essential for Mathlib's class, independently of
simple-root lifting: it fails for the kernel of a projection from a product of two
algebraically closed fields, although the global factor-lifting family holds there.

The proof follows the factor-to-simple-root argument of Fesenko–Vostokov,
*Local Fields and Their Extensions*, II, §1, Corollary 2, p. 37, generalized beyond
valued fields. It uses Mathlib's polynomial division and monic-degree APIs and the
Henselian class formalized by Johan Commelin. This is a non-instance constructor. -/
theorem of_monic_factorization
    {R : Type u} [CommRing R] (I : Ideal R) (hjac : I ≤ Ideal.jacobson ⊥)
    (hLift : ∀ (F : R[X]) (g₀ h₀ : (R ⧸ I)[X]),
      F.Monic → g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ →
      F.map (Ideal.Quotient.mk I) = g₀ * h₀ →
      ∃ g h : R[X], g.Monic ∧ h.Monic ∧ F = g * h ∧
        g.map (Ideal.Quotient.mk I) = g₀ ∧
        h.map (Ideal.Quotient.mk I) = h₀) :
    HenselianRing R I := by
  classical
  refine ⟨hjac, ?_⟩
  intro f hf a₀ herr hder
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    exact ⟨a₀, Subsingleton.elim _ _, by simpa only [sub_self] using I.zero_mem⟩
  let := hR
  have hI : I ≠ ⊤ := by
    intro hI
    have hjtop : Ideal.jacobson (⊥ : Ideal R) = ⊤ := eq_top_iff.mpr (hI ▸ hjac)
    exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp hjtop)
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let π := Ideal.Quotient.mk I
  let a := π a₀
  let F := f.map π
  let H := F /ₘ (X - C a)
  have hroot : F.IsRoot a := by
    simpa only [IsRoot.def, F, a, eval_map_apply] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr herr)
  have hfac : F = (X - C a) * H := (mul_divByMonic_eq_iff_isRoot.mpr hroot).symm
  have hFm : F.Monic := hf.map π
  have hHm : H.Monic := (monic_X_sub_C a).of_mul_monic_left (hfac ▸ hFm)
  have hHeval : H.eval a = π (f.derivative.eval a₀) := by
    calc
      _ = F.derivative.eval a := by rw [hfac, derivative_mul]; simp
      _ = _ := by simp only [F, a, derivative_map, eval_map_apply]
  -- A unit value gives a Bezout identity over the quotient ring, not just over a field.
  have hcop : IsCoprime (X - C a) H := by
    obtain ⟨t, ht⟩ := X_sub_C_dvd_sub_C_eval (p := H) (a := a)
    obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp (hHeval.symm ▸ hder)
    refine ⟨-(C u * t), C u, ?_⟩
    calc
      _ = C u * H - C u * ((X - C a) * t) := by
        rw [neg_mul, mul_assoc, mul_comm t (X - C a), neg_add_eq_sub]
      _ = C u * (H - (X - C a) * t) := (mul_sub _ _ _).symm
      _ = C u * C (H.eval a) := by rw [← ht, sub_sub_cancel]
      _ = 1 := by rw [← C_mul, mul_comm u, hu, C_1]
  obtain ⟨g, h, hgm, _, hgh, hg, _⟩ :=
    hLift f (X - C a) H hf (monic_X_sub_C a) hHm hcop hfac
  have hgdeg : g.natDegree = 1 := by
    simpa only [hgm.natDegree_map, natDegree_X_sub_C] using congrArg natDegree hg
  have hgr : g.eval (-g.coeff 0) = 0 := by
    rw [hgm.eq_X_add_C hgdeg]
    simp
  have hcoeff : π (g.coeff 0) = -a := by
    simpa only [coeff_map, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] using
      congrArg (fun p => p.coeff 0) hg
  refine ⟨-g.coeff 0, ?_, ?_⟩
  · rw [IsRoot.def, hgh, eval_mul, hgr, zero_mul]
  · apply Ideal.Quotient.eq.mp
    change π (-g.coeff 0) = a
    rw [map_neg, hcoeff, neg_neg]

end HenselianRing

open Polynomial IsLocalRing

/-- Henselianity at the maximal ideal of a local ring gives the Henselian local-ring class.
This is the converse of Mathlib's instance from `HenselianLocalRing` to `HenselianRing`.
It is not an instance, so the two directions do not form a typeclass-search cycle. -/
theorem HenselianRing.toHenselianLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] : HenselianLocalRing R where
  is_henselian f hf a₀ h₀ h₁ :=
    HenselianRing.is_henselian f hf a₀ h₀ (h₁.map (residue R))

namespace HenselianRing

variable {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I]

-- Reciprocal substitution makes the equation monic without dividing by its constant term.
private theorem exists_root_of_constant_mem
    [Nontrivial R] (b : R) (q : R[X]) (hb : b ∈ I) (hu : IsUnit (q.coeff 0)) :
    ∃ c : R, (C b + X * q).IsRoot c ∧ c ∈ I := by
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I HenselianRing.jac
  let p := q.comp (C (-b) * X)
  let n := p.natDegree
  let g := X ^ (n + 1) - p.reflect n
  have hdeg : (p.reflect n).natDegree ≤ n := by
    simpa only [n, max_self] using (natDegree_reflect_le (N := n) (p := p))
  have hmonic : g.Monic := by
    apply monic_X_pow_sub
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hdeg))
  have hbm : Ideal.Quotient.mk I b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
  have hred : g.map (Ideal.Quotient.mk I) =
      (X - C (Ideal.Quotient.mk I (q.coeff 0))) * X ^ n := by
    calc
      g.map (Ideal.Quotient.mk I) = X ^ (n + 1) -
          (C (Ideal.Quotient.mk I (q.coeff 0))).reflect n := by
        simp [g, ← reflect_map, p, hbm, Polynomial.map_comp, ← coeff_zero_eq_eval_zero]
      _ = (X - C (Ideal.Quotient.mk I (q.coeff 0))) * X ^ n := by
        simp only [reflect_C, sub_mul, pow_succ']
  have hzero : g.eval (q.coeff 0) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← eval_map_apply, hred]
    simp
  have hderiv : IsUnit (Ideal.Quotient.mk I (g.derivative.eval (q.coeff 0))) := by
    rw [← eval_map_apply, ← derivative_map, hred]
    simpa [derivative_mul] using (hu.map (Ideal.Quotient.mk I)).pow n
  obtain ⟨y, hy, hym⟩ := HenselianRing.is_henselian g hmonic (q.coeff 0) hzero hderiv
  have hyres : Ideal.Quotient.mk I y = Ideal.Quotient.mk I (q.coeff 0) :=
    Ideal.Quotient.eq.mpr hym
  have hyunit : IsUnit y := IsUnit.of_map (Ideal.Quotient.mk I) y (by
    rw [hyres]
    exact hu.map (Ideal.Quotient.mk I))
  obtain ⟨y, rfl⟩ := hyunit
  have hreflect : p.eval (⅟(y : R)) * (y : R) ^ n = (p.reflect n).eval (y : R) := by
    simpa only [reflect_reflect, eval₂_id] using
      eval₂_reflect_mul_pow (RingHom.id R) (y : R) n (p.reflect n) hdeg
  have hq : q.eval (-b * ⅟(y : R)) = y := by
    apply ((y.isUnit).pow n).mul_left_inj.mp
    calc
      q.eval (-b * ⅟(y : R)) * (y : R) ^ n =
          p.eval (⅟(y : R)) * (y : R) ^ n := by simp [p, eval_comp]
      _ = (p.reflect n).eval (y : R) := hreflect
      _ = (y : R) ^ (n + 1) := by
        exact (sub_eq_zero.mp (by simpa only [g, IsRoot, eval_sub, eval_pow, eval_X] using hy)).symm
      _ = (y : R) * (y : R) ^ n := pow_succ' _ _
  refine ⟨-b * ⅟(y : R), ?_, I.mul_mem_right _ (I.neg_mem hb)⟩
  change (C b + X * q).eval (-b * ⅟(y : R)) = 0
  simp only [eval_add, eval_C, eval_mul, eval_X, hq]
  rw [mul_assoc, invOf_mul_self, mul_one, add_neg_cancel]

/-- A simple root modulo a Henselian ideal lifts to a root of an arbitrary polynomial.
The derivative need only be a unit modulo the ideal. Monicity, locality, completeness
and the absence of zero divisors are not required; the zero ring is allowed.

This generalizes the root-existence and congruence assertion of Fesenko and Vostokov,
*Local Fields and Their Extensions*, Chapter II, §1, Corollary 2, p. 37, from monic
polynomials over valuation rings of Henselian fields to arbitrary polynomials over Henselian
pairs.
The lifted root is simple in the source's field setting by derivative congruence. -/
theorem exists_root (f : R[X]) (a₀ : R)
    (h₀ : f.eval a₀ ∈ I)
    (h₁ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    exact ⟨a₀, Subsingleton.elim _ _, by simpa only [sub_self] using I.zero_mem⟩
  let := hR
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I HenselianRing.jac
  let F := f.taylor a₀
  obtain ⟨c, hc, hcm⟩ := exists_root_of_constant_mem I (f.eval a₀) F.divX h₀
    (by simpa only [coeff_divX, zero_add, F, taylor_coeff_one] using
      IsUnit.of_map (Ideal.Quotient.mk I) _ h₁)
  have hF : C (f.eval a₀) + X * F.divX = F := by
    rw [add_comm, ← taylor_coeff_zero a₀ f]
    exact X_mul_divX_add F
  refine ⟨c + a₀, ?_, by simpa only [add_sub_cancel_right] using hcm⟩
  simpa only [hF, IsRoot, F, taylor_eval] using hc

/-- If the evaluation error lies in the square of the derivative times a Henselian ideal,
there is a root whose displacement lies in the derivative times that ideal. The error
and the derivative times the displacement differ by a unit factor.

The derivative may be zero, a zero divisor or a nonunit. No cancellation, locality,
domain or completeness hypothesis is imposed, and the zero ring is allowed.

This is an ideal-theoretic strengthening of Fesenko and Vostokov,
*Local Fields and Their Extensions*, Chapter II, §1, Corollary 3, p. 37: the source treats
monic polynomials over complete discrete valuation rings, whereas this statement treats
arbitrary polynomials over Henselian pairs. The association, not displacement membership
alone, recovers the source's power-ideal precision. -/
theorem exists_root_of_eval_mem_span_derivative_sq_mul (f : R[X]) (a : R)
    (h : f.eval a ∈ Ideal.span {f.derivative.eval a ^ 2} * I) :
    ∃ b : R, f.IsRoot b ∧ b - a ∈ Ideal.span {f.derivative.eval a} * I ∧
      Associated (f.eval a) (f.derivative.eval a * (b - a)) := by
  let d := f.derivative.eval a
  obtain ⟨c, hc, hdc⟩ := Ideal.mem_span_singleton_mul.mp h
  change d ^ 2 * c = f.eval a at hdc
  let F := f.taylor a
  let H := F.divX.divX
  have hdiv : F.divX = X * H + C d := by
    have hcoeff : F.divX.coeff 0 = d := by
      simp only [coeff_divX, zero_add, F, taylor_coeff_one, d]
    simpa only [H, hcoeff] using (X_mul_divX_add F.divX).symm
  have hF : F = C (f.eval a) + C d * X + X ^ 2 * H := by
    calc
      F = X * F.divX + C (F.coeff 0) := (X_mul_divX_add F).symm
      _ = C (f.eval a) + C d * X + X ^ 2 * H := by
        rw [hdiv, show F.coeff 0 = f.eval a from taylor_coeff_zero a f]
        ring
  -- Normalize the equation without cancelling either d or d².
  let Q := C c + X + X ^ 2 * H.comp (C d * X)
  have heval (x : R) : f.eval (a + d * x) = d ^ 2 * Q.eval x := by
    calc
      f.eval (a + d * x) = F.eval (d * x) := by
        rw [taylor_eval, add_comm]
      _ = d ^ 2 * Q.eval x := by
        rw [hF]
        simp only [eval_add, eval_C, eval_mul, eval_X, eval_pow]
        rw [← hdc]
        simp only [Q, eval_add, eval_C, eval_mul, eval_X, eval_pow, eval_comp]
        ring
  obtain ⟨y, hy, hym⟩ := exists_root I Q 0
    (by simpa [Q] using hc)
    (by simp [Q, derivative_add, derivative_mul, derivative_pow])
  have hyI : y ∈ I := by simpa only [sub_zero] using hym
  have hyeq : c + y + y ^ 2 * H.eval (d * y) = 0 := by
    simpa only [Q, IsRoot, eval_add, eval_C, eval_mul, eval_X, eval_pow, eval_comp] using hy
  have hu : IsUnit (-(1 + y * H.eval (d * y))) := by
    have hj : y * H.eval (d * y) ∈ Ideal.jacobson (⊥ : Ideal R) :=
      HenselianRing.jac (I.mul_mem_right _ hyI)
    have hunit : IsUnit (1 + y * H.eval (d * y)) := by
      simpa only [mul_one, add_comm] using (Ideal.mem_jacobson_bot.mp hj) 1
    exact hunit.neg
  have hcy : c = y * (-(1 + y * H.eval (d * y))) := by
    calc
      c = c - (c + y + y ^ 2 * H.eval (d * y)) := by rw [hyeq, sub_zero]
      _ = y * (-(1 + y * H.eval (d * y))) := by ring
  refine ⟨a + d * y, ?_, ?_, ?_⟩
  · change f.eval (a + d * y) = 0
    rw [heval, show Q.eval y = 0 from hy, mul_zero]
  · exact Ideal.mem_span_singleton_mul.mpr
      ⟨y, hyI, by dsimp only [d]; ring⟩
  · change Associated (f.eval a) (d * (a + d * y - a))
    have herr : f.eval a = (d * (a + d * y - a)) * (-(1 + y * H.eval (d * y))) := by
      rw [← hdc, hcy]
      ring
    rw [herr]
    exact associated_mul_unit_left _ _ hu

end HenselianRing

namespace HenselianLocalRing

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

/-- A simple root modulo the maximal ideal of a Henselian local ring lifts to a root of an
arbitrary polynomial. No monicity, domain or completeness hypothesis is required.

The proof reduces to Mathlib's monic Hensel lemma by a reciprocal-polynomial substitution;
only units are inverted, so the coefficient ring may have zero divisors. -/
theorem exists_root (f : R[X]) (a₀ : R)
    (h₀ : f.eval a₀ ∈ maximalIdeal R) (h₁ : IsUnit (f.derivative.eval a₀)) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  exact HenselianRing.exists_root (maximalIdeal R) f a₀ h₀ (h₁.map (residue R))

/-- The residue-field form of simple-root lifting for an arbitrary polynomial over a
Henselian local ring. -/
theorem exists_root_residue (f : R[X]) (a₀ : R)
    (h₀ : f.eval a₀ ∈ maximalIdeal R) (h₁ : IsUnit (f.derivative.eval a₀)) :
    ∃ a : R, f.eval a = 0 ∧ residue R a = residue R a₀ := by
  obtain ⟨a, ha, ham⟩ := exists_root f a₀ h₀ h₁
  refine ⟨a, ha, ?_⟩
  simpa only [map_sub, sub_eq_zero] using (residue_eq_zero_iff _).mpr ham

end HenselianLocalRing

/-- Mathlib's monic simple-root definition of a Henselian local ring is equivalent to the
same criterion for all polynomials. In particular the general lifting theorem recovers the
monic endpoint used in the class definition. -/
theorem HenselianLocalRing.iff_exists_root
    (R : Type u) [CommRing R] [IsLocalRing R] :
    HenselianLocalRing R ↔
      ∀ (f : R[X]) (a₀ : R), f.eval a₀ ∈ maximalIdeal R →
        IsUnit (f.derivative.eval a₀) →
        ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  constructor
  · intro h
    let := h
    exact HenselianLocalRing.exists_root
  · intro h
    exact { is_henselian := fun f _ a₀ h₀ h₁ => h f a₀ h₀ h₁ }
