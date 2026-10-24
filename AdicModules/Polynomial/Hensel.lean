/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.Henselian
public import AdicModules.Polynomial.Coprime
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.Ring

/-!
# Hensel factor lifting, factor uniqueness and irreducible reduction

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
ring to be a subsingleton; this case is treated separately. The existence construction does
not choose a canonical factorization.

Separately, two already-existing factorizations have equal ordered factors if their left
factors are monic, have the same image under a scalar unit-reflecting coefficient map, and
the images of the first pair are Bézout coprime. The coefficient rings are arbitrary
commutative rings in independent universes, including zero rings. No right monicity, second
image equality, locality, Henselianity or completeness is needed for this uniqueness result.
Its proof uses the one-monic coprimeness criterion from `AdicModules.Polynomial.Coprime`,
monic divisibility and degree comparison, and monic regularity.

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
    (b : R) (q : R[X]) (hb : b ∈ I) (hu : IsUnit (q.coeff 0)) :
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


namespace Polynomial

/-- Two factorizations with monic left factors agree factor by factor if their left factors
have the same image under a unit-reflecting coefficient map and the images of the first pair
are coprime. Neither the right factors nor the common product is required to be monic. -/
theorem Monic.eq_factors_of_isCoprime_map
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) [IsLocalHom φ] {g h g' h' : R[X]}
    (hg : g.Monic) (hg' : g'.Monic) (hprod : g * h = g' * h')
    (hmap : g.map φ = g'.map φ) (hcoprime : IsCoprime (g.map φ) (h.map φ)) :
    g = g' ∧ h = h' := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · let := hS
    have hzero : IsUnit (0 : R) :=
      IsUnit.of_map φ 0 (isUnit_of_subsingleton _)
    let : Subsingleton R := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hzero)
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  let := hS
  have hcross : IsCoprime g' h := (hg'.isCoprime_map_iff (q := h) φ).mp (by
    rw [← hmap]
    exact hcoprime)
  have hdvd : g' ∣ g := hcross.dvd_of_dvd_mul_right ⟨h', hprod⟩
  have hdegree : g.natDegree = g'.natDegree := by
    simpa only [hg.natDegree_map, hg'.natDegree_map] using congrArg natDegree hmap
  have heq : g = g' :=
    eq_of_monic_of_dvd_of_natDegree_le hg' hg hdvd hdegree.le
  refine ⟨heq, hg.isRegular.left ?_⟩
  simpa only [heq] using hprod

end Polynomial

namespace HenselianRing

/-- The kernel of an augmentation of a module-finite algebra is finitely generated. -/
private theorem augmentation_ker_fg
    {k : Type*} {A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    [Module.Finite k A] (ρ : A →ₐ[k] k) : (RingHom.ker ρ).FG := by
  have hsplit : ρ.toLinearMap ∘ₗ Algebra.linearMap k A = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.linearMap_apply,
      AlgHom.commutes, Algebra.algebraMap_self_apply, LinearMap.id_apply]
  have hker : (RingHom.ker ρ).restrictScalars k = LinearMap.ker ρ.toLinearMap := by
    apply Submodule.ext
    intro x
    simp only [Submodule.restrictScalars_mem, RingHom.mem_ker, LinearMap.mem_ker,
      AlgHom.toLinearMap_apply]
  apply Submodule.FG.of_restrictScalars k
  rw [hker, LinearMap.ker_eq_range_of_comp_eq_id hsplit]
  exact Module.Finite.iff_fg.mp (Module.Finite.range _)

/-- Polynomial evaluation preserves the representation of an endomorphism on a finite family.
The convention is the column relation characterized by `Matrix.represents_iff'`. -/
private theorem matrix_represents_aeval
    {R N ι : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [Fintype ι] [DecidableEq ι] {v : ι → N}
    {A : Matrix ι ι R} {f : Module.End R N}
    (hA : A.Represents v f) (p : R[X]) :
    (Polynomial.aeval A p).Represents v (Polynomial.aeval f p) := by
  have hpow : ∀ n : ℕ, (A ^ n).Represents v (f ^ n) := by
    intro n
    induction n with
    | zero =>
        simpa only [pow_zero] using (Matrix.Represents.one (R := R) (b := v))
    | succ n hn =>
        simpa only [pow_succ] using hn.mul hA
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.aeval_add] using hp.add hq
  | monomial n r =>
      simpa only [Polynomial.aeval_monomial] using
        (Matrix.Represents.algebraMap (b := v) r).mul (hpow n)

/-- A matrix representing an endomorphism on a spanning family supplies its own
characteristic polynomial as an annihilating polynomial. The family need not be a basis. -/
private theorem aeval_charpoly_eq_zero_of_represents
    {R N ι : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [Fintype ι] [DecidableEq ι] {v : ι → N}
    (hv : Submodule.span R (Set.range v) = ⊤)
    {A : Matrix ι ι R} {f : Module.End R N} (hA : A.Represents v f) :
    Polynomial.aeval f A.charpoly = 0 := by
  have hchar := matrix_represents_aeval hA A.charpoly
  rw [Matrix.aeval_self_charpoly] at hchar
  exact Matrix.Represents.eq hv hchar Matrix.Represents.zero

/-- A supplied matrix reducing to the diagonal with entries `0, 1, …, 1` has a monic
characteristic polynomial with reduction `X * (X - 1) ^ s`. This also holds for zero rings. -/
private theorem charpoly_monic_and_map_eq_of_diagonal
    {R S : Type*} [CommRing R] [CommRing S] {s : ℕ}
    (M : Matrix (Fin (s + 1)) (Fin (s + 1)) R) (q : R →+* S)
    (hM : M.map q = Matrix.diagonal (fun j => if j = 0 then 0 else 1)) :
    M.charpoly.Monic ∧ M.charpoly.map q = X * (X - 1) ^ s := by
  refine ⟨Matrix.charpoly_monic M, ?_⟩
  rw [← Matrix.charpoly_map, hM, Matrix.charpoly_diagonal, Fin.prod_univ_succ]
  simp

/-- The scalar map on the quotient algebra is the induced quotient map. -/
private theorem residue_quotient_algebraMap
    {R : Type*} {B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R)
    (hIJ : I ≤ (I.map (algebraMap R B)).comap (algebraMap R B)) :
    @algebraMap (R ⧸ I) (B ⧸ I.map (algebraMap R B)) _ _
        (Ideal.Quotient.algebraQuotientOfLEComap hIJ) =
      Ideal.quotientMap (I.map (algebraMap R B)) (algebraMap R B) hIJ := by
  rfl

/-- The quotient algebra has the scalar tower induced by the original algebra. -/
private theorem residue_quotient_isScalarTower
    {R : Type*} {B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) :
    @IsScalarTower R (R ⧸ I) (B ⧸ I.map (algebraMap R B)) _
      (Ideal.Quotient.algebraQuotientOfLEComap
        (Ideal.le_comap_map :
          I ≤ (I.map (algebraMap R B)).comap (algebraMap R B))).toSMul _ := by
  let : Algebra (R ⧸ I) (B ⧸ I.map (algebraMap R B)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  apply IsScalarTower.of_algebraMap_eq
  intro r
  rw [residue_quotient_algebraMap I Ideal.le_comap_map,
    Ideal.Quotient.algebraMap_eq I, Ideal.quotientMap_mk]
  exact (Ideal.Quotient.mk_algebraMap R (I.map (algebraMap R B)) r).symm

/-- An augmentation to the residue ring descends to the quotient algebra. -/
private theorem residue_quotient_augmentation
    {R : Type*} {B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R)
    [Algebra (R ⧸ I) (B ⧸ I.map (algebraMap R B))]
    [IsScalarTower R (R ⧸ I) (B ⧸ I.map (algebraMap R B))]
    (ρ₀ : B →ₐ[R] R ⧸ I) :
    ∃ ρ : (B ⧸ I.map (algebraMap R B)) →ₐ[R ⧸ I] R ⧸ I,
      (ρ.restrictScalars R).comp
        (Ideal.Quotient.mkₐ R (I.map (algebraMap R B))) = ρ₀ := by
  have hker : I.map (algebraMap R B) ≤ RingHom.ker ρ₀.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change ρ₀ (algebraMap R B r) = 0
    rw [ρ₀.commutes, Ideal.Quotient.algebraMap_eq I]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  have hJ0 : ∀ b : B, b ∈ I.map (algebraMap R B) → ρ₀ b = 0 := by
    intro b hb
    exact RingHom.mem_ker.mp (hker hb)
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := by
    rw [Ideal.Quotient.algebraMap_eq I]
    exact Ideal.Quotient.mk_surjective
  refine ⟨AlgHom.extendScalarsOfSurjective hsurj
    (Ideal.Quotient.liftₐ (I.map (algebraMap R B)) ρ₀ hJ0), ?_⟩
  rw [AlgHom.restrictScalars_extendScalarsOfSurjective]
  exact Ideal.Quotient.liftₐ_comp (I.map (algebraMap R B)) ρ₀ hJ0

/-- Columnwise errors in the ideal multiple of a spanned module give a representing matrix
whose reduction has diagonal entries `0, 1, …, 1`. -/
private lemma exists_matrix_represents_map_diagonal
    {R : Type u} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
    {s : ℕ} (I : Ideal R) (v : Fin (s + 1) → N)
    (hv : Submodule.span R (Set.range v) = ⊤) (f : Module.End R N)
    (herr : ∀ j, f (v j) - (if j = 0 then 0 else v j) ∈ I • (⊤ : Submodule R N)) :
    ∃ M : Matrix (Fin (s + 1)) (Fin (s + 1)) R, M.Represents v f ∧
      M.map (Ideal.Quotient.mk I) = Matrix.diagonal (fun j => if j = 0 then 0 else 1) := by
  classical
  have hcoeff : ∀ j, ∃ a : Fin (s + 1) →₀ R, (∀ i, a i ∈ I) ∧
      (∑ i, a i • v i) = f (v j) - (if j = 0 then 0 else v j) := by
    intro j
    have hj : f (v j) - (if j = 0 then 0 else v j) ∈
        I • Submodule.span R (Set.range v) := by
      rw [hv]
      exact herr j
    obtain ⟨a, ha, haj⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum I v _).mp hj
    refine ⟨a, ha, ?_⟩
    exact (Finsupp.sum_fintype a (fun i c => c • v i)
      (fun i => zero_smul R (v i))).symm.trans haj
  choose a ha hsum using hcoeff
  refine ⟨fun i j => a j i +
    (Matrix.diagonal (fun k : Fin (s + 1) => if k = 0 then (0 : R) else 1)) i j, ?_, ?_⟩
  · apply Matrix.represents_iff'.2
    intro j
    have hd : (∑ i, (Matrix.diagonal
        (fun k : Fin (s + 1) => if k = 0 then (0 : R) else 1)) i j • v i) =
          (if j = 0 then 0 else v j) := by
      by_cases hj : j = 0 <;> simp [Matrix.diagonal_apply, ite_smul, hj]
    simp only [add_smul, Finset.sum_add_distrib, hsum j, hd, sub_add_cancel]
  · ext i j
    change Ideal.Quotient.mk I (a j i +
      (Matrix.diagonal (fun k : Fin (s + 1) => if k = 0 then (0 : R) else 1)) i j) =
        (Matrix.diagonal
          (fun k : Fin (s + 1) => if k = 0 then (0 : R ⧸ I) else 1)) i j
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (ha j i), zero_add]
    by_cases hij : i = j
    · subst i
      by_cases hj : j = 0 <;> simp [hj]
    · simp [hij]

/-- A scalar monic relation with residue `X * (X - 1) ^ s` lifts the complementary
idempotent component of an algebra element. -/
private lemma exists_isIdempotentElem_of_monic_annihilator
    {R : Type*} {B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) [HenselianRing R I] (s : ℕ) (P : R[X]) (hP : P.Monic)
    (hPbar : P.map (Ideal.Quotient.mk I) = X * (X - 1) ^ s)
    (b : B) (hb : aeval b P = 0)
    (hbbar : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R B)) b)) :
    ∃ e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk (I.map (algebraMap R B)) e =
        1 - Ideal.Quotient.mk (I.map (algebraMap R B)) b := by
  let J : Ideal B := I.map (algebraMap R B)
  let k := R ⧸ I
  let Bbar := B ⧸ J
  let q : R →+* k := Ideal.Quotient.mk I
  let beta : B →+* Bbar := Ideal.Quotient.mk J
  let : Algebra k Bbar :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower R k Bbar := residue_quotient_isScalarTower I
  have hsquare : (algebraMap k Bbar).comp q = beta.comp (algebraMap R B) := by
    change (algebraMap k Bbar).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk J).comp (algebraMap R B)
    rw [Ideal.Quotient.mk_comp_algebraMap, ← Ideal.Quotient.algebraMap_eq I,
      ← IsScalarTower.algebraMap_eq R k Bbar]
  have hscalar (r : R) :
      beta (algebraMap R B r) = algebraMap k Bbar (q r) :=
    (DFunLike.congr_fun hsquare r).symm
  have heval (F : R[X]) : beta (aeval b F) = aeval (beta b) (F.map q) :=
    Polynomial.map_aeval_eq_aeval_map hsquare F b
  cases s with
  | zero =>
      have hbzero : beta b = 0 := by
        have h := heval P
        rw [hb, map_zero, hPbar] at h
        simpa only [pow_zero, mul_one, aeval_X] using h.symm
      refine ⟨1, isIdempotentElem_iff.mpr (one_mul 1), ?_⟩
      change beta 1 = 1 - beta b
      rw [map_one, hbzero, sub_zero]
  | succ s =>
      have hPzero : q (P.eval 0) = 0 := by
        calc
          q (P.eval 0) = (P.map q).eval (q 0) :=
            (Polynomial.eval_map_apply (p := P) q 0).symm
          _ = 0 := by rw [hPbar]; simp
      have hderivzero : q (P.derivative.eval 0) = (-1 : k) ^ (s + 1) := by
        calc
          q (P.derivative.eval 0) = (P.derivative.map q).eval (q 0) :=
            (Polynomial.eval_map_apply (p := P.derivative) q 0).symm
          _ = (P.map q).derivative.eval 0 := by
            rw [Polynomial.derivative_map]
            simp only [map_zero]
          _ = (-1 : k) ^ (s + 1) := by
            rw [hPbar, Polynomial.derivative_mul]
            simp
      have hminus : IsUnit (-1 : k) :=
        isUnit_iff_exists_inv.mpr ⟨-1, by ring⟩
      have hsimple : IsUnit (q (P.derivative.eval 0)) := by
        rw [hderivzero]
        exact hminus.pow (s + 1)
      obtain ⟨a, ha, haI⟩ := HenselianRing.is_henselian (R := R) (I := I)
        P hP 0 (Ideal.Quotient.eq_zero_iff_mem.mp hPzero) hsimple
      have haq : q a = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [sub_zero] using haI)
      let Q : R[X] := P /ₘ (X - C a)
      have hfactor : (X - C a) * Q = P :=
        Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha
      have hQbar : Q.map q = (X - 1 : k[X]) ^ (s + 1) := by
        dsimp only [Q]
        rw [Polynomial.map_divByMonic q (Polynomial.monic_X_sub_C a)]
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
          haq, Polynomial.C_0, sub_zero]
        rw [hPbar]
        exact Polynomial.mul_divByMonic_cancel_left _ Polynomial.monic_X
      have hQderiv : Q.eval a = P.derivative.eval a := by
        rw [← hfactor, Polynomial.derivative_mul]
        simp
      have hQscalar : q (Q.eval a) = (-1 : k) ^ (s + 1) := by
        calc
          q (Q.eval a) = q (P.derivative.eval a) := congrArg q hQderiv
          _ = (P.derivative.map q).eval (q a) :=
            (Polynomial.eval_map_apply (p := P.derivative) q a).symm
          _ = (P.derivative.map q).eval (q 0) := by rw [haq, map_zero]
          _ = q (P.derivative.eval 0) :=
            Polynomial.eval_map_apply (p := P.derivative) q 0
          _ = (-1 : k) ^ (s + 1) := hderivzero
      let : IsLocalHom q :=
        isLocalHom_of_le_jacobson_bot I (HenselianRing.jac (R := R) (I := I))
      have hunit : IsUnit (Q.eval a) := by
        apply IsUnit.of_map q
        rw [hQscalar]
        exact hminus.pow (s + 1)
      obtain ⟨v, hv⟩ := hunit.exists_left_inv
      have hvB : algebraMap R B v * algebraMap R B (Q.eval a) = 1 := by
        rw [← map_mul, hv, map_one]
      have hann : (b - algebraMap R B a) * aeval b Q = 0 := by
        have h := congrArg (aeval b) hfactor
        simpa only [map_mul, map_sub, aeval_X, aeval_C, hb] using h
      obtain ⟨D, hD⟩ :=
        Polynomial.X_sub_C_dvd_sub_C_eval (p := Q) (a := a)
      have hdiff : aeval b Q - algebraMap R B (Q.eval a) =
          (b - algebraMap R B a) * aeval b D := by
        have h := congrArg (aeval b) hD
        simpa only [map_sub, map_mul, aeval_C, aeval_X] using h
      have hzero : (aeval b Q - algebraMap R B (Q.eval a)) * aeval b Q = 0 := by
        rw [hdiff]
        calc
          ((b - algebraMap R B a) * aeval b D) * aeval b Q =
              ((b - algebraMap R B a) * aeval b Q) * aeval b D := by ring
          _ = 0 := by rw [hann, zero_mul]
      have hsq : aeval b Q * aeval b Q = algebraMap R B (Q.eval a) * aeval b Q := by
        apply sub_eq_zero.mp
        simpa only [sub_mul] using hzero
      refine ⟨algebraMap R B v * aeval b Q, ?_, ?_⟩
      · apply isIdempotentElem_iff.mpr
        calc
          (algebraMap R B v * aeval b Q) * (algebraMap R B v * aeval b Q) =
              (algebraMap R B v * algebraMap R B v) * (aeval b Q * aeval b Q) := by
            ring
          _ = algebraMap R B v *
              (algebraMap R B v * algebraMap R B (Q.eval a)) * aeval b Q := by
            rw [hsq]
            ring
          _ = algebraMap R B v * aeval b Q := by rw [hvB, mul_one]
      · have hQb : beta (aeval b Q) = (beta b - 1) ^ (s + 1) := by
          rw [heval Q, hQbar]
          simp only [map_pow, map_sub, aeval_X, map_one]
        have hvbar : beta (algebraMap R B v) * (-1 : Bbar) ^ (s + 1) = 1 := by
          have h := congrArg beta hvB
          simpa only [map_mul, map_one, hscalar, hQscalar, map_pow, map_neg] using h
        have hpow : (beta b - 1) ^ (s + 1) =
            (-1 : Bbar) ^ (s + 1) * (1 - beta b) := by
          calc
            (beta b - 1) ^ (s + 1) = (-1 * (1 - beta b)) ^ (s + 1) := by
              congr 1
              ring
            _ = (-1 : Bbar) ^ (s + 1) * (1 - beta b) ^ (s + 1) := mul_pow _ _ _
            _ = (-1 : Bbar) ^ (s + 1) * (1 - beta b) := by
              rw [IsIdempotentElem.pow_succ_eq s hbbar.one_sub]
        change beta (algebraMap R B v * aeval b Q) = 1 - beta b
        rw [map_mul, hQb, hpow, ← mul_assoc, hvbar, one_mul]

/-- A residue idempotent generating an augmentation kernel admits a finite spanning
family on which multiplication is diagonal modulo the scalar ideal. -/
private theorem exists_spanning_family_mul_errors
    {R : Type*} {B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (I : Ideal R)
    (ρ : (B ⧸ I.map (algebraMap R B)) →ₐ[R] (R ⧸ I)) (b : B)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R B)) b))
    (hker : RingHom.ker ρ.toRingHom =
      Ideal.span {Ideal.Quotient.mk (I.map (algebraMap R B)) b}) :
    ∃ (s : ℕ) (v : Fin (s + 1) → B),
      Submodule.span R (Set.range v) = ⊤ ∧
        ∀ j, b * v j - (if j = 0 then 0 else v j) ∈ I • (⊤ : Submodule R B) := by
  classical
  let J : Ideal B := I.map (algebraMap R B)
  let β : B →ₐ[R] B ⧸ J := Ideal.Quotient.mkₐ R J
  change IsIdempotentElem (β b) at hb
  change RingHom.ker ρ.toRingHom = Ideal.span {β b} at hker
  obtain ⟨n, w, hw⟩ := Module.Finite.exists_fin (R := R) (M := B)
  have hlift : ∀ i : Fin n, ∃ a : R, Ideal.Quotient.mk I a = ρ (β (w i)) := by
    intro i
    exact Ideal.Quotient.mk_surjective (ρ (β (w i)))
  choose a ha using hlift
  let z : Fin n → B := fun i => w i - (a i • (1 - b) + b * w i)
  have hz_mem : ∀ i : Fin n, z i ∈ I • (⊤ : Submodule R B) := by
    intro i
    rw [Ideal.smul_top_eq_map]
    change z i ∈ J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hdiff : β (w i) - algebraMap R (B ⧸ J) (a i) ∈ RingHom.ker ρ.toRingHom := by
      change ρ (β (w i) - algebraMap R (B ⧸ J) (a i)) = 0
      rw [map_sub, ρ.commutes, Ideal.Quotient.algebraMap_eq, ha i, sub_self]
    rw [hker] at hdiff
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hdiff
    have hann : (1 - β b) * (β (w i) - algebraMap R (B ⧸ J) (a i)) = 0 := by
      rw [← hc]
      calc
        (1 - β b) * (c * β b) = c * ((1 - β b) * β b) := by ring
        _ = 0 := by rw [hb.one_sub_mul_self, mul_zero]
    change β (w i - (a i • (1 - b) + b * w i)) = 0
    simp only [map_sub, map_add, map_smul, map_one, map_mul]
    rw [Algebra.smul_def]
    calc
      β (w i) - (algebraMap R (B ⧸ J) (a i) * (1 - β b) + β b * β (w i)) =
          (1 - β b) * (β (w i) - algebraMap R (B ⧸ J) (a i)) := by ring
      _ = 0 := hann
  have hz_zero : ∀ i : Fin n, β (z i) = 0 := by
    intro i
    have hi := hz_mem i
    rw [Ideal.smul_top_eq_map] at hi
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hi
  let v : Fin (n + n + 1) → B :=
    Fin.cons (1 - b) (Fin.append (fun i => b * w i) z)
  let N : Submodule R B := Submodule.span R (Set.range v)
  have h0 : 1 - b ∈ N :=
    Submodule.subset_span ⟨0, by simp only [v, Fin.cons_zero]⟩
  have hbw : ∀ i : Fin n, b * w i ∈ N := by
    intro i
    exact Submodule.subset_span
      ⟨(Fin.castAdd n i).succ, by simp only [v, Fin.cons_succ, Fin.append_left]⟩
  have hz : ∀ i : Fin n, z i ∈ N := by
    intro i
    exact Submodule.subset_span
      ⟨(Fin.natAdd n i).succ, by simp only [v, Fin.cons_succ, Fin.append_right]⟩
  have hN : N = ⊤ := by
    apply top_unique
    rw [← hw]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    have hi : w i = a i • (1 - b) + b * w i + z i := by
      dsimp only [z]
      ring
    rw [hi]
    exact N.add_mem (N.add_mem (N.smul_mem (a i) h0) (hbw i)) (hz i)
  have htail : ∀ i : Fin (n + n),
      b * Fin.append (fun i => b * w i) z i - Fin.append (fun i => b * w i) z i ∈
        I • (⊤ : Submodule R B) := by
    refine (Fin.forall_fin_add (m := n) (n := n) _).mpr ?_
    constructor
    · intro i
      have hzero : β (b * (b * w i) - b * w i) = 0 := by
        simp only [map_sub, map_mul]
        rw [← mul_assoc, hb.eq, sub_self]
      have hmem : b * (b * w i) - b * w i ∈ I • (⊤ : Submodule R B) := by
        rw [Ideal.smul_top_eq_map]
        exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
      simpa only [Fin.append_left] using hmem
    · intro i
      have hzero : β (b * z i - z i) = 0 := by
        simp only [map_sub, map_mul, hz_zero, mul_zero, sub_self]
      have hmem : b * z i - z i ∈ I • (⊤ : Submodule R B) := by
        rw [Ideal.smul_top_eq_map]
        exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
      simpa only [Fin.append_right] using hmem
  refine ⟨n + n, v, hN, ?_⟩
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · have hzero : β (b * (1 - b)) = 0 := by
      simpa only [map_mul, map_sub, map_one] using hb.mul_one_sub_self
    have hmem : b * (1 - b) ∈ I • (⊤ : Submodule R B) := by
      rw [Ideal.smul_top_eq_map]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
    simpa [v] using hmem
  · simpa only [v, Fin.cons_succ, Fin.succ_ne_zero, ite_false] using htail i

/-- A residue augmentation with principal kernel makes the complementary quotient a
quotient of the source ring. The augmentation descends through that quotient. -/
private theorem component_augmentation_surjective
    {R : Type*} {B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (ρ : (B ⧸ I.map (algebraMap R B)) →ₐ[R] R ⧸ I) (b e : B)
    (hker : RingHom.ker ρ.toRingHom =
      Ideal.span {Ideal.Quotient.mk (I.map (algebraMap R B)) b})
    (he : Ideal.Quotient.mk (I.map (algebraMap R B)) e =
      1 - Ideal.Quotient.mk (I.map (algebraMap R B)) b) :
    ∃ ψ : (B ⧸ Ideal.span {1 - e}) →ₐ[R] R ⧸ I,
      ψ.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e})) =
        ρ.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R B))) ∧
      Function.Surjective (algebraMap R (B ⧸ Ideal.span {1 - e})) := by
  let A := B ⧸ I.map (algebraMap R B)
  let C := B ⧸ Ideal.span {1 - e}
  let β : B →ₐ[R] A := Ideal.Quotient.mkₐ R (I.map (algebraMap R B))
  let q : B →ₐ[R] C := Ideal.Quotient.mkₐ R (Ideal.span {1 - e})
  have hρb : ρ (β b) = 0 := by
    have hb : β b ∈ RingHom.ker ρ.toRingHom := by
      rw [hker]
      exact Ideal.mem_span_singleton_self _
    exact RingHom.mem_ker.mp hb
  have hρe : ρ (β e) = 1 := by
    change ρ (Ideal.Quotient.mk (I.map (algebraMap R B)) e) = 1
    rw [he, map_sub, map_one]
    change 1 - ρ (β b) = 1
    rw [hρb, sub_zero]
  have hkill : Ideal.span {1 - e} ≤ RingHom.ker (ρ.comp β).toRingHom := by
    apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    apply RingHom.mem_ker.mpr
    change ρ (β (1 - e)) = 0
    simp only [map_sub, map_one, hρe, sub_self]
  refine ⟨Ideal.Quotient.liftₐ (Ideal.span {1 - e}) (ρ.comp β)
    (fun z hz => RingHom.mem_ker.mp (hkill hz)), ?_, ?_⟩
  · exact Ideal.Quotient.liftₐ_comp _ _ _
  · let : Module.Finite R C :=
      Module.Finite.quotient R (Ideal.span {1 - e} : Ideal B)
    let J : Ideal C := I.map (algebraMap R C)
    have hqη : q.toRingHom.comp (algebraMap R B) = algebraMap R C := by
      ext a
      exact q.commutes a
    have hmap : (I.map (algebraMap R B)).map q.toRingHom = J := by
      rw [Ideal.map_map, hqη]
    have hmap_mem {z : B} (hz : z ∈ I.map (algebraMap R B)) : q z ∈ J := by
      rw [← hmap]
      exact Ideal.mem_map_of_mem q.toRingHom hz
    have hqzero : q (1 - e) = 0 := by
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr
        (Ideal.mem_span_singleton_self (1 - e))
    -- The principal residue generator disappears modulo the extended ideal in C.
    have hbrel : b - (1 - e) ∈ I.map (algebraMap R B) := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      change β (b - (1 - e)) = 0
      rw [map_sub, map_sub, map_one]
      change β b - (1 - β e) = 0
      rw [show β e = 1 - β b from he]
      ring
    have hqb : q b ∈ J := by
      simpa only [map_sub, hqzero, sub_zero] using hmap_mem hbrel
    -- Every element is a scalar modulo the extended ideal.
    have hscalar (x : B) : ∃ a : R, q x - algebraMap R C a ∈ J := by
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := I) (ρ (β x))
      have hxker : β (x - algebraMap R B a) ∈ RingHom.ker ρ.toRingHom := by
        apply RingHom.mem_ker.mpr
        change (ρ.comp β) (x - algebraMap R B a) = 0
        rw [map_sub, (ρ.comp β).commutes, Ideal.Quotient.algebraMap_eq]
        change ρ (β x) - Ideal.Quotient.mk I a = 0
        rw [ha, sub_self]
      have hxspan : β (x - algebraMap R B a) ∈ Ideal.span {β b} := by
        rw [hker] at hxker
        exact hxker
      obtain ⟨t₀, ht₀⟩ := Ideal.mem_span_singleton.mp hxspan
      obtain ⟨t, ht⟩ := Ideal.Quotient.mkₐ_surjective R (I.map (algebraMap R B)) t₀
      have hz : x - algebraMap R B a - b * t ∈ I.map (algebraMap R B) := by
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        change β (x - algebraMap R B a - b * t) = 0
        change β t = t₀ at ht
        rw [map_sub, map_mul, ht, ht₀, sub_self]
      refine ⟨a, ?_⟩
      have hsum := J.add_mem (hmap_mem hz) (Ideal.mul_mem_right (q t) J hqb)
      simpa only [map_sub, map_mul, q.commutes, sub_add_cancel] using hsum
    let S : Submodule R C := LinearMap.range (Algebra.linearMap R C)
    have hspan : (⊤ : Submodule R C) ≤ S ⊔ I • (⊤ : Submodule R C) := by
      intro c _
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (Ideal.span {1 - e}) c
      obtain ⟨a, ha⟩ := hscalar x
      have hd : q x - algebraMap R C a ∈ I • (⊤ : Submodule R C) := by
        rw [Ideal.smul_top_eq_map]
        exact ha
      have hs : algebraMap R C a ∈ S := LinearMap.mem_range.mpr ⟨a, rfl⟩
      have hd' : q x - algebraMap R C a ∈ S ⊔ I • (⊤ : Submodule R C) :=
        (le_sup_right : I • (⊤ : Submodule R C) ≤ S ⊔ I • ⊤) hd
      have hs' : algebraMap R C a ∈ S ⊔ I • (⊤ : Submodule R C) :=
        (le_sup_left : S ≤ S ⊔ I • (⊤ : Submodule R C)) hs
      simpa only [sub_add_cancel] using
        (S ⊔ I • (⊤ : Submodule R C)).add_mem hd' hs'
    have htop : (⊤ : Submodule R C) ≤ S :=
      Submodule.le_of_le_smul_of_le_jacobson_bot
        (Module.Finite.fg_top (R := R) (M := C)) hI hspan
    intro c
    have hc : c ∈ S := htop Submodule.mem_top
    simpa only [Algebra.linearMap_apply] using (LinearMap.mem_range.mp hc)

universe v w

/-- For a split augmentation, the conormal map to the base-changed Kähler differentials
is injective. The structural map into the quotient by the square of the augmentation
kernel is a section of the induced augmentation. Mathlib's conormal retraction/section
API (Andrew Yang), built on the differential API of Nicolò Cavalleri and Andrew Yang,
then gives a retraction of the conormal map. -/
private theorem augmentation_kerCotangentToTensor_injective
    {k : Type u} {A : Type v} [CommRing k] [CommRing A]
    [Algebra k A] [Algebra A k] [IsScalarTower k A k] :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k A k) := by
  let ρ : A →ₐ[k] k := IsScalarTower.toAlgHom k A k
  let η : k →ₐ[k] A := Algebra.ofId k A
  have hρη (c : k) : ρ (η c) = c := by
    simpa only [η, Algebra.ofId_apply, Algebra.algebraMap_self_apply] using ρ.commutes c
  have hρ : Function.Surjective (algebraMap A k) := by
    intro c
    refine ⟨η c, ?_⟩
    simpa only [ρ, IsScalarTower.toAlgHom_apply] using hρη c
  let Q := A ⧸ (RingHom.ker ρ.toRingHom) ^ 2
  let s : k →ₐ[k] Q := Algebra.ofId k Q
  have hs : ρ.kerSquareLift.comp s = AlgHom.id k k := by
    apply AlgHom.ext
    intro c
    simpa only [AlgHom.comp_apply, s, Algebra.ofId_apply, AlgHom.id_apply,
      Algebra.algebraMap_self_apply] using ρ.kerSquareLift.commutes c
  obtain ⟨r, hr⟩ :=
    (retractionKerCotangentToTensorEquivSection
      (R := k) (P := A) (S := k) (hf := hρ)).symm ⟨s, hs⟩
  have hr' : Function.LeftInverse r (KaehlerDifferential.kerCotangentToTensor k A k) :=
    fun x => LinearMap.congr_fun hr x
  exact hr'.injective

/-- The cotangent module of an augmentation vanishes when the augmentation factors through
a formally unramified principal localization. This uses Mathlib's localization equivalence
for Kähler differentials (Andrew Yang) and its tensor base-change equivalences
(Kim Morrison, Johan Commelin and Eric Wieser). -/
private theorem augmentation_cotangent_subsingleton_of_localization
    {k : Type u} {A : Type v} {U : Type w}
    [CommRing k] [CommRing A] [CommRing U]
    [Algebra k A] [Algebra A k] [IsScalarTower k A k]
    [Algebra k U] [Algebra A U] [IsScalarTower k A U]
    [Algebra U k] [IsScalarTower A U k]
    (d : A) [IsLocalization.Away d U] [Algebra.FormallyUnramified k U] :
    Subsingleton ((RingHom.ker (algebraMap A k)).Cotangent) := by
  let : IsScalarTower A k k :=
    IsScalarTower.of_algebraMap_smul fun a c => (Algebra.smul_def a c).symm
  let : IsScalarTower U k k :=
    IsScalarTower.of_algebraMap_smul fun a c => (Algebra.smul_def a c).symm
  let : Algebra.FormallyEtale A U :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers d)
  let e : TensorProduct A k (KaehlerDifferential k A) ≃ₗ[k]
      TensorProduct U k (KaehlerDifferential k U) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      A U k k (KaehlerDifferential k A)).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl k k)
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A U))
  have : Subsingleton (TensorProduct A k (KaehlerDifferential k A)) :=
    ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩
  exact ⟨fun x y => augmentation_kerCotangentToTensor_injective (k := k) (A := A)
    (Subsingleton.elim _ _)⟩

/-- A surjective étale algebra map with Jacobson-contained kernel is bijective. -/
private theorem bijective_of_etale_of_surjective_of_ker_le_jacobson
    {R : Type u} {C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.Etale R C]
    (hsurj : Function.Surjective (algebraMap R C))
    (hker : RingHom.ker (algebraMap R C) ≤ Ideal.jacobson (⊥ : Ideal R)) :
    Function.Bijective (algebraMap R C) := by
  have hsurj' : Function.Surjective (Algebra.ofId R C) := by
    intro c
    obtain ⟨r, hr⟩ := hsurj c
    exact ⟨r, by simpa only [Algebra.ofId_apply] using hr⟩
  have hfg : (RingHom.ker (algebraMap R C)).FG := by
    have hmap : (Algebra.ofId R C).toRingHom = algebraMap R C := by
      ext r
      exact Algebra.ofId_apply (R := R) C r
    rw [← hmap]
    exact Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId R C) hsurj'
  have hmul :
      RingHom.ker (algebraMap R C) * RingHom.ker (algebraMap R C) =
        RingHom.ker (algebraMap R C) :=
    isIdempotentElem_iff.mp
      ((Algebra.FormallyEtale.iff_of_surjective hsurj).mp inferInstance)
  have hbot : RingHom.ker (algebraMap R C) = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (RingHom.ker (algebraMap R C)) (RingHom.ker (algebraMap R C)) hfg ?_ hker
    exact le_of_eq (by rw [Ideal.smul_eq_mul, hmul])
  exact ⟨(RingHom.injective_iff_ker_eq_bot (algebraMap R C)).mpr hbot, hsurj⟩

/-- A residue section of an étale principal localization of a module-finite algebra
lifts over a Henselian pair. The component is constructed by a scalar monic
simple-root problem; no Henselian structure on the finite algebra is required. -/
private theorem exists_algHom_lift_of_finite_localization
    {R : Type u} {B : Type v} {U₀ : Type w}
    [CommRing R] [CommRing B] [CommRing U₀]
    [Algebra R B] [Algebra B U₀] [Algebra R U₀] [IsScalarTower R B U₀]
    [Module.Finite R B] (I : Ideal R) [HenselianRing R I]
    (d : B) [IsLocalization.Away d U₀] [Algebra.Etale R U₀]
    (ψ₀ : U₀ →ₐ[R] R ⧸ I) :
    ∃ σ : U₀ →ₐ[R] R, (Algebra.ofId R (R ⧸ I)).comp σ = ψ₀ := by
  classical
  let k := R ⧸ I
  let J : Ideal B := I.map (algebraMap R B)
  let A := B ⧸ J
  let β : B →ₐ[R] A := Ideal.Quotient.mkₐ R J
  let η : B →ₐ[R] U₀ := IsScalarTower.toAlgHom R B U₀
  let : Algebra k A := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower R k A := residue_quotient_isScalarTower I
  obtain ⟨ρ, hρ⟩ := residue_quotient_augmentation I (ψ₀.comp η)
  have hρβ (b : B) : ρ (β b) = ψ₀ (algebraMap B U₀ b) := by
    change ((ρ.restrictScalars R).comp β) b = ψ₀ (algebraMap B U₀ b)
    rw [hρ]
    simp only [AlgHom.comp_apply, η, IsScalarTower.toAlgHom_apply]
  have hqsurj : Function.Surjective (algebraMap R k) := by
    rw [Ideal.Quotient.algebraMap_eq I]
    exact Ideal.Quotient.mk_surjective
  -- Descend the original localization square, retaining the selected k-action on A.
  let Jᵤ : Ideal U₀ := I.map (algebraMap R U₀)
  let UQ := U₀ ⧸ Jᵤ
  let qᵤ : U₀ →ₐ[R] UQ := Ideal.Quotient.mkₐ R Jᵤ
  let : Algebra k UQ := Ideal.Quotient.algebraQuotientMapQuotient
  let : IsScalarTower R k UQ := Ideal.Quotient.tower_quotient_map_quotient
  have hmap : J.map (algebraMap B U₀) = Jᵤ := by
    dsimp only [J, Jᵤ]
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R B U₀]
  have hle : J ≤ Jᵤ.comap η.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mp
    change J.map (algebraMap B U₀) ≤ Jᵤ
    exact le_of_eq hmap
  let aR : A →ₐ[R] UQ := Ideal.quotientMapₐ Jᵤ η hle
  let aK : A →ₐ[k] UQ := AlgHom.extendScalarsOfSurjective hqsurj aR
  have haK : aK.restrictScalars R = aR :=
    AlgHom.restrictScalars_extendScalarsOfSurjective hqsurj aR
  have haβ (b : B) : aK (β b) = qᵤ (algebraMap B U₀ b) := by
    change (aK.restrictScalars R) (β b) = qᵤ (algebraMap B U₀ b)
    rw [haK]
    have hβb : β b = Ideal.Quotient.mk J b :=
      DFunLike.congr_fun (Ideal.Quotient.mkₐ_toRingHom (R₁ := R) J) b
    rw [hβb]
    simpa only [aR, qᵤ, η, IsScalarTower.toAlgHom_apply] using
      (Ideal.quotient_map_mkₐ (R₁ := R) (I := J) (J := Jᵤ) η hle (x := b))
  let : Algebra A UQ := aK.toRingHom.toAlgebra
  let : IsScalarTower k A UQ := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    rw [RingHom.algebraMap_toAlgebra aK.toRingHom]
    exact (aK.commutes c).symm
  let : IsScalarTower R A UQ := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    rw [RingHom.algebraMap_toAlgebra aK.toRingHom]
    exact ((aK.restrictScalars R).commutes r).symm
  have hsquare : qᵤ.toRingHom.comp (algebraMap B U₀) =
      (algebraMap A UQ).comp β.toRingHom := by
    ext b
    exact (haβ b).symm
  have hkbound : RingHom.ker qᵤ.toRingHom ≤
      (RingHom.ker β.toRingHom).map (algebraMap B U₀) := by
    dsimp only [qᵤ, β]
    have hkerJ : RingHom.ker (Ideal.Quotient.mk J) = J := by
      ext b
      simp only [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    have hkerJᵤ : RingHom.ker (Ideal.Quotient.mk Jᵤ) = Jᵤ := by
      ext x
      simp only [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    simpa only [Ideal.Quotient.mkₐ_toRingHom, hkerJ, hkerJᵤ] using le_of_eq hmap.symm
  let : IsLocalization.Away (β d) UQ := by
    have hloc := IsLocalization.of_surjective (M := Submonoid.powers d) (S := U₀)
      β.toRingHom (Ideal.Quotient.mkₐ_surjective R J)
      qᵤ.toRingHom (Ideal.Quotient.mkₐ_surjective R Jᵤ) hsquare hkbound
    rw [Submonoid.map_powers] at hloc
    exact hloc
  let : Algebra.FormallyUnramified k UQ :=
    Algebra.FormallyUnramified.quotient_map (R := R) (B := U₀) I
  have hδ : IsUnit (ρ (β d)) := by
    rw [hρβ]
    exact (IsLocalization.Away.algebraMap_isUnit (S := U₀) d).map ψ₀.toRingHom
  let ψ₁ : UQ →ₐ[k] k := IsLocalization.Away.liftAlgHom (β d) hδ
  have hψ₁ : ψ₁.toRingHom.comp (algebraMap A UQ) = ρ.toRingHom := by
    dsimp only [ψ₁]
    rw [IsLocalization.Away.liftAlgHom_toRingHom]
    exact IsLocalization.Away.lift_comp (S := UQ) (x := β d) (g := ρ.toRingHom) hδ
  -- Both augmentation actions are those of the displayed maps.
  let : Algebra A k := ρ.toRingHom.toAlgebra
  let : Algebra UQ k := ψ₁.toRingHom.toAlgebra
  let : IsScalarTower k A k := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    rw [RingHom.algebraMap_toAlgebra ρ.toRingHom]
    exact (ρ.commutes c).symm
  let : IsScalarTower A UQ k := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [RingHom.algebraMap_toAlgebra ρ.toRingHom,
      RingHom.algebraMap_toAlgebra ψ₁.toRingHom]
    exact hψ₁.symm
  have hcot : Subsingleton (RingHom.ker ρ.toRingHom).Cotangent := by
    change Subsingleton (RingHom.ker (algebraMap A k)).Cotangent
    exact augmentation_cotangent_subsingleton_of_localization (k := k) (A := A)
      (U := UQ) (β d)
  let : Module.Finite R A := Module.Finite.quotient R (J : Ideal B)
  let : Module.Finite k A := Module.Finite.of_restrictScalars_finite R k A
  have hKfg : (RingHom.ker ρ.toRingHom).FG := augmentation_ker_fg ρ
  have hKid : IsIdempotentElem (RingHom.ker ρ.toRingHom) :=
    (Ideal.cotangent_subsingleton_iff _).mp hcot
  obtain ⟨bbar, hbbar, hK⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ hKfg).mp hKid
  obtain ⟨b, hb⟩ := Ideal.Quotient.mkₐ_surjective R J bbar
  have hbidem : IsIdempotentElem (β b) := by
    change β b = bbar at hb
    rw [hb]
    exact hbbar
  have hker : RingHom.ker (ρ.restrictScalars R).toRingHom = Ideal.span {β b} := by
    change β b = bbar at hb
    rw [hb]
    exact hK
  obtain ⟨s, v, hv, herr⟩ :=
    exists_spanning_family_mul_errors I (ρ.restrictScalars R) b hbidem hker
  let f : Module.End R B := Algebra.lmul R B b
  have hf (x : B) : f x = b * x := by
    dsimp only [f]
    rw [Algebra.coe_lmul_eq_mul]
    exact LinearMap.mul_apply' b x
  obtain ⟨M, hM, hMbar⟩ := exists_matrix_represents_map_diagonal I v hv f
    (fun j => by rw [hf]; exact herr j)
  have hchar : aeval f M.charpoly = 0 := aeval_charpoly_eq_zero_of_represents hv hM
  have hann : aeval b M.charpoly = 0 := by
    apply Algebra.lmul_injective (R := R) (A := B)
    rw [← Polynomial.aeval_algHom_apply, map_zero]
    exact hchar
  obtain ⟨hmonic, hbar⟩ :=
    charpoly_monic_and_map_eq_of_diagonal M (Ideal.Quotient.mk I) hMbar
  obtain ⟨e, heidem, he⟩ := exists_isIdempotentElem_of_monic_annihilator
    I s M.charpoly hmonic hbar b hann hbidem
  -- First establish surjectivity of the component's structural map.
  let C := B ⧸ Ideal.span {1 - e}
  let q : B →ₐ[R] C := Ideal.Quotient.mkₐ R (Ideal.span {1 - e})
  have hqmap : q.toRingHom = algebraMap B C := by
    change (Ideal.Quotient.mkₐ R _).toRingHom = algebraMap B C
    rw [Ideal.Quotient.mkₐ_toRingHom, Ideal.Quotient.algebraMap_eq]
  obtain ⟨ψC, hψC, hsurj⟩ := component_augmentation_surjective I
    (HenselianRing.jac (R := R) (I := I)) (ρ.restrictScalars R) b e hker he
  have hψq (x : B) : ψC (q x) = ρ (β x) :=
    DFunLike.congr_fun hψC x
  have hdC : IsUnit (q d) := by
    obtain ⟨a, ha⟩ := hsurj (q d)
    have hqa : IsUnit (algebraMap R k a) := by
      rw [← ψC.commutes a, ha, hψq]
      exact hδ
    let : IsLocalHom (Ideal.Quotient.mk I) :=
      isLocalHom_of_le_jacobson_bot I (HenselianRing.jac (R := R) (I := I))
    have hau : IsUnit a := IsUnit.of_map (Ideal.Quotient.mk I) a (by
      change IsUnit (algebraMap R (R ⧸ I) a) at hqa
      simpa only [Ideal.Quotient.algebraMap_eq I] using hqa)
    rw [← ha]
    exact hau.map (algebraMap R C)
  have hdC' : IsUnit (algebraMap B C d) := by
    rw [← hqmap]
    exact hdC
  -- The localization map is defined before its action and the étale structure.
  let μ : U₀ →ₐ[R] C := IsLocalization.Away.liftAlgHom d hdC
  have hμ : μ.toRingHom.comp (algebraMap B U₀) = q.toRingHom := by
    dsimp only [μ]
    rw [IsLocalization.Away.liftAlgHom_toRingHom]
    exact IsLocalization.Away.lift_comp (S := U₀) (x := d) (g := q.toRingHom) hdC
  let : Algebra U₀ C := μ.toRingHom.toAlgebra
  let : IsScalarTower R U₀ C := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [RingHom.algebraMap_toAlgebra μ.toRingHom]
    exact μ.comp_algebraMap.symm
  let : IsScalarTower B U₀ C := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [RingHom.algebraMap_toAlgebra μ.toRingHom]
    exact (hμ.trans hqmap).symm
  let : IsScalarTower B C C := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    exact (Algebra.algebraMap_self_apply _).symm
  let : IsLocalization.Away e C :=
    IsLocalization.Away.quotient_of_isIdempotentElem heidem
  let : IsLocalization.Away (algebraMap B C d) C :=
    IsLocalization.away_of_isUnit_of_bijective C hdC' (by
      constructor
      · intro x y h
        simpa only [Algebra.algebraMap_self_apply] using h
      · intro x
        exact ⟨x, Algebra.algebraMap_self_apply x⟩)
  let : IsLocalization.Away (algebraMap B U₀ e) C :=
    IsLocalization.Away.commutes (R := B) U₀ C C d e
  let : Algebra.Etale U₀ C :=
    Algebra.Etale.of_isLocalizationAway (algebraMap B U₀ e)
  let : Algebra.Etale R C := Algebra.Etale.comp R U₀ C
  have hkI : RingHom.ker (algebraMap R C) ≤ I := by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz : algebraMap R k a = 0 := by
      rw [← ψC.commutes a, RingHom.mem_ker.mp ha, map_zero]
    change algebraMap R (R ⧸ I) a = 0 at hz
    simpa only [Ideal.Quotient.algebraMap_eq I] using hz
  have hbij : Function.Bijective (algebraMap R C) :=
    bijective_of_etale_of_surjective_of_ker_le_jacobson hsurj
      (hkI.trans (HenselianRing.jac (R := R) (I := I)))
  let ε : R ≃ₐ[R] C := AlgEquiv.ofBijective (Algebra.ofId R C) hbij
  have hε (a : R) : ε a = algebraMap R C a := by
    simpa only [Algebra.algebraMap_self_apply] using ε.commutes a
  let σ : U₀ →ₐ[R] R := ε.symm.toAlgHom.comp μ
  have hredC (c : C) : algebraMap R k (ε.symm c) = ψC c := by
    calc
      algebraMap R k (ε.symm c) = ψC (algebraMap R C (ε.symm c)) :=
        (ψC.commutes _).symm
      _ = ψC c := by rw [← hε, ε.apply_symm_apply]
  refine ⟨σ, ?_⟩
  have hred : ((Algebra.ofId R k).comp σ).toRingHom = ψ₀.toRingHom := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers d)
    ext x
    change algebraMap R k (ε.symm (μ (algebraMap B U₀ x))) =
      ψ₀ (algebraMap B U₀ x)
    rw [hredC]
    have hμx : μ (algebraMap B U₀ x) = q x := DFunLike.congr_fun hμ x
    rw [hμx, hψq, hρβ]
  exact AlgHom.ext fun x => DFunLike.congr_fun hred x

/-- Decode an ordered coprime universal factorization whose image is a prescribed pair.
The reduction map and the universal algebra map are supplied; their existence is separate. -/
private theorem exists_monic_factorization_of_universal_coprime_lift
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {n m k : ℕ} (hn : n = m + k) (p : Polynomial.MonicDegreeEq R n)
    (g₀ : Polynomial.MonicDegreeEq S m) (h₀ : Polynomial.MonicDegreeEq S k)
    (hfac : g₀.1 * h₀.1 = p.1.map (algebraMap R S))
    (hcop : IsCoprime g₀.1 h₀.1) (q : R →ₐ[R] S)
    (σ : Polynomial.UniversalCoprimeFactorizationRing m k hn p →ₐ[R] R)
    (hσ : q.comp σ =
      (Polynomial.UniversalCoprimeFactorizationRing.homEquiv S m k hn p).symm
        ⟨(g₀, h₀), hfac, hcop⟩) :
    ∃ g h : R[X], g.Monic ∧ h.Monic ∧ p.1 = g * h ∧
      g.map q.toRingHom = g₀.1 ∧ h.map q.toRingHom = h₀.1 := by
  refine ⟨(Polynomial.UniversalCoprimeFactorizationRing.homEquiv R m k hn p σ).1.1.1,
    (Polynomial.UniversalCoprimeFactorizationRing.homEquiv R m k hn p σ).1.2.1,
    (Polynomial.UniversalCoprimeFactorizationRing.homEquiv R m k hn p σ).1.1.monic,
    (Polynomial.UniversalCoprimeFactorizationRing.homEquiv R m k hn p σ).1.2.monic,
    ?_, ?_, ?_⟩
  · simpa only [Algebra.algebraMap_self, Polynomial.map_id] using
      (Polynomial.UniversalCoprimeFactorizationRing.homEquiv R m k hn p σ).2.1.symm
  · have h := Polynomial.UniversalCoprimeFactorizationRing.homEquiv_comp_fst
      R m k hn p σ q
    rw [hσ, Equiv.apply_symm_apply] at h
    have hraw := congrArg (fun a : Polynomial.MonicDegreeEq S m => a.1) h.symm
    change
      (Polynomial.UniversalCoprimeFactorizationRing.homEquiv R m k hn p σ).1.1.1.map
        q.toRingHom = g₀.1 at hraw
    exact hraw
  · have h := Polynomial.UniversalCoprimeFactorizationRing.homEquiv_comp_snd
      R m k hn p σ q
    rw [hσ, Equiv.apply_symm_apply] at h
    have hraw := congrArg (fun a : Polynomial.MonicDegreeEq S k => a.1) h.symm
    change
      (Polynomial.UniversalCoprimeFactorizationRing.homEquiv R m k hn p σ).1.2.1.map
        q.toRingHom = h₀.1 at hraw
    exact hraw

/-- Over a Henselian pair, every prescribed factorization of a monic polynomial into
coprime monic polynomials modulo the ideal lifts to monic factors over the ring,
with the prescribed reductions. -/
theorem exists_monic_factorization
    {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I]
    {f : R[X]} {g₀ h₀ : (R ⧸ I)[X]}
    (hf : f.Monic) (hg : g₀.Monic) (hh : h₀.Monic)
    (hcop : IsCoprime g₀ h₀)
    (hfac : f.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃ g h : R[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (Ideal.Quotient.mk I) = g₀ ∧
      h.map (Ideal.Quotient.mk I) = h₀ := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      let : Subsingleton R := hR
      refine ⟨1, f, monic_one, hf, (one_mul f).symm, ?_, ?_⟩
      · exact Subsingleton.elim _ _
      · exact Subsingleton.elim _ _
  | inr hR =>
      let : Nontrivial R := hR
      have hI : I ≠ ⊤ := by
        intro htop
        have hj := HenselianRing.jac (R := R) (I := I)
        rw [htop, top_le_iff, Ideal.jacobson_eq_top_iff] at hj
        exact bot_ne_top hj
      let κ := R ⧸ I
      let : Nontrivial κ := Ideal.Quotient.nontrivial_iff.mpr hI
      let n := f.natDegree
      let m := g₀.natDegree
      let k := h₀.natDegree
      have hn : n = m + k := by
        calc
          f.natDegree = (f.map (Ideal.Quotient.mk I)).natDegree :=
            (hf.natDegree_map (Ideal.Quotient.mk I)).symm
          _ = (g₀ * h₀).natDegree := congrArg Polynomial.natDegree hfac
          _ = g₀.natDegree + h₀.natDegree := hg.natDegree_mul hh
      let p : Polynomial.MonicDegreeEq R n := Polynomial.MonicDegreeEq.mk f hf rfl
      let gpack : Polynomial.MonicDegreeEq κ m := Polynomial.MonicDegreeEq.mk g₀ hg rfl
      let hpack : Polynomial.MonicDegreeEq κ k := Polynomial.MonicDegreeEq.mk h₀ hh rfl
      let B := Polynomial.UniversalFactorizationRing m k hn p
      let U := Polynomial.UniversalCoprimeFactorizationRing m k hn p
      let J : B := (Polynomial.UniversalFactorizationRing.presentation m k hn p).jacobian
      let d : B := (Polynomial.UniversalFactorizationRing.factor₁ m k hn p).1.resultant
        (Polynomial.UniversalFactorizationRing.factor₂ m k hn p).1
      -- Keep the existing R- and B-actions on the same universal coprime ring.
      let : IsScalarTower R B U := by
        apply IsScalarTower.of_algebraMap_eq
        intro r
        exact (Localization.mk_algebraMap (M := Submonoid.powers J) r).symm.trans
          (Localization.mk_one_eq_algebraMap (M := Submonoid.powers J) (algebraMap R B r))
      let : IsLocalization.Away J U := inferInstance
      have hJd : Associated J d := by
        dsimp only [J, d]
        rw [Polynomial.UniversalFactorizationRing.jacobian_resentation]
        exact associated_unit_mul_left _ _ (isUnit_neg_one.pow n)
      let : IsLocalization.Away d U := IsLocalization.Away.of_associated hJd
      have hprod : gpack.1 * hpack.1 = p.1.map (algebraMap R κ) := by
        change g₀ * h₀ = f.map (algebraMap R κ)
        rw [Ideal.Quotient.algebraMap_eq I]
        exact hfac.symm
      let ψ₀ : U →ₐ[R] κ :=
        (Polynomial.UniversalCoprimeFactorizationRing.homEquiv κ m k hn p).symm
          ⟨(gpack, hpack), hprod, hcop⟩
      obtain ⟨σ, hσ⟩ := exists_algHom_lift_of_finite_localization (B := B) I d ψ₀
      obtain ⟨g, h, hgm, hhm, hgh, hgred, hhred⟩ :=
        exists_monic_factorization_of_universal_coprime_lift hn p gpack hpack
          hprod hcop (Algebra.ofId R κ) σ hσ
      have hq : (Algebra.ofId R κ).toRingHom = Ideal.Quotient.mk I := by
        ext r
        change Algebra.ofId R κ r = (Ideal.Quotient.mk I) r
        rw [Algebra.ofId_apply, Ideal.Quotient.algebraMap_eq I]
      refine ⟨g, h, hgm, hhm, hgh, ?_, ?_⟩
      · change g.map (Algebra.ofId R κ).toRingHom = g₀ at hgred
        simpa only [hq] using hgred
      · change h.map (Algebra.ofId R κ).toRingHom = h₀ at hhred
        simpa only [hq] using hhred

end HenselianRing
