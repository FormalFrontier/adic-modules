/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Hensel factor lifting and irreducible reduction

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

For a maximal ideal, the reduction of a monic irreducible polynomial in `R[X]` is a positive
power of a monic irreducible polynomial. The proof extracts the largest power of one normalized
irreducible factor. Its coprime complement lifts, so irreducibility forces that complement to
be 1. This argument allows coefficient rings with zero divisors. For a
valuation domain with fraction field `F`, irreducibility over `F` implies the required
irreducibility over the integer ring by Mathlib's
`Polynomial.Monic.irreducible_of_irreducible_map`. Thus the coefficient-ring hypothesis does
not require an additional irreducibility assumption in the complete discretely valued case.
The source's Exercise 4 treats all Henselian valuation fields; adic completeness is a different,
more restrictive hypothesis in that setting, and no equivalence with that scope is asserted.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  AMS, 2002, Chapter II, §1, Corollary 1 (coprime Hensel lifting over complete discrete
  valuation rings). The theorem here is stated for arbitrary adically complete rings.
* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  AMS, 2002, Chapter II, §1, Exercise 4, p. 38 (irreducible reduction over Henselian
  valuation fields).
* Mathlib's `Polynomial.UniversalCoprimeFactorizationRing.homEquiv` and
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`.
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
  obtain ⟨g, h, hgm, hhm, _, hgh, hg, hh⟩ :=
    exists_monic_factorization_of_isAdicComplete I hf (hqm.pow e) ham
      ((hqi.coprime_iff_not_dvd.mpr hqa).pow_left) hfac
  -- The lift of the positive power cannot be a unit, so the other lift is 1.
  have ha : a = 1 := by
    rcases hirr.isUnit_or_isUnit hgh with hgu | hhu
    · have hqpow : q ^ e = 1 := by
        rw [← hg, hgm.eq_one_of_isUnit hgu, Polynomial.map_one]
      exact (hqi.not_isUnit (isUnit_of_dvd_one (hqpow ▸ dvd_pow_self q he.ne'))).elim
    · rw [← hh, hhm.eq_one_of_isUnit hhu, Polynomial.map_one]
  exact ⟨q, e, hqm, hqi, he, by simpa [ha] using hfac⟩

end Polynomial
