/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.LocalizedResidueField

/-!
# Quotient valuation rings in completed-localization residue fields

This file transports the quotient valuation ring at a nonzero prime into the
residue field of the completed-localization valuation subring. The transport is
the comap along the inverse of the localized-completion residue-field
equivalence.
-/

@[expose] public section

set_option linter.style.haveILetI false

open scoped Topology

noncomputable section

universe u v

namespace ValuationRing

variable {V : Type u} {K : Type v}
  [CommRing V] [IsDomain V] [ValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

/-- The complement of a nonzero prime is disjoint from the radical of every
principal ideal whose power filtration is separated. -/
theorem primeCompl_disjoint_radical_span_singleton_of_isHausdorff
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} [IsHausdorff (Ideal.span {a}) V] :
    Disjoint (p.primeCompl : Set V) ((Ideal.span {a}).radical : Set V) := by
  rw [Set.disjoint_left]
  intro x hxp hxa
  exact (Ideal.mem_primeCompl_iff.mp hxp)
    (radical_span_singleton_le_prime_of_isHausdorff p hp hxa)

/-- The quotient valuation ring `V / p`, transported into the residue field of
the completed localization at `p`.

The canonical valuation subring of `p.ResidueField`, with coefficient ring
`V / p`, is pulled back along the inverse of the completed-localization
residue-field equivalence. This inverse orientation makes the result a
valuation subring of the completed-localization residue field. -/
noncomputable def localizedAtPrimeQuotientValuationSubring
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let A := localizedAdicCompletionValuationSubring
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0
        (primeCompl_disjoint_radical_span_singleton_of_isHausdorff p hp)
    ValuationSubring (IsLocalRing.ResidueField A) := by
  let hDisj :=
    primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
  letI : ValuationRing (V ⧸ p) :=
    Function.Surjective.valuationRing (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective
  let B := (valuation (V ⧸ p) p.ResidueField).valuationSubring
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let A := localizedAdicCompletionValuationSubring
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  let e : p.ResidueField ≃+* IsLocalRing.ResidueField A :=
    localizedAdicCompletionResidueFieldEquiv
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  exact B.comap e.symm.toRingHom

/-- An element belongs to the transported quotient valuation ring exactly when
its inverse image in `p.ResidueField` belongs to the canonical quotient
valuation subring. -/
@[simp]
theorem mem_localizedAtPrimeQuotientValuationSubring
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V]
    (x :
      letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
      let A := localizedAdicCompletionValuationSubring
        (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0
          (primeCompl_disjoint_radical_span_singleton_of_isHausdorff p hp)
      IsLocalRing.ResidueField A) :
    letI : ValuationRing (V ⧸ p) :=
      Function.Surjective.valuationRing (Ideal.Quotient.mk p)
        Ideal.Quotient.mk_surjective
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let hDisj :=
      primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
    let A := localizedAdicCompletionValuationSubring
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
    let e : p.ResidueField ≃+* IsLocalRing.ResidueField A :=
      localizedAdicCompletionResidueFieldEquiv
        (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
    x ∈ localizedAtPrimeQuotientValuationSubring (K := K) p hp ha0 ↔
      e.symm x ∈ (valuation (V ⧸ p) p.ResidueField).valuationSubring := by
  let hDisj :=
    primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
  letI : ValuationRing (V ⧸ p) :=
    Function.Surjective.valuationRing (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let A := localizedAdicCompletionValuationSubring
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  let e : p.ResidueField ≃+* IsLocalRing.ResidueField A :=
    localizedAdicCompletionResidueFieldEquiv
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  change e.symm x ∈ (valuation (V ⧸ p) p.ResidueField).valuationSubring ↔ _
  rfl

/-- The transported quotient valuation ring contains the image of every
element of `V / p`. -/
theorem localizedAtPrimeQuotientValuationSubring_algebraMap_mem
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V]
    (x : V ⧸ p) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let hDisj :=
      primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
    let A := localizedAdicCompletionValuationSubring
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
    let e : p.ResidueField ≃+* IsLocalRing.ResidueField A :=
      localizedAdicCompletionResidueFieldEquiv
        (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
    e (algebraMap (V ⧸ p) p.ResidueField x) ∈
      localizedAtPrimeQuotientValuationSubring (K := K) p hp ha0 := by
  let hDisj :=
    primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
  letI : ValuationRing (V ⧸ p) :=
    Function.Surjective.valuationRing (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective
  let B := (valuation (V ⧸ p) p.ResidueField).valuationSubring
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let A := localizedAdicCompletionValuationSubring
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  let e : p.ResidueField ≃+* IsLocalRing.ResidueField A :=
    localizedAdicCompletionResidueFieldEquiv
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  change e.symm (e (algebraMap (V ⧸ p) p.ResidueField x)) ∈ B
  rw [e.symm_apply_apply, Valuation.mem_valuationSubring_iff]
  exact (ValuationRing.integers (V ⧸ p) p.ResidueField).map_le_one x

end ValuationRing
