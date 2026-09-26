/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.LocalizedQuotientValuationSubring
public import AdicModules.CompositeValuationSubring

/-!
# Completed valuation rings as composites

This file identifies the completed valuation-integer subring with the composite
of the completed localization at a nonzero prime and the transported quotient
valuation ring. It also recovers the localized factor and quotient factor from
the distinguished prime of that composite.
-/

@[expose] public section

open scoped Topology

noncomputable section

set_option linter.style.haveILetI false

universe u v

namespace ValuationRing

variable {V : Type u} {K : Type v} [CommRing V] [IsDomain V]
  [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

/-- The canonical map from a separated principal-adic valuation ring to the
valuation integers of its completed fraction field is local. -/
theorem completionIntegers_algebraMap_isLocalHom
    (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
    [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    IsLocalHom (algebraMap V (CompletionIntegers V K)) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let D := AdicCompletion (Ideal.span {a}) V
  letI : IsDomain D := principalAdicCompletion_isDomain K a ha0
  letI : ValuationRing D := principalAdicCompletion_isValuationRing K a ha0
  letI : ValuationRing (CompletionIntegers V K) :=
    ValuationRing.instValuationRingInteger
      (Valued.v : Valuation (UniformSpace.Completion K) (ValueGroup V K))
  let e := principalAdicCompletionRingEquiv (V := V) (K := K) a ha0
  letI : IsLocalHom e.toRingHom :=
    { map_nonunit := (isLocalHom_equiv e).map_nonunit }
  letI : IsLocalHom (algebraMap V D) :=
    principalAdicCompletion_algebraMap_isLocalHom K a ha0 ha
  have hcomp : IsLocalHom (e.toRingHom.comp (algebraMap V D)) :=
    RingHom.isLocalHom_comp _ _
  have heq : e.toRingHom.comp (algebraMap V D) =
      algebraMap V (CompletionIntegers V K) := by
    apply RingHom.ext
    intro x
    exact principalAdicCompletionRingEquiv_algebraMap
      (V := V) (K := K) a ha0 x
  rw [heq] at hcomp
  exact hcomp

/-- The canonical map to the completed valuation integers induces a bijection
on residue fields. -/
theorem completionIntegers_residueFieldMap_bijective
    (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
    [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    letI : ValuationRing (CompletionIntegers V K) :=
      ValuationRing.instValuationRingInteger
        (Valued.v : Valuation (UniformSpace.Completion K) (ValueGroup V K))
    letI : IsLocalHom (algebraMap V (CompletionIntegers V K)) :=
      completionIntegers_algebraMap_isLocalHom a ha0 ha
    Function.Bijective (IsLocalRing.ResidueField.map
      (algebraMap V (CompletionIntegers V K))) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let D := AdicCompletion (Ideal.span {a}) V
  letI : IsDomain D := principalAdicCompletion_isDomain K a ha0
  letI : ValuationRing D := principalAdicCompletion_isValuationRing K a ha0
  letI : ValuationRing (CompletionIntegers V K) :=
    ValuationRing.instValuationRingInteger
      (Valued.v : Valuation (UniformSpace.Completion K) (ValueGroup V K))
  let e := principalAdicCompletionRingEquiv (V := V) (K := K) a ha0
  letI : IsLocalHom e.toRingHom :=
    { map_nonunit := (isLocalHom_equiv e).map_nonunit }
  letI : IsLocalHom (algebraMap V D) :=
    principalAdicCompletion_algebraMap_isLocalHom K a ha0 ha
  letI : IsLocalHom (algebraMap V (CompletionIntegers V K)) :=
    completionIntegers_algebraMap_isLocalHom a ha0 ha
  have heq : e.toRingHom.comp (algebraMap V D) =
      algebraMap V (CompletionIntegers V K) := by
    apply RingHom.ext
    intro x
    exact principalAdicCompletionRingEquiv_algebraMap
      (V := V) (K := K) a ha0 x
  have hmap : IsLocalRing.ResidueField.map
        (algebraMap V (CompletionIntegers V K)) =
      (IsLocalRing.ResidueField.mapEquiv e).toRingHom.comp
        (IsLocalRing.ResidueField.map (algebraMap V D)) := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    change IsLocalRing.ResidueField.map
        (algebraMap V (CompletionIntegers V K)) (IsLocalRing.residue V x) =
      IsLocalRing.ResidueField.map e.toRingHom
        (IsLocalRing.ResidueField.map (algebraMap V D)
          (IsLocalRing.residue V x))
    rw [IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue]
    exact congrArg (fun f : V →+* CompletionIntegers V K ↦
      IsLocalRing.residue (CompletionIntegers V K) (f x)) heq.symm
  rw [hmap]
  exact (IsLocalRing.ResidueField.mapEquiv e).bijective.comp
    (principalAdicCompletion_residueFieldMap_bijective K a ha0 ha)

private theorem nonunits_subset_of_le {F : Type*} [Field F]
    {R S : ValuationSubring F} (h : R ≤ S) :
    (S.nonunits : Set F) ⊆ R := by
  intro x hx
  rcases (S.mem_nonunits_iff_or.mp hx) with rfl | hxinv
  · exact R.zero_mem
  · exact (R.mem_or_inv_mem x).resolve_right fun hxR ↦ hxinv (h hxR)

/-- The completed valuation integers lie in the valuation subring obtained
from the completed localization at a nonzero prime. -/
theorem completionIntegers_le_localizedAtPrime
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let C := (Valued.v : Valuation (UniformSpace.Completion K)
      (ValueGroup V K)).valuationSubring
    let hDisj :=
      primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
    let A := localizedAdicCompletionValuationSubring
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
    C ≤ A := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let C := (Valued.v : Valuation (UniformSpace.Completion K)
    (ValueGroup V K)).valuationSubring
  let hDisj :=
    primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
  let A := localizedAdicCompletionValuationSubring
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  change C ≤ A
  intro x hx
  have hx' : Valued.v x ≤ (1 : ValueGroup V K) := hx
  let z : CompletionIntegers V K := ⟨x, hx'⟩
  obtain ⟨y, hy⟩ := completionIntegers_mem_range_localizedAdicCompletion
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj z
  let ey := localizedAdicCompletionValuationSubringEquiv
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj y
  have hey : ((ey : A) : UniformSpace.Completion K) = x := by
    calc
      ((ey : A) : UniformSpace.Completion K) =
          localizedAdicCompletionToFractionFieldCompletion
            (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj y :=
        coe_localizedAdicCompletionValuationSubringEquiv_apply
          (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj y
      _ = (z : UniformSpace.Completion K) := hy
      _ = x := rfl
  rw [← hey]
  exact ey.property

/-- The completed valuation integers are literally the composite of the
completed localization at `p` and the transported quotient valuation ring. -/
theorem completionIntegersValuationSubring_eq_localizedAtPrime_composite
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let C := (Valued.v : Valuation (UniformSpace.Completion K)
      (ValueGroup V K)).valuationSubring
    let hDisj :=
      primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
    let A := localizedAdicCompletionValuationSubring
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
    let W := localizedAtPrimeQuotientValuationSubring (K := K) p hp ha0
    C = A.composite W := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let C := (Valued.v : Valuation (UniformSpace.Completion K)
    (ValueGroup V K)).valuationSubring
  let hDisj :=
    primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
  let A := localizedAdicCompletionValuationSubring
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  let W := localizedAtPrimeQuotientValuationSubring (K := K) p hp ha0
  let e : p.ResidueField ≃+* IsLocalRing.ResidueField A :=
    localizedAdicCompletionResidueFieldEquiv
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  let eA := localizedAdicCompletionValuationSubringEquiv
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  change C = A.composite W
  letI : ValuationRing (V ⧸ p) :=
    Function.Surjective.valuationRing (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective
  have haMax : a ∈ IsLocalRing.maximalIdeal V := by
    apply IsLocalRing.le_maximalIdeal_of_isPrime p
    apply radical_span_singleton_le_prime_of_isHausdorff (a := a) p hp
    exact Ideal.le_radical (by simp)
  have hCA : C ≤ A :=
    completionIntegers_le_localizedAtPrime (K := K) p hp ha0
  have hbaseC (x : V) :
      (((algebraMap V (CompletionIntegers V K) x : CompletionIntegers V K) :
        UniformSpace.Completion K)) ∈ C :=
    (algebraMap V (CompletionIntegers V K) x).property
  have hbaseResidue (x : V) :
      IsLocalRing.residue A
          ⟨((algebraMap V (CompletionIntegers V K) x : CompletionIntegers V K) :
            UniformSpace.Completion K), hCA (hbaseC x)⟩ =
        e (algebraMap (V ⧸ p) p.ResidueField (Ideal.Quotient.mk p x)) := by
    have hres := localizedAdicCompletionResidueFieldEquiv_residue
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
        (algebraMap V (Localization.AtPrime p) x)
    change e (algebraMap (V ⧸ p) p.ResidueField (Ideal.Quotient.mk p x)) =
      IsLocalRing.residue A
        (eA (algebraMap (Localization.AtPrime p)
          (AdicCompletion
            (Ideal.span {algebraMap V (Localization.AtPrime p) a})
            (Localization.AtPrime p))
          (algebraMap V (Localization.AtPrime p) x))) at hres
    rw [hres]
    congr 1
    apply Subtype.ext
    calc
      (((⟨_, hCA (hbaseC x)⟩ : A) : UniformSpace.Completion K)) =
          ((algebraMap V (CompletionIntegers V K) x : CompletionIntegers V K) :
            UniformSpace.Completion K) := rfl
      _ = algebraMap K (UniformSpace.Completion K) (algebraMap V K x) :=
        coe_algebraMap_completionIntegers x
      _ = localizedAdicCompletionToFractionFieldCompletion
            (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
            (algebraMap (Localization.AtPrime p)
              (AdicCompletion
                (Ideal.span {algebraMap V (Localization.AtPrime p) a})
                (Localization.AtPrime p))
              (algebraMap V (Localization.AtPrime p) x)) :=
        (localizedAdicCompletionToFractionFieldCompletion_algebraMap_base
          (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj x).symm
      _ = ((eA (algebraMap (Localization.AtPrime p)
              (AdicCompletion
                (Ideal.span {algebraMap V (Localization.AtPrime p) a})
                (Localization.AtPrime p))
              (algebraMap V (Localization.AtPrime p) x)) : A) :
            UniformSpace.Completion K) :=
        (coe_localizedAdicCompletionValuationSubringEquiv_apply
          (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj _).symm
  have hbaseR (x : V) :
      (((algebraMap V (CompletionIntegers V K) x : CompletionIntegers V K) :
        UniformSpace.Completion K)) ∈ A.composite W := by
    apply ValuationSubring.mem_composite.mpr
    refine ⟨hCA (hbaseC x), ?_⟩
    rw [hbaseResidue x]
    exact localizedAtPrimeQuotientValuationSubring_algebraMap_mem
      (K := K) p hp ha0 (Ideal.Quotient.mk p x)
  have hRC : A.composite W ≤ C := by
    intro x hx
    obtain ⟨hxA, hxW⟩ := ValuationSubring.mem_composite.mp hx
    have hxW' :
        e.symm (IsLocalRing.residue A ⟨x, hxA⟩) ∈
          (valuation (V ⧸ p) p.ResidueField).valuationSubring :=
      (mem_localizedAtPrimeQuotientValuationSubring
        (K := K) p hp ha0 (IsLocalRing.residue A ⟨x, hxA⟩)).mp hxW
    obtain ⟨q, hq⟩ :=
      (ValuationRing.mem_integer_iff (V ⧸ p) p.ResidueField
        (e.symm (IsLocalRing.residue A ⟨x, hxA⟩))).mp hxW'
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective q
    let cv : CompletionIntegers V K := algebraMap V (CompletionIntegers V K) v
    have hcvC : (cv : UniformSpace.Completion K) ∈ C := cv.property
    have hcvA : (cv : UniformSpace.Completion K) ∈ A := hCA hcvC
    have hq' :
        e (algebraMap (V ⧸ p) p.ResidueField (Ideal.Quotient.mk p v)) =
          IsLocalRing.residue A ⟨x, hxA⟩ := by
      rw [hq, e.apply_symm_apply]
    have hresEq :
        IsLocalRing.residue A ⟨x, hxA⟩ =
          IsLocalRing.residue A ⟨(cv : UniformSpace.Completion K), hcvA⟩ :=
      hq'.symm.trans (hbaseResidue v).symm
    have hdiffA : x - (cv : UniformSpace.Completion K) ∈ A :=
      A.sub_mem hxA hcvA
    have hdiffMax :
        (⟨x - (cv : UniformSpace.Completion K), hdiffA⟩ : A) ∈
          IsLocalRing.maximalIdeal A := by
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      change IsLocalRing.residue A ⟨x, hxA⟩ -
        IsLocalRing.residue A ⟨(cv : UniformSpace.Completion K), hcvA⟩ = 0
      rw [hresEq, sub_self]
    have hdiffNon : x - (cv : UniformSpace.Completion K) ∈ A.nonunits :=
      ValuationSubring.coe_mem_nonunits_iff.mpr hdiffMax
    have hdiffC : x - (cv : UniformSpace.Completion K) ∈ C :=
      nonunits_subset_of_le hCA hdiffNon
    have hadd := C.add_mem _ _ hdiffC hcvC
    simpa only [sub_add_cancel] using hadd
  apply le_antisymm
  · intro x hxC
    letI : ValuationRing (CompletionIntegers V K) :=
      ValuationRing.instValuationRingInteger
        (Valued.v : Valuation (UniformSpace.Completion K) (ValueGroup V K))
    letI : IsLocalHom (algebraMap V (CompletionIntegers V K)) :=
      completionIntegers_algebraMap_isLocalHom a ha0 haMax
    let z : CompletionIntegers V K := ⟨x, hxC⟩
    obtain ⟨y, hy⟩ :=
      (completionIntegers_residueFieldMap_bijective
        (V := V) (K := K) a ha0 haMax).2
        (IsLocalRing.residue (CompletionIntegers V K) z)
    obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective y
    rw [IsLocalRing.ResidueField.map_residue] at hy
    let cv : CompletionIntegers V K := algebraMap V (CompletionIntegers V K) v
    have hdiffMax : z - cv ∈ IsLocalRing.maximalIdeal
        (CompletionIntegers V K) := by
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      rw [map_sub, hy, sub_self]
    have hdiffNon : x - (cv : UniformSpace.Completion K) ∈ C.nonunits := by
      let d : C := ⟨x - (cv : UniformSpace.Completion K),
        C.sub_mem hxC cv.property⟩
      change (d : UniformSpace.Completion K) ∈ C.nonunits
      apply ValuationSubring.coe_mem_nonunits_iff.mpr
      change z - cv ∈ IsLocalRing.maximalIdeal (CompletionIntegers V K)
      exact hdiffMax
    have hdiffR : x - (cv : UniformSpace.Completion K) ∈ A.composite W :=
      nonunits_subset_of_le hRC hdiffNon
    have hadd := (A.composite W).add_mem _ _ hdiffR (hbaseR v)
    change x - (cv : UniformSpace.Completion K) +
      (cv : UniformSpace.Completion K) ∈ A.composite W at hadd
    simpa only [sub_add_cancel] using hadd
  · exact hRC

/-- The distinguished prime of the completed valuation integers associated to
the completed localization at `p`. -/
noncomputable def completionIntegersLocalizedPrime
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let C := (Valued.v : Valuation (UniformSpace.Completion K)
      (ValueGroup V K)).valuationSubring
    Ideal C := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let C := (Valued.v : Valuation (UniformSpace.Completion K)
    (ValueGroup V K)).valuationSubring
  let hDisj :=
    primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
  let A := localizedAdicCompletionValuationSubring
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  exact C.idealOfLE A (completionIntegers_le_localizedAtPrime (K := K) p hp ha0)

noncomputable instance completionIntegersLocalizedPrime_isPrime
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    (completionIntegersLocalizedPrime (K := K) p hp ha0).IsPrime := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  unfold completionIntegersLocalizedPrime
  infer_instance

/-- Localizing the completed valuation integers at their distinguished prime
recovers the completed localization at `p`. -/
@[simp]
theorem completionIntegers_ofPrime_localizedPrime
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let C := (Valued.v : Valuation (UniformSpace.Completion K)
      (ValueGroup V K)).valuationSubring
    let hDisj :=
      primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
    let A := localizedAdicCompletionValuationSubring
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
    C.ofPrime (completionIntegersLocalizedPrime (K := K) p hp ha0) = A := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let C := (Valued.v : Valuation (UniformSpace.Completion K)
    (ValueGroup V K)).valuationSubring
  let hDisj :=
    primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
  let A := localizedAdicCompletionValuationSubring
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  change C.ofPrime (C.idealOfLE A
    (completionIntegers_le_localizedAtPrime (K := K) p hp ha0)) = A
  exact C.ofPrime_idealOfLE A
    (completionIntegers_le_localizedAtPrime (K := K) p hp ha0)

/-- The residue map from the completed valuation integers to the transported
quotient valuation ring. -/
noncomputable def completionIntegersCompositeResidue
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let C := (Valued.v : Valuation (UniformSpace.Completion K)
      (ValueGroup V K)).valuationSubring
    let W := localizedAtPrimeQuotientValuationSubring (K := K) p hp ha0
    C →+* W := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let C := (Valued.v : Valuation (UniformSpace.Completion K)
    (ValueGroup V K)).valuationSubring
  let hDisj :=
    primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
  let A := localizedAdicCompletionValuationSubring
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  let W := localizedAtPrimeQuotientValuationSubring (K := K) p hp ha0
  let hCA := completionIntegers_le_localizedAtPrime (K := K) p hp ha0
  exact ((IsLocalRing.residue A).comp (C.inclusion A hCA)).codRestrict W fun x ↦ by
    have hx : (x : UniformSpace.Completion K) ∈ A.composite W := by
      rw [← completionIntegersValuationSubring_eq_localizedAtPrime_composite
        (K := K) p hp ha0]
      exact x.property
    exact (ValuationSubring.mem_composite.mp hx).choose_spec

@[simp]
theorem completionIntegersCompositeResidue_apply
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V]
    (x :
      letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
      (Valued.v : Valuation (UniformSpace.Completion K)
        (ValueGroup V K)).valuationSubring) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let C := (Valued.v : Valuation (UniformSpace.Completion K)
      (ValueGroup V K)).valuationSubring
    let hDisj :=
      primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
    let A := localizedAdicCompletionValuationSubring
      (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
    let hCA := completionIntegers_le_localizedAtPrime (K := K) p hp ha0
    completionIntegersCompositeResidue (K := K) p hp ha0 x =
      IsLocalRing.residue A (C.inclusion A hCA x) := by
  rfl

/-- The completed composite residue map is onto the transported quotient
valuation ring. -/
theorem completionIntegersCompositeResidue_surjective
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    Function.Surjective (completionIntegersCompositeResidue (K := K) p hp ha0) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let C := (Valued.v : Valuation (UniformSpace.Completion K)
    (ValueGroup V K)).valuationSubring
  let hDisj :=
    primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
  let A := localizedAdicCompletionValuationSubring
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  let W := localizedAtPrimeQuotientValuationSubring (K := K) p hp ha0
  let hCA := completionIntegers_le_localizedAtPrime (K := K) p hp ha0
  let hEq := completionIntegersValuationSubring_eq_localizedAtPrime_composite
    (K := K) p hp ha0
  intro w
  obtain ⟨x, hx⟩ := A.compositeResidue_surjective W w
  have hxC : (x : UniformSpace.Completion K) ∈ C := by
    change (x : UniformSpace.Completion K) ∈
      (Valued.v : Valuation (UniformSpace.Completion K)
        (ValueGroup V K)).valuationSubring
    rw [hEq]
    exact x.property
  let y : C := ⟨(x : UniformSpace.Completion K), hxC⟩
  refine ⟨y, ?_⟩
  calc
    completionIntegersCompositeResidue (K := K) p hp ha0 y =
        A.compositeResidue W x := by
      apply Subtype.ext
      rfl
    _ = w := hx

/-- The kernel of the completed composite residue map is the distinguished
prime corresponding to the completed localization. -/
theorem ker_completionIntegersCompositeResidue
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    RingHom.ker (completionIntegersCompositeResidue (K := K) p hp ha0) =
      completionIntegersLocalizedPrime (K := K) p hp ha0 := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let C := (Valued.v : Valuation (UniformSpace.Completion K)
    (ValueGroup V K)).valuationSubring
  let hDisj :=
    primeCompl_disjoint_radical_span_singleton_of_isHausdorff (a := a) p hp
  let A := localizedAdicCompletionValuationSubring
    (Vₛ := Localization.AtPrime p) (K := K) p.primeCompl ha0 hDisj
  let hCA := completionIntegers_le_localizedAtPrime (K := K) p hp ha0
  change RingHom.ker (completionIntegersCompositeResidue (K := K) p hp ha0) =
    C.idealOfLE A hCA
  ext x
  rw [RingHom.mem_ker]
  constructor
  · intro hx
    have hxv := congrArg Subtype.val hx
    change IsLocalRing.residue A (C.inclusion A hCA x) = 0 at hxv
    change C.inclusion A hCA x ∈ IsLocalRing.maximalIdeal A
    exact (IsLocalRing.residue_eq_zero_iff _).mp hxv
  · intro hx
    change C.inclusion A hCA x ∈ IsLocalRing.maximalIdeal A at hx
    apply Subtype.ext
    change IsLocalRing.residue A (C.inclusion A hCA x) = 0
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hx

/-- Quotienting the completed valuation integers by their distinguished prime
recovers the transported quotient valuation ring. -/
noncomputable def completionIntegersQuotientEquiv
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let C := (Valued.v : Valuation (UniformSpace.Completion K)
      (ValueGroup V K)).valuationSubring
    let W := localizedAtPrimeQuotientValuationSubring (K := K) p hp ha0
    (C ⧸ completionIntegersLocalizedPrime (K := K) p hp ha0) ≃+* W := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  exact (Ideal.quotEquivOfEq
      (ker_completionIntegersCompositeResidue (K := K) p hp ha0).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (completionIntegersCompositeResidue_surjective (K := K) p hp ha0))

@[simp]
theorem completionIntegersQuotientEquiv_mk
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥)
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V]
    (x :
      letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
      (Valued.v : Valuation (UniformSpace.Completion K)
        (ValueGroup V K)).valuationSubring) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    completionIntegersQuotientEquiv (K := K) p hp ha0
        (Ideal.Quotient.mk
          (completionIntegersLocalizedPrime (K := K) p hp ha0) x) =
      completionIntegersCompositeResidue (K := K) p hp ha0 x := by
  rfl

end ValuationRing
