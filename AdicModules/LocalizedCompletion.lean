/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.LocalizedFiltration
public import AdicModules.CompletedIntegers
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Localized principal-adic completions in a common completed fraction field

For a localization of a valuation ring whose denominators avoid the radical of a principal
ideal, this file identifies the localized adic uniformity with the one induced from the original
fraction field. It then extends the localization embedding to an injective map from the localized
principal-adic completion into the completed fraction field and proves that the latter is its
fraction field.
-/

@[expose] public section

set_option linter.style.haveILetI false

open scoped Topology
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

noncomputable section

universe u v w

namespace ValuationRing

variable {V : Type u} {Vₛ : Type v} {K : Type w}
  [CommRing V] [IsDomain V] [ValuationRing V]
  [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K]
  (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K]

omit [IsDomain V] [ValuationRing V] in
private lemma mapToFractionRing_injective
    (hS : S ≤ nonZeroDivisors V) :
    Function.Injective (Localization.mapToFractionRing K S Vₛ hS) := by
  change Function.Injective
    (IsLocalization.lift (Localization.map_isUnit_of_le K S hS))
  rw [IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    exact congrArg (algebraMap V K) (IsLocalization.injective Vₛ hS h)
  · intro h
    exact congrArg (algebraMap V Vₛ) (IsFractionRing.injective V K h)

omit [IsDomain V] [ValuationRing V] in
private lemma preimage_powerImage_mapToFractionRing
    (hS : S ≤ nonZeroDivisors V) (a : V) (n : ℕ) :
    (Localization.mapToFractionRing K S Vₛ hS) ⁻¹'
        (algebraMap V K '' (↑((Ideal.span {a}) ^ n) : Set V)) =
      (localizedPowerImage (V := V) (Vₛ := Vₛ) a n : Set Vₛ) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    apply mapToFractionRing_injective (K := K) S hS
    change (Localization.mapToFractionRing K S Vₛ hS)
      (algebraMap V Vₛ y) = (Localization.mapToFractionRing K S Vₛ hS) x
    rw [AlgHom.commutes]
    exact hxy
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    simp

private lemma image_power_eq_closedBall
    (a : V) (n : ℕ) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    algebraMap V K '' (↑((Ideal.span {a}) ^ n) : Set V) =
      {x : K | Valued.v.restrict x ≤ Valued.v.restrict (algebraMap V K (a ^ n))} := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Ideal.span_singleton_pow] at hy
    change y ∈ (Ideal.span {a ^ n} : Ideal V) at hy
    have hy' : (valuation V K) (algebraMap V K y) ≤
        (valuation V K) (algebraMap V K (a ^ n)) :=
      (Set.ext_iff.mp
        ((integers V K).coe_span_singleton_eq_setOfPred_le_v_algebraMap (a ^ n)) y).mp hy
    exact (valuation V K).restrict_le_iff.mpr hy'
  · intro hx
    have hx' : (valuation V K) x ≤ (valuation V K) (algebraMap V K (a ^ n)) :=
      (valuation V K).restrict_le_iff.mp hx
    have hpow : algebraMap V K (a ^ n) ∈ (valuation V K).integer :=
      (ValuationRing.mem_integer_iff V K _).2 ⟨a ^ n, rfl⟩
    change (valuation V K) (algebraMap V K (a ^ n)) ≤ 1 at hpow
    have hxint : x ∈ (valuation V K).integer := hx'.trans hpow
    obtain ⟨y, hyx⟩ := (ValuationRing.mem_integer_iff V K x).1 hxint
    refine ⟨y, ?_, hyx⟩
    rw [Ideal.span_singleton_pow]
    change y ∈ (Ideal.span {a ^ n} : Ideal V)
    apply (Set.ext_iff.mp
      ((integers V K).coe_span_singleton_eq_setOfPred_le_v_algebraMap (a ^ n)) y).mpr
    simpa [hyx] using hx'

private lemma image_power_mem_nhds
    {a : V} (ha0 : a ≠ 0) (n : ℕ) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    algebraMap V K '' (↑((Ideal.span {a}) ^ n) : Set V) ∈ nhds (0 : K) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  rw [image_power_eq_closedBall (K := K) a n]
  rw [mem_nhds_iff]
  refine ⟨_, Set.Subset.rfl, Valued.isOpen_closedBall K ?_, ?_⟩
  · change (valuation V K).restrict (algebraMap V K (a ^ n)) ≠ 0
    rw [ne_eq, (valuation V K).restrict_eq_zero_iff]
    simp [ha0]
  · simp

/-- The canonical embedding of a localization into the fraction field induces the localized
principal-adic uniformity when the denominators avoid the radical of the generator. -/
theorem isUniformInducing_mapToFractionRing
    {a : V} (ha0 : a ≠ 0)
    (hSrad : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    letI : WithIdeal Vₛ := ⟨Ideal.span {algebraMap V Vₛ a}⟩
    IsUniformInducing (Localization.mapToFractionRing K S Vₛ
      (le_nonZeroDivisors_of_noZeroDivisors (fun h0 ↦
        Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)))) := by
  have hS0 : (0 : V) ∉ S := by
    intro h0
    exact Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
  let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  letI : WithIdeal Vₛ := ⟨Ideal.span {algebraMap V Vₛ a}⟩
  let f := Localization.mapToFractionRing K S Vₛ hSnzd
  apply AddMonoidHom.isUniformInducing_of_isInducing
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  let hsource := hasBasis_nhds_zero_adic_localizedPowerImage S Vₛ hSrad
  let htarget : (nhds (0 : K)).HasBasis
      (fun U : Set K ↦ U ∈ nhds (0 : K) ∧ True) id :=
    Filter.hasBasis_self.mpr fun U hU ↦ ⟨U, hU, trivial, Set.Subset.rfl⟩
  apply hsource.ext (htarget.comap f)
  · intro n _
    refine ⟨algebraMap V K '' (↑((Ideal.span {a}) ^ n) : Set V),
      ⟨image_power_mem_nhds (K := K) ha0 n, trivial⟩, ?_⟩
    simp only [id_eq, f]
    rw [preimage_powerImage_mapToFractionRing (K := K) S hSnzd a n]
  · intro U hU
    letI : Valued V (ValueGroup V K) :=
      Valued.mk' ((valuation V K).comap (algebraMap V K))
    have hVK : IsUniformInducing (algebraMap V K) :=
      isUniformInducing_algebraMap_fractionRing (V := V) (K := K)
    have hU0 : U ∈ nhds ((algebraMap V K) (0 : V)) := by simpa using hU.1
    have hpreValued : (algebraMap V K) ⁻¹' U ∈ nhds (0 : V) :=
      hVK.uniformContinuous.continuous.continuousAt hU0
    have hI := isAdic_valuationTopology_span_singleton
      (V := V) (K := K) (a := a) ha0
    have hpreAdic : (algebraMap V K) ⁻¹' U ∈
        @nhds V (Ideal.span {a}).adicTopology (0 : V) := by
      rw [← hI]
      exact hpreValued
    obtain ⟨n, -, hn⟩ := (Ideal.hasBasis_nhds_zero_adic
      (Ideal.span {a})).mem_iff.mp hpreAdic
    refine ⟨n, trivial, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change f (algebraMap V Vₛ y) ∈ U
    rw [f.commutes]
    exact hn hy

/-- The completion of a localization embeds canonically into the completion of the original
fraction field. -/
noncomputable def localizedAdicCompletionToFractionFieldCompletion
    {a : V} (ha0 : a ≠ 0)
    (hSrad : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ →+*
      UniformSpace.Completion K := by
  have hS0 : (0 : V) ∉ S := by
    intro h0
    exact Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
  let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let I : Ideal Vₛ := Ideal.span {algebraMap V Vₛ a}
  letI : WithIdeal Vₛ := ⟨I⟩
  letI : WithIdeal (AdicCompletion I Vₛ) :=
    ⟨I.map (algebraMap Vₛ (AdicCompletion I Vₛ))⟩
  let hfg : I.FG := Submodule.fg_span_singleton _
  let f : Vₛ →+* UniformSpace.Completion K :=
    UniformSpace.Completion.coeRingHom.comp
      (Localization.mapToFractionRing K S Vₛ hSnzd).toRingHom
  have hf : UniformContinuous f :=
    ((UniformSpace.Completion.isUniformInducing_coe K).comp
      (isUniformInducing_mapToFractionRing (K := K) S ha0 hSrad)).uniformContinuous
  exact IsDenseInducing.extendRingHom
    (AdicCompletion.isUniformInducing_algebraMap I rfl hfg)
    (AdicCompletion.denseRange_algebraMap I rfl hfg) hf

/-- The completion embedding extends the canonical localization map into the fraction field. -/
theorem localizedAdicCompletionToFractionFieldCompletion_algebraMap
    {a : V} (ha0 : a ≠ 0)
    (hSrad : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    [IsHausdorff (Ideal.span {a}) V] (x : Vₛ) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    localizedAdicCompletionToFractionFieldCompletion (K := K) S ha0 hSrad
        (algebraMap Vₛ (AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ) x) =
      algebraMap K (UniformSpace.Completion K)
        (Localization.mapToFractionRing K S Vₛ
          (le_nonZeroDivisors_of_noZeroDivisors (fun h0 ↦
            Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _))) x) := by
  have hS0 : (0 : V) ∉ S := by
    intro h0
    exact Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
  let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let I : Ideal Vₛ := Ideal.span {algebraMap V Vₛ a}
  letI : WithIdeal Vₛ := ⟨I⟩
  letI : WithIdeal (AdicCompletion I Vₛ) :=
    ⟨I.map (algebraMap Vₛ (AdicCompletion I Vₛ))⟩
  let hfg : I.FG := Submodule.fg_span_singleton _
  let f : Vₛ →+* UniformSpace.Completion K :=
    UniformSpace.Completion.coeRingHom.comp
      (Localization.mapToFractionRing K S Vₛ hSnzd).toRingHom
  have hf : UniformContinuous f :=
    ((UniformSpace.Completion.isUniformInducing_coe K).comp
      (isUniformInducing_mapToFractionRing (K := K) S ha0 hSrad)).uniformContinuous
  change (IsDenseInducing.extendRingHom
      (AdicCompletion.isUniformInducing_algebraMap I rfl hfg)
      (AdicCompletion.denseRange_algebraMap I rfl hfg) hf)
      (algebraMap Vₛ (AdicCompletion I Vₛ) x) = _
  exact ((AdicCompletion.isUniformInducing_algebraMap I rfl hfg).isDenseInducing
    (AdicCompletion.denseRange_algebraMap I rfl hfg)).extend_eq hf.continuous x

/-- On the original valuation ring, the localized completion embedding is the canonical map to
the completed fraction field. -/
theorem localizedAdicCompletionToFractionFieldCompletion_algebraMap_base
    {a : V} (ha0 : a ≠ 0)
    (hSrad : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    [IsHausdorff (Ideal.span {a}) V] (x : V) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    localizedAdicCompletionToFractionFieldCompletion (K := K) S ha0 hSrad
        (algebraMap Vₛ (AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ)
          (algebraMap V Vₛ x)) =
      algebraMap K (UniformSpace.Completion K) (algebraMap V K x) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  rw [localizedAdicCompletionToFractionFieldCompletion_algebraMap]
  simp

/-- The canonical map from the localized principal-adic completion to the completed fraction
field is injective. -/
theorem localizedAdicCompletionToFractionFieldCompletion_injective
    {a : V} (ha0 : a ≠ 0)
    (hSrad : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    Function.Injective
      (localizedAdicCompletionToFractionFieldCompletion (Vₛ := Vₛ) (K := K)
        S ha0 hSrad) := by
  have hS0 : (0 : V) ∉ S := by
    intro h0
    exact Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
  let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let I : Ideal Vₛ := Ideal.span {algebraMap V Vₛ a}
  letI : WithIdeal Vₛ := ⟨I⟩
  letI : WithIdeal (AdicCompletion I Vₛ) :=
    ⟨I.map (algebraMap Vₛ (AdicCompletion I Vₛ))⟩
  let hfg : I.FG := Submodule.fg_span_singleton _
  let P := AdicCompletion.abstractCompletion I rfl hfg
  letI : CompleteSpace (AdicCompletion I Vₛ) := P.complete
  letI : T0Space (AdicCompletion I Vₛ) := P.separation
  let f : Vₛ →+* UniformSpace.Completion K :=
    UniformSpace.Completion.coeRingHom.comp
      (Localization.mapToFractionRing K S Vₛ hSnzd).toRingHom
  have hf : IsUniformInducing f :=
    (UniformSpace.Completion.isUniformInducing_coe K).comp
      (isUniformInducing_mapToFractionRing (K := K) S ha0 hSrad)
  have hext : IsUniformInducing
      (((AdicCompletion.isUniformInducing_algebraMap I rfl hfg).isDenseInducing
        (AdicCompletion.denseRange_algebraMap I rfl hfg)).extend f) :=
    ((AdicCompletion.isUniformInducing_algebraMap I rfl hfg).isDenseInducing
      (AdicCompletion.denseRange_algebraMap I rfl hfg)).isUniformInducing_extend
        (AdicCompletion.isUniformInducing_algebraMap I rfl hfg) hf
  apply hext.injective

/-- Every completed valuation integer lies in the image of the localized completion inside the
common completed fraction field. -/
theorem completionIntegers_mem_range_localizedAdicCompletion
    {a : V} (ha0 : a ≠ 0)
    (hSrad : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    [IsHausdorff (Ideal.span {a}) V] (z : CompletionIntegers V K) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    (z : UniformSpace.Completion K) ∈ Set.range
      (localizedAdicCompletionToFractionFieldCompletion (Vₛ := Vₛ) (K := K)
        S ha0 hSrad) := by
  have hS0 : (0 : V) ∉ S := by
    intro h0
    exact Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
  let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let I : Ideal Vₛ := Ideal.span {algebraMap V Vₛ a}
  letI : WithIdeal Vₛ := ⟨I⟩
  letI : WithIdeal (AdicCompletion I Vₛ) :=
    ⟨I.map (algebraMap Vₛ (AdicCompletion I Vₛ))⟩
  let hfg : I.FG := Submodule.fg_span_singleton _
  let P := AdicCompletion.abstractCompletion I rfl hfg
  letI : CompleteSpace (AdicCompletion I Vₛ) := P.complete
  let f : Vₛ →+* UniformSpace.Completion K :=
    UniformSpace.Completion.coeRingHom.comp
      (Localization.mapToFractionRing K S Vₛ hSnzd).toRingHom
  let g := localizedAdicCompletionToFractionFieldCompletion
    (Vₛ := Vₛ) (K := K) S ha0 hSrad
  have hf : IsUniformInducing f :=
    (UniformSpace.Completion.isUniformInducing_coe K).comp
      (isUniformInducing_mapToFractionRing (K := K) S ha0 hSrad)
  have hg : IsUniformInducing g := by
    change IsUniformInducing
      (((AdicCompletion.isUniformInducing_algebraMap I rfl hfg).isDenseInducing
        (AdicCompletion.denseRange_algebraMap I rfl hfg)).extend f)
    exact ((AdicCompletion.isUniformInducing_algebraMap I rfl hfg).isDenseInducing
      (AdicCompletion.denseRange_algebraMap I rfl hfg)).isUniformInducing_extend
        (AdicCompletion.isUniformInducing_algebraMap I rfl hfg) hf
  refine DenseRange.induction_on
    (p := fun z : CompletionIntegers V K ↦
      (z : UniformSpace.Completion K) ∈ Set.range g)
    (denseRange_algebraMap_completionIntegers (V := V) (K := K)) z ?_ ?_
  · exact hg.isComplete_range.isClosed.preimage continuous_subtype_val
  · intro x
    refine ⟨algebraMap Vₛ (AdicCompletion I Vₛ) (algebraMap V Vₛ x), ?_⟩
    rw [localizedAdicCompletionToFractionFieldCompletion_algebraMap_base]
    exact (coe_algebraMap_completionIntegers (K := K) x).symm

/-- The algebra structure on the common completed fraction field induced by the localized
completion embedding. -/
@[instance_reducible]
noncomputable def localizedAdicCompletionFractionFieldAlgebra
    {a : V} (ha0 : a ≠ 0)
    (hSrad : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    Algebra (AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ)
      (UniformSpace.Completion K) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  exact (localizedAdicCompletionToFractionFieldCompletion
    (Vₛ := Vₛ) (K := K) S ha0 hSrad).toAlgebra

/-- The common completed fraction field is a fraction field of the localized principal-adic
completion. -/
theorem localizedAdicCompletion_isFractionRing
    {a : V} (ha0 : a ≠ 0)
    (hSrad : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    letI : Algebra (AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ)
        (UniformSpace.Completion K) :=
      localizedAdicCompletionFractionFieldAlgebra (K := K) S ha0 hSrad
    IsFractionRing (AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ)
      (UniformSpace.Completion K) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let I : Ideal Vₛ := Ideal.span {algebraMap V Vₛ a}
  letI : Algebra (AdicCompletion I Vₛ) (UniformSpace.Completion K) :=
    localizedAdicCompletionFractionFieldAlgebra (K := K) S ha0 hSrad
  have hinj : Function.Injective
      (algebraMap (AdicCompletion I Vₛ) (UniformSpace.Completion K)) :=
    localizedAdicCompletionToFractionFieldCompletion_injective
      (Vₛ := Vₛ) (K := K) S ha0 hSrad
  letI : FaithfulSMul (AdicCompletion I Vₛ) (UniformSpace.Completion K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  apply IsFractionRing.of_field
  intro z
  letI : IsFractionRing (CompletionIntegers V K) (UniformSpace.Completion K) :=
    ValuationRing.instIsFractionRingInteger
      (Valued.v : Valuation (UniformSpace.Completion K) (ValueGroup V K))
  obtain ⟨x, y, _hy, hxy⟩ := IsFractionRing.div_surjective (CompletionIntegers V K) z
  obtain ⟨x', hx'⟩ := completionIntegers_mem_range_localizedAdicCompletion
    (Vₛ := Vₛ) (K := K) S ha0 hSrad x
  obtain ⟨y', hy'⟩ := completionIntegers_mem_range_localizedAdicCompletion
    (Vₛ := Vₛ) (K := K) S ha0 hSrad y
  refine ⟨x', y', ?_⟩
  change z =
    localizedAdicCompletionToFractionFieldCompletion (Vₛ := Vₛ) (K := K)
        S ha0 hSrad x' /
      localizedAdicCompletionToFractionFieldCompletion (Vₛ := Vₛ) (K := K)
        S ha0 hSrad y'
  rw [hx', hy']
  change (x : UniformSpace.Completion K) / (y : UniformSpace.Completion K) = z at hxy
  exact hxy.symm

end ValuationRing
