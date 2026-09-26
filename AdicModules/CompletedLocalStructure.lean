/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.CompletedIntegers
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Local structure of principal-adic completions of valuation rings

This file transports the algebraic structure of the completed valuation integers across the
principal-adic comparison. It also identifies the completed fraction field and proves that the
canonical map is local and induces an isomorphism on residue fields when the generator lies in the
maximal ideal.
-/

@[expose] public section

set_option linter.style.haveILetI false

open scoped Topology

noncomputable section

universe u v

namespace ValuationRing

variable {V : Type u} {K : Type v} [CommRing V] [IsDomain V]
  [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

/-- A separated principal-adic completion of a valuation ring is a domain. -/
theorem principalAdicCompletion_isDomain
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    IsDomain (AdicCompletion (Ideal.span {a}) V) :=
  ((principalAdicCompletionRingEquiv (K := K) a ha0) :
    AdicCompletion (Ideal.span {a}) V ≃* CompletionIntegers V K).isDomain _

/-- A separated principal-adic completion of a valuation ring is a valuation ring. -/
theorem principalAdicCompletion_isValuationRing
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isDomain K a ha0
    ValuationRing (AdicCompletion (Ideal.span {a}) V) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
    principalAdicCompletion_isDomain K a ha0
  letI : ValuationRing (CompletionIntegers V K) :=
    ValuationRing.instValuationRingInteger
      (Valued.v : Valuation (UniformSpace.Completion K) (ValueGroup V K))
  exact Function.Surjective.valuationRing
    (principalAdicCompletionRingEquiv (K := K) a ha0).symm.toRingHom
    (principalAdicCompletionRingEquiv (K := K) a ha0).symm.surjective

/-- The algebra structure on the completed fraction field induced by the principal-adic
comparison and the inclusion of the completed valuation integers. -/
@[instance_reducible]
noncomputable def principalAdicCompletionFractionFieldAlgebra
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    Algebra (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  exact ((algebraMap (CompletionIntegers V K) (UniformSpace.Completion K)).comp
    (principalAdicCompletionRingEquiv (K := K) a ha0).toRingHom).toAlgebra

/-- The induced fraction-field algebra map is the principal-adic comparison followed by the
inclusion of the completed valuation integers. -/
@[simp]
theorem principalAdicCompletionFractionFieldAlgebra_algebraMap
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V]
    (x : AdicCompletion (Ideal.span {a}) V) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    letI : Algebra (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K) :=
      principalAdicCompletionFractionFieldAlgebra a ha0
    algebraMap (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K) x =
      algebraMap (CompletionIntegers V K) (UniformSpace.Completion K)
        (principalAdicCompletionRingEquiv (K := K) a ha0 x) :=
  rfl

/-- The induced fraction-field algebra map agrees with the original fraction-field embedding on
the valuation ring. -/
theorem principalAdicCompletionFractionFieldAlgebra_algebraMap_base
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (x : V) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    letI : Algebra (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K) :=
      principalAdicCompletionFractionFieldAlgebra a ha0
    algebraMap (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K)
        (algebraMap V (AdicCompletion (Ideal.span {a}) V) x) =
      algebraMap K (UniformSpace.Completion K) (algebraMap V K x) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  letI : Algebra (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K) :=
    principalAdicCompletionFractionFieldAlgebra a ha0
  rw [principalAdicCompletionFractionFieldAlgebra_algebraMap,
    principalAdicCompletionRingEquiv_algebraMap]
  exact coe_algebraMap_completionIntegers x

/-- The completion of the fraction field is a fraction field of the separated principal-adic
completion. -/
theorem principalAdicCompletion_isFractionRing
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    letI : Algebra (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K) :=
      principalAdicCompletionFractionFieldAlgebra a ha0
    IsFractionRing (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  letI : Algebra (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K) :=
    principalAdicCompletionFractionFieldAlgebra a ha0
  letI : IsFractionRing (CompletionIntegers V K) (UniformSpace.Completion K) :=
    ValuationRing.instIsFractionRingInteger
      (Valued.v : Valuation (UniformSpace.Completion K) (ValueGroup V K))
  exact IsFractionRing.of_ringEquiv_left
    (principalAdicCompletionRingEquiv (K := K) a ha0) (fun _ ↦ rfl)

/-- The maximal ideal of a separated principal-adic completion is the extension of the maximal
ideal of the valuation ring, provided the adic generator lies in that maximal ideal. -/
theorem principalAdicCompletion_maximalIdeal_eq_map
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
    [IsHausdorff (Ideal.span {a}) V] :
    letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isValuationRing K a ha0
    IsLocalRing.maximalIdeal (AdicCompletion (Ideal.span {a}) V) =
      (IsLocalRing.maximalIdeal V).map
        (algebraMap V (AdicCompletion (Ideal.span {a}) V)) := by
  letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
    principalAdicCompletion_isDomain K a ha0
  letI : ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
    principalAdicCompletion_isValuationRing K a ha0
  exact (IsLocalRing.eq_maximalIdeal
    (AdicCompletion.isMaximal_map_of_le (Ideal.span {a})
      (IsLocalRing.maximalIdeal V) ((Ideal.span_singleton_le_iff_mem _).mpr ha)
      (Submodule.fg_span_singleton a))).symm

/-- A separated principal-adic completion is not a field when the nonzero generator lies in the
maximal ideal. -/
theorem principalAdicCompletion_not_isField
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
    [IsHausdorff (Ideal.span {a}) V] :
    letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isValuationRing K a ha0
    ¬ IsField (AdicCompletion (Ideal.span {a}) V) := by
  let A := AdicCompletion (Ideal.span {a}) V
  letI : IsDomain A := principalAdicCompletion_isDomain K a ha0
  letI : ValuationRing A := principalAdicCompletion_isValuationRing K a ha0
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  have hVK : algebraMap V K a ≠ 0 := by
    simpa using (IsFractionRing.injective V K).ne ha0
  have hK : algebraMap K (UniformSpace.Completion K) (algebraMap V K a) ≠ 0 :=
    (RingHom.injective (algebraMap K (UniformSpace.Completion K))).ne hVK
  have hC : algebraMap V (CompletionIntegers V K) a ≠ 0 := by
    intro h
    apply hK
    simpa [coe_algebraMap_completionIntegers] using
      congrArg (fun x : CompletionIntegers V K ↦ (x : UniformSpace.Completion K)) h
  have hA : algebraMap V A a ≠ 0 := by
    intro h
    apply hC
    simpa [A, principalAdicCompletionRingEquiv_algebraMap] using
      congrArg (principalAdicCompletionRingEquiv (K := K) a ha0) h
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  intro hfield
  have hmem : algebraMap V A a ∈ IsLocalRing.maximalIdeal A := by
    rw [principalAdicCompletion_maximalIdeal_eq_map K a ha0 ha]
    exact Ideal.mem_map_of_mem _ ha
  rw [hfield] at hmem
  exact hA (by simpa using hmem)

/-- The canonical map to a separated principal-adic completion is local when the generator lies
in the maximal ideal. -/
theorem principalAdicCompletion_algebraMap_isLocalHom
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
    [IsHausdorff (Ideal.span {a}) V] :
    letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isValuationRing K a ha0
    IsLocalHom (algebraMap V (AdicCompletion (Ideal.span {a}) V)) := by
  letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
    principalAdicCompletion_isDomain K a ha0
  letI : ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
    principalAdicCompletion_isValuationRing K a ha0
  apply ((IsLocalRing.local_hom_TFAE _).out 3 1).mp
  exact le_of_eq (principalAdicCompletion_maximalIdeal_eq_map K a ha0 ha).symm

/-- The canonical map to a separated principal-adic completion induces a bijection on residue
fields when the generator lies in the maximal ideal. -/
theorem principalAdicCompletion_residueFieldMap_bijective
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
    [IsHausdorff (Ideal.span {a}) V] :
    letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isValuationRing K a ha0
    letI : IsLocalHom (algebraMap V (AdicCompletion (Ideal.span {a}) V)) :=
      principalAdicCompletion_algebraMap_isLocalHom K a ha0 ha
    Function.Bijective (IsLocalRing.ResidueField.map
      (algebraMap V (AdicCompletion (Ideal.span {a}) V))) := by
  let I : Ideal V := Ideal.span {a}
  let A := AdicCompletion I V
  letI : IsDomain A := principalAdicCompletion_isDomain K a ha0
  letI : ValuationRing A := principalAdicCompletion_isValuationRing K a ha0
  letI : IsLocalHom (algebraMap V A) :=
    principalAdicCompletion_algebraMap_isLocalHom K a ha0 ha
  have hmax : IsLocalRing.maximalIdeal A =
      (IsLocalRing.maximalIdeal V).map (algebraMap V A) :=
    principalAdicCompletion_maximalIdeal_eq_map K a ha0 ha
  refine ⟨RingHom.injective _, fun x ↦ ?_⟩
  rcases IsLocalRing.residue_surjective x with ⟨y, hy⟩
  rcases Ideal.Quotient.mk_surjective (y.1 1) with ⟨z, hz⟩
  use IsLocalRing.residue V z
  rw [IsLocalRing.ResidueField.map_residue, ← hy]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [hmax, ← Submodule.restrictScalars_mem V, ← Ideal.smul_top_eq_map]
  have hI : (algebraMap V A) z - y ∈ I ^ 1 • (⊤ : Submodule V A) := by
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.pow_smul_top_eq_ker_eval
      (Submodule.fg_span_singleton a)]
    simpa [AdicCompletion.eval, sub_eq_zero, I, A] using hz
  exact (Submodule.smul_mono_left (by simpa [I] using
    (Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal V)).mpr ha)) hI

end ValuationRing
