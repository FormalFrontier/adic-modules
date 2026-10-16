/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules
public import Mathlib.Algebra.Field.Rat
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Residues under the completed-localization comparison

The residue-field comparison sends the residue of a localization element to the residue of its
canonical image in the completed-localization valuation subring.

For the units identity localization of `PowerSeries ℚ`, this comparison kills the residue of
`X` and distinguishes the residues of one and zero. Its source residue field uses the local
structure supplied by the public localization valuation-ring construction.

The proofs reuse Mathlib's description of the power-series maximal ideal and its separated
filtration, and the residue-comparison API of AdicModules.

## References

The units-localization inputs use Mathlib's power-series maximal ideal and
separated filtration. The canonical local structure and residue-congruence
criterion come from `AdicModules.LocalizedResidueField` and its valuation-subring
realization.
-/

set_option warningAsError true
set_option linter.style.haveILetI false

open scoped Topology

noncomputable section

universe u v w

namespace ValuationRing

variable {V : Type u} {Vₛ : Type v} {K : Type w}
  [CommRing V] [IsDomain V] [ValuationRing V]
  [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K]
  (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K]
  {a : V} (ha0 : a ≠ 0)
  (hSrad : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
  [IsHausdorff (Ideal.span {a}) V]

private noncomputable def residueEquivalenceClient :
    let hS0 : (0 : V) ∉ S := fun h0 ↦
      Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
    let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
    letI : IsDomain Vₛ := IsLocalization.isDomain_of_le_nonZeroDivisors Vₛ hSnzd
    letI : ValuationRing Vₛ := localization_isValuationRing (Vₛ := Vₛ) S hSnzd
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    IsLocalRing.ResidueField Vₛ ≃+*
      IsLocalRing.ResidueField
        (localizedAdicCompletionValuationSubring (Vₛ := Vₛ) (K := K)
          S ha0 hSrad) :=
  localizedAdicCompletionResidueFieldEquiv (Vₛ := Vₛ) (K := K)
    S ha0 hSrad

private theorem residueMapClient (x : Vₛ) :
    let hS0 : (0 : V) ∉ S := fun h0 ↦
      Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
    let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
    letI : IsDomain Vₛ := IsLocalization.isDomain_of_le_nonZeroDivisors Vₛ hSnzd
    letI : ValuationRing Vₛ := localization_isValuationRing (Vₛ := Vₛ) S hSnzd
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    localizedAdicCompletionResidueFieldEquiv (Vₛ := Vₛ) (K := K)
        S ha0 hSrad (IsLocalRing.residue Vₛ x) =
      IsLocalRing.residue
        (localizedAdicCompletionValuationSubring (Vₛ := Vₛ) (K := K)
          S ha0 hSrad)
        (localizedAdicCompletionValuationSubringEquiv (Vₛ := Vₛ) (K := K)
          S ha0 hSrad
          (algebraMap Vₛ (AdicCompletion
            (Ideal.span {algebraMap V Vₛ a}) Vₛ) x)) :=
  localizedAdicCompletionResidueFieldEquiv_residue (Vₛ := Vₛ) (K := K)
    S ha0 hSrad x

/-- The residue comparison distinguishes the residues of one and zero. -/
private theorem residueComparisonSeparatesOneZero :
    let hS0 : (0 : V) ∉ S := fun h0 ↦
      Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
    let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
    letI : IsDomain Vₛ := IsLocalization.isDomain_of_le_nonZeroDivisors Vₛ hSnzd
    letI : ValuationRing Vₛ := localization_isValuationRing (Vₛ := Vₛ) S hSnzd
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    localizedAdicCompletionResidueFieldEquiv (Vₛ := Vₛ) (K := K) S ha0 hSrad
        (IsLocalRing.residue Vₛ 1) ≠
      localizedAdicCompletionResidueFieldEquiv (Vₛ := Vₛ) (K := K) S ha0 hSrad
        (IsLocalRing.residue Vₛ 0) := by
  have hS0 : (0 : V) ∉ S := fun h0 ↦
    Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
  let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
  letI : IsDomain Vₛ := IsLocalization.isDomain_of_le_nonZeroDivisors Vₛ hSnzd
  letI : ValuationRing Vₛ := localization_isValuationRing (Vₛ := Vₛ) S hSnzd
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  change localizedAdicCompletionResidueFieldEquiv (Vₛ := Vₛ) (K := K) S ha0 hSrad
      (IsLocalRing.residue Vₛ 1) ≠
    localizedAdicCompletionResidueFieldEquiv (Vₛ := Vₛ) (K := K) S ha0 hSrad
      (IsLocalRing.residue Vₛ 0)
  intro h
  have hmem := (localizedAdicCompletionResidueFieldEquiv_eq_iff
    (Vₛ := Vₛ) (K := K) S ha0 hSrad 1 0).1 h
  simp [IsLocalRing.mem_maximalIdeal] at hmem

end ValuationRing

namespace ValuationRing

/-- In the units localization of `PowerSeries ℚ`, the completed residue comparison kills
`X` but distinguishes one from zero, using its canonical localization local-ring structure. -/
public theorem powerSeries_unitsLocalizedResidueField_X_eq_zero_one_ne_zero :
    let hUnits : Disjoint (IsUnit.submonoid (PowerSeries ℚ) : Set (PowerSeries ℚ))
        ((Ideal.span {(PowerSeries.X : PowerSeries ℚ)}).radical : Set (PowerSeries ℚ)) := by
      rw [Set.disjoint_left]
      intro s hs hr
      have hnot : ¬ IsUnit s := by
        simpa only [← PowerSeries.maximalIdeal_eq_span_X (k := ℚ),
          IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using
          (PowerSeries.span_X_isPrime (R := ℚ)).isRadical hr
      exact hnot hs
    let hSep : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) :=
      Eq.mp
        (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ IsHausdorff I (PowerSeries ℚ))
          (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
        (inferInstance :
          IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ))
    let hS0 : (0 : PowerSeries ℚ) ∉ IsUnit.submonoid (PowerSeries ℚ) := fun h0 ↦
      Set.disjoint_left.1 hUnits h0 (Ideal.zero_mem _)
    let hSnzd : IsUnit.submonoid (PowerSeries ℚ) ≤ nonZeroDivisors (PowerSeries ℚ) :=
      le_nonZeroDivisors_of_noZeroDivisors hS0
    let hDomain := IsLocalization.isDomain_of_le_nonZeroDivisors (PowerSeries ℚ) hSnzd
    let hValuation : @ValuationRing (PowerSeries ℚ) _ hDomain :=
      localization_isValuationRing (Vₛ := PowerSeries ℚ)
        (IsUnit.submonoid (PowerSeries ℚ)) hSnzd
    let hLocal := @ValuationRing.isLocalRing (PowerSeries ℚ) _
      hDomain.toNontrivial hValuation.toPreValuationRing
    let e := @localizedAdicCompletionResidueFieldEquiv
      (PowerSeries ℚ) (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))
      _ _ _ _ _ _ _ (IsUnit.submonoid (PowerSeries ℚ)) _ _
      PowerSeries.X (PowerSeries.X_ne_zero (R := ℚ)) hUnits hSep
    e (@IsLocalRing.residue (PowerSeries ℚ) _ hLocal PowerSeries.X) =
        e (@IsLocalRing.residue (PowerSeries ℚ) _ hLocal 0) ∧
      e (@IsLocalRing.residue (PowerSeries ℚ) _ hLocal 1) ≠
        e (@IsLocalRing.residue (PowerSeries ℚ) _ hLocal 0) := by
  intro hUnits hSep hS0 hSnzd hDomain hValuation hLocal e
  letI : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) := hSep
  have hX : PowerSeries.X ∈ @IsLocalRing.maximalIdeal (PowerSeries ℚ) _ hLocal := by
    rw [PowerSeries.maximalIdeal_eq_span_X (k := ℚ)]
    exact Ideal.subset_span (Set.mem_singleton PowerSeries.X)
  constructor
  · apply (localizedAdicCompletionResidueFieldEquiv_eq_iff
      (Vₛ := PowerSeries ℚ) (K := FractionRing (PowerSeries ℚ))
      (IsUnit.submonoid (PowerSeries ℚ)) (PowerSeries.X_ne_zero (R := ℚ)) hUnits
      PowerSeries.X 0).2
    simpa only [sub_zero] using hX
  · intro h
    have hmem := (localizedAdicCompletionResidueFieldEquiv_eq_iff
      (Vₛ := PowerSeries ℚ) (K := FractionRing (PowerSeries ℚ))
      (IsUnit.submonoid (PowerSeries ℚ)) (PowerSeries.X_ne_zero (R := ℚ)) hUnits 1 0).1 h
    simp only [sub_zero, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_one, not_true_eq_false] at hmem

end ValuationRing
