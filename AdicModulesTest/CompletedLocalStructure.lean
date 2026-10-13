/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Local algebra of separated principal-adic completions

The principal-adic comparison supplies domain, valuation-ring and fraction-field structures.
For a nonzero generator in the maximal ideal, the completion is not a field and the canonical
local map induces a bijection on residue fields.

The `X`-adic completion of rational power series contains a nonzero nonunit. Its generator and
separatedness hypotheses follow from the discrete valuation ring of power series and the equality
of its maximal ideal with `(X)`.

## References

The power-series discrete valuation ring, fraction ring and separated powers of the maximal ideal
are supplied by Mathlib. The nonzero nonunit criterion is supplied by
`AdicModules.CompletedLocalStructure`.
-/

set_option warningAsError true
set_option linter.style.haveILetI false

noncomputable section

open scoped Topology

universe u v

section

variable {V : Type u} {K : Type v} [CommRing V] [IsDomain V]
  [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
  [IsHausdorff (Ideal.span {a}) V]

include K ha0 in
/-- The transported domain and valuation-ring structures are usable with independent universes. -/
private theorem domainClient : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
  ValuationRing.principalAdicCompletion_isDomain K a ha0

private theorem valuationRingClient :
    letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
      ValuationRing.principalAdicCompletion_isDomain K a ha0
    ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
  ValuationRing.principalAdicCompletion_isValuationRing K a ha0

include K ha0 ha in
/-- The completion stays non-field when its nonzero adic generator lies in the maximal ideal. -/
private theorem nonfieldClient : ¬ IsField (AdicCompletion (Ideal.span {a}) V) :=
  ValuationRing.principalAdicCompletion_not_isField K a ha0 ha

include K ha0 ha in
/-- The canonical map is local and extends the maximal ideal. -/
private theorem localMapClient :
    letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
      ValuationRing.principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
      ValuationRing.principalAdicCompletion_isValuationRing K a ha0
    IsLocalHom (algebraMap V (AdicCompletion (Ideal.span {a}) V)) :=
  ValuationRing.principalAdicCompletion_algebraMap_isLocalHom K a ha0 ha

include ha in
private theorem maximalIdealClient :
    letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
      ValuationRing.principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
      ValuationRing.principalAdicCompletion_isValuationRing K a ha0
    IsLocalRing.maximalIdeal (AdicCompletion (Ideal.span {a}) V) =
      (IsLocalRing.maximalIdeal V).map
        (algebraMap V (AdicCompletion (Ideal.span {a}) V)) :=
  ValuationRing.principalAdicCompletion_maximalIdeal_eq_map K a ha0 ha

/-- The induced map on residue fields is bijective. -/
private theorem residueFieldBijectionClient :
    letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
      ValuationRing.principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
      ValuationRing.principalAdicCompletion_isValuationRing K a ha0
    letI : IsLocalHom (algebraMap V (AdicCompletion (Ideal.span {a}) V)) :=
      ValuationRing.principalAdicCompletion_algebraMap_isLocalHom K a ha0 ha
    Function.Bijective (IsLocalRing.ResidueField.map
      (algebraMap V (AdicCompletion (Ideal.span {a}) V))) :=
  ValuationRing.principalAdicCompletion_residueFieldMap_bijective K a ha0 ha

/-- The completed field is a fraction field of the principal-adic completion. -/
private theorem fractionFieldClient :
    letI : Valued K (ValuationRing.ValueGroup V K) :=
      Valued.mk' (ValuationRing.valuation V K)
    letI : Algebra (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K) :=
      ValuationRing.principalAdicCompletionFractionFieldAlgebra a ha0
    IsFractionRing (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K) :=
  ValuationRing.principalAdicCompletion_isFractionRing a ha0

/-- The completed fraction-field embedding restricts to the original map on the base ring. -/
private theorem baseMapClient (x : V) :
    letI : Valued K (ValuationRing.ValueGroup V K) :=
      Valued.mk' (ValuationRing.valuation V K)
    letI : Algebra (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K) :=
      ValuationRing.principalAdicCompletionFractionFieldAlgebra a ha0
    algebraMap (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K)
        (algebraMap V (AdicCompletion (Ideal.span {a}) V) x) =
      algebraMap K (UniformSpace.Completion K) (algebraMap V K x) := by
  exact ValuationRing.principalAdicCompletionFractionFieldAlgebra_algebraMap_base a ha0 x

/-- Simplification retains the base-map computation without the redundant composite rule. -/
private theorem baseMapSimpClient (x : V) :
    letI : Valued K (ValuationRing.ValueGroup V K) :=
      Valued.mk' (ValuationRing.valuation V K)
    letI : Algebra (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K) :=
      ValuationRing.principalAdicCompletionFractionFieldAlgebra a ha0
    algebraMap (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K)
        (algebraMap V (AdicCompletion (Ideal.span {a}) V) x) =
      algebraMap K (UniformSpace.Completion K) (algebraMap V K x) := by
  simp


end

/-- The `X`-adic completion of rational power series contains a nonzero nonunit. -/
public theorem PowerSeries.exists_ne_zero_not_isUnit_adicCompletion :
    ∃ z : AdicCompletion (R := PowerSeries ℚ) (Ideal.span {PowerSeries.X}) (PowerSeries ℚ),
      z ≠ 0 ∧ ¬ IsUnit z := by
  let hSep : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) :=
    Eq.mp
      (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ IsHausdorff I (PowerSeries ℚ))
        (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
      (inferInstance :
        IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ))
  have hXmax : (PowerSeries.X : PowerSeries ℚ) ∈
      IsLocalRing.maximalIdeal (PowerSeries ℚ) := by
    rw [PowerSeries.maximalIdeal_eq_span_X (k := ℚ)]
    exact Ideal.subset_span (Set.mem_singleton PowerSeries.X)
  exact @ValuationRing.exists_ne_zero_not_isUnit_principalAdicCompletion
    (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
    PowerSeries.X PowerSeries.X_ne_zero hXmax hSep
