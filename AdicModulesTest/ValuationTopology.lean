/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Principal-adic valuation topology

A valuation domain separated for powers of a nonzero principal ideal carries the corresponding
adic topology under its fraction-field valuation. This module also retains the cofinality and
prime-radical consequences of separatedness, without rank or Noetherian hypotheses. The
zero-neighborhood criterion combines this comparison with the `IsAdic` neighborhood-basis API.

For `ℚ[[X]]`, `(X)` is a zero-neighborhood for the topology induced by the canonical
fraction-field valuation. This is the topology selected by the comparison theorem, not a
separately chosen power-series topology. The empty set contains no ideal power, since each
contains zero.

The proofs use the valuation topology APIs of AdicModules and Mathlib.

## References

The model uses Mathlib's rational power-series DVR, fraction field and separated
`(X)` powers. The zero-neighborhood criterion combines the principal-adic/valuation
comparison of `AdicModules.ValuationTopology` with Mathlib's `IsAdic`
neighborhood-basis interface.
-/

set_option warningAsError true

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
open scoped Topology

noncomputable section

universe u v w

section Generic

variable {R : Type u} {Γ₀ : Type w} [CommRing R]
  [LinearOrderedCommGroupWithZero Γ₀]

private theorem genericPowerCofinalityClient (ν : Valuation R Γ₀)
    (hspan : ∀ x y : R, x ∈ Ideal.span {y} ↔ ν x ≤ ν y)
    {a : R} [IsHausdorff (Ideal.span {a}) R]
    (γ : (ValueGroup₀ (.ofClass ν))ˣ) :
    ∃ n : ℕ, ν.restrict a ^ n < γ.1 :=
  ν.exists_pow_restrict_lt_of_isHausdorff hspan γ

end Generic

section ValuationRing

variable {V : Type u} {K : Type v} [CommRing V] [IsDomain V]
  [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

private theorem nonzeroPrimeRadicalClient {a : V} [IsHausdorff (Ideal.span {a}) V]
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) :
    (Ideal.span {a}).radical ≤ p :=
  ValuationRing.radical_span_singleton_le_prime_of_isHausdorff p hp

private theorem valuationPowerCofinalityClient {a : V} [IsHausdorff (Ideal.span {a}) V]
    (γ : (ValueGroup₀ (.ofClass
      ((ValuationRing.valuation V K).comap (algebraMap V K))))ˣ) :
    ∃ n : ℕ,
      ((ValuationRing.valuation V K).comap (algebraMap V K)).restrict a ^ n < γ.1 :=
  ValuationRing.exists_pow_valuation_lt_of_isHausdorff γ

private theorem adicTopologyClient {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    @IsAdic V _
      (Valued.mk' ((ValuationRing.valuation V K).comap
        (algebraMap V K))).toUniformSpace.toTopologicalSpace
      (Ideal.span {a}) :=
  ValuationRing.isAdic_valuationTopology_span_singleton ha0

end ValuationRing

/-- For rational power series, `(X)` is a zero-neighborhood in the topology induced by the
canonical fraction-field valuation, whereas the empty set is not a zero-neighborhood. -/
public theorem ValuationRing.powerSeries_span_X_mem_nhds_zero_and_empty_not_mem :
    ((Ideal.span {PowerSeries.X} : Ideal (PowerSeries ℚ)) : Set (PowerSeries ℚ)) ∈
        @nhds (PowerSeries ℚ)
          (Valued.mk' ((ValuationRing.valuation (PowerSeries ℚ)
            (FractionRing (PowerSeries ℚ))).comap
              (algebraMap (PowerSeries ℚ)
                (FractionRing (PowerSeries ℚ))))).toUniformSpace.toTopologicalSpace 0 ∧
      (∅ : Set (PowerSeries ℚ)) ∉
        @nhds (PowerSeries ℚ)
          (Valued.mk' ((ValuationRing.valuation (PowerSeries ℚ)
            (FractionRing (PowerSeries ℚ))).comap
              (algebraMap (PowerSeries ℚ)
                (FractionRing (PowerSeries ℚ))))).toUniformSpace.toTopologicalSpace 0 := by
  let hSep : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) :=
    Eq.mp
      (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ IsHausdorff I (PowerSeries ℚ))
        (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
      (inferInstance :
        IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ))
  constructor
  · apply (@ValuationRing.principalAdicTopology_mem_nhds_zero_iff
      (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
      PowerSeries.X PowerSeries.X_ne_zero hSep _).mpr
    refine ⟨1, ?_⟩
    simpa only [pow_one] using
      (Set.Subset.rfl :
        ((Ideal.span {PowerSeries.X} : Ideal (PowerSeries ℚ)) : Set (PowerSeries ℚ)) ⊆
          ((Ideal.span {PowerSeries.X} : Ideal (PowerSeries ℚ)) : Set (PowerSeries ℚ)))
  · intro hEmpty
    obtain ⟨n, hn⟩ := (@ValuationRing.principalAdicTopology_mem_nhds_zero_iff
      (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) _ _ _ _ _ _
      PowerSeries.X PowerSeries.X_ne_zero hSep (∅ : Set (PowerSeries ℚ))).mp hEmpty
    exact hn (Ideal.zero_mem ((Ideal.span {PowerSeries.X} : Ideal (PowerSeries ℚ)) ^ n))
