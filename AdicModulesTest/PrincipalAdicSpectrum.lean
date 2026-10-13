/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Contraction in the prime spectrum of a principal-adic completion

The prime-spectrum order isomorphism of a separated principal-adic valuation-ring completion
acts by contraction along the algebra map. Contracting the prime selected by its inverse
recovers the original prime without unfolding the order-isomorphism construction.
For `ℚ[[X]]`, the bottom prime and the maximal prime `(X)` have distinct inverse lifts to
the `X`-adic completion. Contracting either lift recovers its original prime. The
associated-element, faithful-flatness, height and value-group applications are retained as well.

The proofs use the completion, spectrum and valuation APIs of AdicModules and Mathlib.
-/

set_option warningAsError true

noncomputable section

open scoped Topology

universe u v

namespace ValuationRing

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

private theorem associatedIntegerClient (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (z : CompletionIntegers V K) :
    ∃ x : V, Associated (algebraMap V (CompletionIntegers V K) x) z :=
  completionIntegers_exists_associated_algebraMap z

variable (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
  (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
  [IsHausdorff (Ideal.span {a}) V]

include K ha0 in
private theorem associatedCompletionClient (z : AdicCompletion (Ideal.span {a}) V) :
    ∃ x : V, Associated
      (algebraMap V (AdicCompletion (Ideal.span {a}) V) x) z :=
  principalAdicCompletion_exists_associated_algebraMap K a ha0 z

include K ha0 in
private theorem idealMapComapClient (J : Ideal (AdicCompletion (Ideal.span {a}) V)) :
    Ideal.map (algebraMap V (AdicCompletion (Ideal.span {a}) V))
        (Ideal.comap (algebraMap V (AdicCompletion (Ideal.span {a}) V)) J) = J :=
  principalAdicCompletion_map_comap_eq K a ha0 J

include K ha0 ha in
private theorem faithfulFlatnessClient :
    letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isValuationRing K a ha0
    Module.FaithfullyFlat V (AdicCompletion (Ideal.span {a}) V) :=
  principalAdicCompletion_faithfullyFlat K a ha0 ha

private theorem spectrumMapReductionClient (P : PrimeSpectrum (AdicCompletion (Ideal.span {a}) V)) :
    principalAdicCompletionPrimeSpectrumOrderIso K a ha0 ha P =
      PrimeSpectrum.comap
        (algebraMap V (AdicCompletion (Ideal.span {a}) V)) P := rfl

include K ha0 ha in
private theorem heightClient (P : PrimeSpectrum (AdicCompletion (Ideal.span {a}) V)) :
    Order.height
        (PrimeSpectrum.comap
          (algebraMap V (AdicCompletion (Ideal.span {a}) V)) P) =
      Order.height P :=
  principalAdicCompletion_primeHeight_comap K a ha0 ha P

private noncomputable def valueGroupEquivalenceClient :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let A := AdicCompletion (Ideal.span {a}) V
    letI : IsDomain A := principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing A := principalAdicCompletion_isValuationRing K a ha0
    letI : Algebra A (UniformSpace.Completion K) :=
      principalAdicCompletionFractionFieldAlgebra a ha0
    letI : IsFractionRing A (UniformSpace.Completion K) :=
      principalAdicCompletion_isFractionRing a ha0
    MonoidWithZeroHom.ValueGroup₀ (.ofClass
        (Valued.v : Valuation (UniformSpace.Completion K) (ValueGroup V K))) ≃*o
      MonoidWithZeroHom.ValueGroup₀
        (.ofClass (valuation A (UniformSpace.Completion K))) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let A := AdicCompletion (Ideal.span {a}) V
  letI : IsDomain A := principalAdicCompletion_isDomain K a ha0
  letI : ValuationRing A := principalAdicCompletion_isValuationRing K a ha0
  letI : Algebra A (UniformSpace.Completion K) :=
    principalAdicCompletionFractionFieldAlgebra a ha0
  letI : IsFractionRing A (UniformSpace.Completion K) :=
    principalAdicCompletion_isFractionRing a ha0
  exact (principalAdicCompletion_extensionValuation_isEquiv K a ha0).orderMonoidIso

end ValuationRing

namespace ValuationRing

/-- The bottom and maximal primes of rational power series have distinct lifts to the
`X`-adic completion, and both lifts contract to their respective original primes. -/
public theorem powerSeries_principalAdicCompletion_two_primes :
    let p := IsLocalRing.maximalIdeal (PowerSeries ℚ)
    let hSep : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) :=
      Eq.mp
        (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ IsHausdorff I (PowerSeries ℚ))
          (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
        (inferInstance :
          IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ))
    let hXmax : (PowerSeries.X : PowerSeries ℚ) ∈ p :=
      Eq.mpr
        (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ (PowerSeries.X : PowerSeries ℚ) ∈ I)
          (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
        (Ideal.subset_span (Set.mem_singleton PowerSeries.X))
    let P₀ : PrimeSpectrum (PowerSeries ℚ) := ⟨⊥, inferInstance⟩
    let Pₘ : PrimeSpectrum (PowerSeries ℚ) := ⟨p, inferInstance⟩
    let e := @principalAdicCompletionPrimeSpectrumOrderIso
      (PowerSeries ℚ) _ _ _ (FractionRing (PowerSeries ℚ)) _ _ _
      PowerSeries.X PowerSeries.X_ne_zero hXmax hSep
    e.symm P₀ ≠ e.symm Pₘ ∧
      PrimeSpectrum.comap
          (algebraMap (PowerSeries ℚ)
            (AdicCompletion (Ideal.span {PowerSeries.X}) (PowerSeries ℚ)))
          (e.symm P₀) = P₀ ∧
      PrimeSpectrum.comap
          (algebraMap (PowerSeries ℚ)
            (AdicCompletion (Ideal.span {PowerSeries.X}) (PowerSeries ℚ)))
          (e.symm Pₘ) = Pₘ := by
  let p := IsLocalRing.maximalIdeal (PowerSeries ℚ)
  let hSep : IsHausdorff (Ideal.span {PowerSeries.X}) (PowerSeries ℚ) :=
    Eq.mp
      (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ IsHausdorff I (PowerSeries ℚ))
        (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
      (inferInstance :
        IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ))
  have hXmax : (PowerSeries.X : PowerSeries ℚ) ∈ p :=
    Eq.mpr
      (congrArg (fun I : Ideal (PowerSeries ℚ) ↦ (PowerSeries.X : PowerSeries ℚ) ∈ I)
        (PowerSeries.maximalIdeal_eq_span_X (k := ℚ)))
      (Ideal.subset_span (Set.mem_singleton PowerSeries.X))
  let P₀ : PrimeSpectrum (PowerSeries ℚ) := ⟨⊥, inferInstance⟩
  let Pₘ : PrimeSpectrum (PowerSeries ℚ) := ⟨p, inferInstance⟩
  let e := @principalAdicCompletionPrimeSpectrumOrderIso
    (PowerSeries ℚ) _ _ _ (FractionRing (PowerSeries ℚ)) _ _ _
    PowerSeries.X PowerSeries.X_ne_zero hXmax hSep
  change e.symm P₀ ≠ e.symm Pₘ ∧
    PrimeSpectrum.comap
        (algebraMap (PowerSeries ℚ)
          (AdicCompletion (Ideal.span {PowerSeries.X}) (PowerSeries ℚ)))
        (e.symm P₀) = P₀ ∧
    PrimeSpectrum.comap
        (algebraMap (PowerSeries ℚ)
          (AdicCompletion (Ideal.span {PowerSeries.X}) (PowerSeries ℚ)))
        (e.symm Pₘ) = Pₘ
  have hPrimes : P₀ ≠ Pₘ := by
    intro h
    have hIdeals : (⊥ : Ideal (PowerSeries ℚ)) = p :=
      congrArg PrimeSpectrum.asIdeal h
    exact (IsDiscreteValuationRing.not_a_field (PowerSeries ℚ)) hIdeals.symm
  refine ⟨fun h ↦ hPrimes (e.symm.injective h), ?_, ?_⟩
  · exact @principalAdicCompletion_comap_orderIso_symm
      (PowerSeries ℚ) _ _ _ (FractionRing (PowerSeries ℚ)) _ _ _
      PowerSeries.X PowerSeries.X_ne_zero hXmax hSep P₀
  · exact @principalAdicCompletion_comap_orderIso_symm
      (PowerSeries ℚ) _ _ _ (FractionRing (PowerSeries ℚ)) _ _ _
      PowerSeries.X PowerSeries.X_ne_zero hXmax hSep Pₘ

end ValuationRing
