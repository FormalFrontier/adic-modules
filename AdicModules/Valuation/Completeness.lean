/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.CompletedIntegers
public import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Adic completeness of valuation integers

The integers of a complete valued field are complete for any separated principal-ideal
filtration. Completeness of the field is for its valuation uniformity; the conclusion is
algebraic and requires no chosen topology on the integer ring. No discreteness, rank,
Noetherianity, or residue-field finiteness is assumed.

The proof uses Mathlib's equivalence of valuation uniformities and closed-range completeness,
together with the principal-adic topology comparison in `AdicModules.ValuationTopology` and
the uniform-inducing fraction-field map in `AdicModules.CompletedIntegers`. The zero ideal is
handled separately, since its adic topology need not be the valuation topology.

## References

Fesenko–Vostokov, *Local Fields and Their Extensions*, second edition, II §1, Corollary 1,
motivates the completeness bridge for valuation integers used in factor lifting. The statement
here concerns principal-adic completeness, not factor lifting, and allows arbitrary valuations.
-/

@[expose] public section

universe u v w

/-- The integers of a complete valued field are adically complete for every principal ideal
whose powers are separated, including the zero ideal.

This supplies a completeness bridge motivated by Fesenko–Vostokov, *Local Fields and Their
Extensions*, II §1, Corollary 1. Unlike the discrete-valuation setting there, no rank,
discreteness, Noetherianity, or residue-field finiteness assumption is required. -/
theorem Valuation.Integers.isAdicComplete_span_singleton
    {V : Type u} {K : Type v} {Γ₀ : Type w}
    [CommRing V] [Field K] [Algebra V K]
    [LinearOrderedCommGroupWithZero Γ₀]
    [hv : Valued K Γ₀] [CompleteSpace K]
    (hV : hv.v.Integers V) {a : V}
    [IsHausdorff (Ideal.span {a}) V] :
    IsAdicComplete (Ideal.span {a}) V := by
  by_cases ha : a = 0
  · subst a
    simpa only [Ideal.span_singleton_zero] using (inferInstance : IsAdicComplete (⊥ : Ideal V) V)
  let : IsDomain V := hV.hom_inj.isDomain
  let : ValuationRing V := ValuationRing.of_integers hv.v hV
  let : IsFractionRing V K := hV.isFractionRing
  let ν := ValuationRing.valuation V K
  have heq : ν.IsEquiv hv.v := Valuation.isEquiv_of_val_le_one fun x ↦ by
    change x ∈ ν.integer ↔ hv.v x ≤ 1
    rw [ValuationRing.mem_integer_iff]
    exact ⟨fun ⟨r, hr⟩ ↦ hr ▸ hV.map_le_one r, fun hx ↦ hV.exists_of_le_one hx⟩
  -- Transport completeness before replacing the given valuation by the canonical one.
  have : CompleteSpace (WithVal ν) :=
    (WithVal.uniformEquiv rfl heq).completeSpace_iff.mpr inferInstance
  let : Valued K (ValuationRing.ValueGroup V K) := Valued.mk' ν
  have : CompleteSpace K :=
    (WithVal.uniformEquiv rfl (show ν.IsEquiv ν from .refl)).completeSpace_iff.mp inferInstance
  let : Valued V (ValuationRing.ValueGroup V K) :=
    Valued.mk' (ν.comap (algebraMap V K))
  have hi : IsUniformInducing (algebraMap V K) :=
    ValuationRing.isUniformInducing_algebraMap_fractionRing
  have hrange : IsClosed (Set.range (algebraMap V K)) := by
    convert Valued.isClosed_integer K using 1
    exact (congrArg (fun S : Subring K ↦ (S : Set K))
      (ValuationRing.range_algebraMap_eq (A := V) (K := K))).symm
  have : CompleteSpace V := hi.completeSpace hrange.isComplete
  have : T2Space V := (Topology.IsEmbedding.mk hi.isInducing hV.hom_inj).t2Space
  exact (ValuationRing.isAdic_valuationTopology_span_singleton (K := K) ha).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩
