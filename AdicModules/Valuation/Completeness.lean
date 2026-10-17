/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.CompletedIntegers
public import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Adic completeness of valuation integers

The integers of a complete valued field are complete for any separated principal-ideal
filtration. For a nonzero generator, principal-adic completeness is equivalent to completeness
of the ambient valued field. Completeness of the field is for its supplied valuation
uniformity; adic completeness is algebraic and requires no chosen topology on the integer
ring. No discreteness, rank, Noetherianity, or residue-field finiteness is assumed.

The proofs use Mathlib's equivalence of valuation uniformities, together with the principal-adic
topology comparison in `AdicModules.ValuationTopology` and the uniform-inducing fraction-field
map in `AdicModules.CompletedIntegers`. In one direction, the valuation integers are a closed
subspace of a complete field. In the other, they form a complete neighborhood of zero, which
implies completeness of the field. Uniform equivalences transport completeness between the
canonical valuation and the supplied valuation on the same field. The zero ideal is handled
separately, since its adic topology need not be the valuation topology.

## References

Fesenko–Vostokov, *Local Fields and Their Extensions*, second edition, II §1, Corollary 1,
motivates the completeness bridge for valuation integers used in factor lifting. The statement
here concerns principal-adic completeness, not factor lifting, and allows arbitrary valuations.

The complete-neighborhood criterion generalizes Mathlib's right-uniform group completeness
argument by Patrick Massot and Johannes Hölzl in
`Mathlib.Topology.Algebra.IsUniformGroup.Basic`.
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

/-
The complete-neighborhood argument below generalizes the proof of
`IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace` in Mathlib.
The original source notice is:

Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
section

open Filter
open scoped Topology

/-- A right-uniform group with a complete neighborhood of the identity is complete. -/
@[to_additive
/-- A right-uniform additive group with a complete neighborhood of zero is complete. -/]
private theorem IsRightUniformGroup.completeSpace_of_isComplete_mem_nhds
    {G : Type*} [Group G] [UniformSpace G] [IsRightUniformGroup G]
    (s : Set G) (hs : IsComplete s) (hs_mem : s ∈ 𝓝 (1 : G)) : CompleteSpace G where
  complete {f} hf := by
    have : f.NeBot := hf.1
    obtain ⟨x, hx⟩ : ∃ x, ∀ᶠ y in f, y / x ∈ s := by
      rw [cauchy_iff_le, uniformity_eq_comap_nhds_one, ← tendsto_iff_comap] at hf
      exact hf.eventually_mem hs_mem |>.curry.exists
    have htranslate : IsUniformEmbedding (fun y : G ↦ y * x) :=
      { comap_uniformity := by
          simp only [uniformity_eq_comap_nhds_one, comap_comap, Function.comp_def,
            div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
        injective := mul_left_injective x }
    have hsx : IsComplete ((fun y : G ↦ y * x) '' s) := htranslate.isComplete_iff.mpr hs
    have hx' : ∀ᶠ y in f, y ∈ (fun z : G ↦ z * x) '' s :=
      hx.mono fun y hy ↦ ⟨y / x, hy, div_mul_cancel y x⟩
    obtain ⟨l, -, hl⟩ := hsx f hf (le_principal_iff.mpr hx')
    exact ⟨l, hl⟩

/-- A compact identity neighborhood supplies the complete neighborhood required by the criterion,
recovering completeness under weak local compactness. -/
@[to_additive
/-- A compact zero neighborhood supplies the complete neighborhood required by the criterion,
recovering completeness under weak local compactness. -/]
private theorem
    IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace_via_isComplete_mem_nhds
    {G : Type*} [Group G] [UniformSpace G] [IsRightUniformGroup G]
    [WeaklyLocallyCompactSpace G] : CompleteSpace G := by
  obtain ⟨s, hs, hs_mem⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds (1 : G)
  exact IsRightUniformGroup.completeSpace_of_isComplete_mem_nhds s hs.isComplete hs_mem

end

/-- For a nonzero element of a valuation-integer ring with separated principal-ideal powers,
adic completeness is equivalent to completeness of the ambient valued field.

The nonzero hypothesis is needed because the zero ideal is adically complete even when the
field is not complete. Separation excludes the unit-ideal filtration on a nontrivial ring.
Completeness of `K` is for the uniformity of the given `Valued K Γ₀` instance on the given
field. This valuation uniformity is determined by its intrinsic value group; no new norm or
field structure is chosen.

This extends the completeness bridge motivated by Fesenko–Vostokov, *Local Fields and Their
Extensions*, II §1, Corollary 1, without a rank or discreteness assumption. -/
theorem Valuation.Integers.isAdicComplete_span_singleton_iff
    {R : Type u} {K : Type v} {Γ₀ : Type w}
    [CommRing R] [Field K] [Algebra R K]
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀]
    (hR : hv.v.Integers R) {a : R} (ha0 : a ≠ 0)
    [IsHausdorff (Ideal.span {a}) R] :
    IsAdicComplete (Ideal.span {a}) R ↔ CompleteSpace K := by
  constructor
  · intro hcomplete
    let : IsDomain R := hR.hom_inj.isDomain
    let : ValuationRing R := ValuationRing.of_integers hv.v hR
    let : IsFractionRing R K := hR.isFractionRing
    let ν := ValuationRing.valuation R K
    have heq : ν.IsEquiv hv.v := Valuation.isEquiv_of_val_le_one fun x ↦ by
      change x ∈ ν.integer ↔ hv.v x ≤ 1
      rw [ValuationRing.mem_integer_iff]
      exact ⟨fun ⟨r, hr⟩ ↦ hr ▸ hR.map_le_one r, fun hx ↦ hR.exists_of_le_one hx⟩
    -- Keep the canonical uniformities scoped to this intermediate completeness statement.
    have hν : CompleteSpace (WithVal ν) := by
      let : Valued K (ValuationRing.ValueGroup R K) := Valued.mk' ν
      let : Valued R (ValuationRing.ValueGroup R K) :=
        Valued.mk' (ν.comap (algebraMap R K))
      have hAdic :=
        ValuationRing.isAdic_valuationTopology_span_singleton (K := K) ha0
      have : CompleteSpace R := (hAdic.isAdicComplete_iff.mp hcomplete).1
      have hi : IsUniformInducing (algebraMap R K) :=
        ValuationRing.isUniformInducing_algebraMap_fractionRing
      have hinteger : IsComplete (ν.integer : Set K) := by
        convert hi.isComplete_range using 1
        exact congrArg (fun S : Subring K ↦ (S : Set K))
          (ValuationRing.range_algebraMap_eq (A := R) (K := K))
      have : CompleteSpace K :=
        IsRightUniformAddGroup.completeSpace_of_isComplete_mem_nhds (ν.integer : Set K)
          hinteger ((Valued.isOpen_integer K).mem_nhds ν.integer.zero_mem)
      exact (WithVal.uniformEquiv rfl (show ν.IsEquiv ν from .refl)).completeSpace_iff.mpr
        inferInstance
    -- Here the uniformity on `K` is again the one supplied by `hv`.
    exact (WithVal.uniformEquiv rfl heq).completeSpace_iff.mp hν
  · intro hcomplete
    let : CompleteSpace K := hcomplete
    exact Valuation.Integers.isAdicComplete_span_singleton hR
