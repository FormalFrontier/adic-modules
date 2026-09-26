/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.CompletedLocalStructure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Prime spectra of principal-adic completions of valuation rings

For a separated principal-adic completion of a valuation ring, every element of the completion is
associated to an element from the base ring. Consequently, extension after contraction is the
identity on ideals of the completion. When the generator belongs to the maximal ideal, the
completion map is faithfully flat, and contraction gives an order isomorphism on prime spectra.
In particular, corresponding primes have the same height.

This file also compares the extension of the original valuation to the canonical valuation of the
completed valuation ring. The resulting `Valuation.IsEquiv` can be turned into the canonical
ordered value-group isomorphism with `Valuation.IsEquiv.orderMonoidIso`.
-/

@[expose] public section

set_option linter.style.haveILetI false

noncomputable section

open scoped Topology

universe u v

namespace ValuationRing

variable {V : Type u} {K : Type v} [CommRing V] [IsDomain V]
  [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

/-- Every element of the completed valuation integers is associated to the image of an element of
the original valuation ring. -/
lemma completionIntegers_exists_associated_algebraMap (z : CompletionIntegers V K) :
    ∃ x : V, Associated (algebraMap V (CompletionIntegers V K) x) z := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  obtain ⟨k, hk⟩ := Valued.exists_coe_eq_v (K := K) (z : UniformSpace.Completion K)
  have hkint : valuation V K k ≤ 1 := by
    change Valued.v k ≤ 1
    rw [← hk]
    exact z.2
  obtain ⟨x, hx⟩ := (ValuationRing.mem_integer_iff V K k).1 hkint
  have hInt : Valuation.Integers
      (Valued.v : Valuation (UniformSpace.Completion K) (ValueGroup V K))
      (CompletionIntegers V K) := by
    unfold CompletionIntegers
    exact Valuation.integer.integers
      (Valued.v : Valuation (UniformSpace.Completion K) (ValueGroup V K))
  refine ⟨x, associated_of_dvd_dvd ?_ ?_⟩
  · apply Valuation.Integers.dvd_of_le hInt
    change Valued.v (z : UniformSpace.Completion K) ≤
      Valued.v ((algebraMap V (CompletionIntegers V K) x : CompletionIntegers V K) :
        UniformSpace.Completion K)
    rw [ValuationRing.coe_algebraMap_completionIntegers,
      UniformSpace.Completion.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply,
      Valued.valuedCompletion_apply, hx]
    change Valued.extensionValuation (z : UniformSpace.Completion K) ≤
      (Valued.v : Valuation K (ValueGroup V K)) k
    exact hk.le
  · apply Valuation.Integers.dvd_of_le hInt
    change Valued.v ((algebraMap V (CompletionIntegers V K) x : CompletionIntegers V K) :
        UniformSpace.Completion K) ≤ Valued.v (z : UniformSpace.Completion K)
    rw [ValuationRing.coe_algebraMap_completionIntegers,
      UniformSpace.Completion.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply,
      Valued.valuedCompletion_apply, hx]
    change (Valued.v : Valuation K (ValueGroup V K)) k ≤
      Valued.extensionValuation (z : UniformSpace.Completion K)
    exact hk.symm.le

/-- Every element of a separated principal-adic completion of a valuation ring is associated to
the image of an element of the original ring. -/
lemma principalAdicCompletion_exists_associated_algebraMap
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V]
    (z : AdicCompletion (Ideal.span {a}) V) :
    ∃ x : V, Associated
      (algebraMap V (AdicCompletion (Ideal.span {a}) V) x) z := by
  let e := principalAdicCompletionRingEquiv (V := V) (K := K) a ha0
  obtain ⟨x, hx⟩ := completionIntegers_exists_associated_algebraMap (e z)
  refine ⟨x, ?_⟩
  have hm := hx.map e.symm.toMonoidHom
  convert hm using 1
  · change algebraMap V (AdicCompletion (Ideal.span {a}) V) x =
      e.symm (algebraMap V (CompletionIntegers V K) x)
    apply e.injective
    rw [e.apply_symm_apply]
    exact principalAdicCompletionRingEquiv_algebraMap a ha0 x
  · exact (e.symm_apply_apply z).symm

/-- Extension after contraction is the identity on every ideal of a separated principal-adic
completion of a valuation ring. -/
lemma principalAdicCompletion_map_comap_eq
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V]
    (J : Ideal (AdicCompletion (Ideal.span {a}) V)) :
    Ideal.map (algebraMap V (AdicCompletion (Ideal.span {a}) V))
        (Ideal.comap (algebraMap V (AdicCompletion (Ideal.span {a}) V)) J) = J := by
  apply le_antisymm Ideal.map_comap_le
  intro z hz
  obtain ⟨x, hx⟩ := principalAdicCompletion_exists_associated_algebraMap K a ha0 z
  apply (Ideal.mem_iff_of_associated hx).mp
  apply Ideal.mem_map_of_mem
  exact (Ideal.mem_iff_of_associated hx).mpr hz

/-- A separated principal-adic completion map of a valuation ring is faithfully flat when its
nonzero generator belongs to the maximal ideal. -/
theorem principalAdicCompletion_faithfullyFlat
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
    [IsHausdorff (Ideal.span {a}) V] :
    letI : IsDomain (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing (AdicCompletion (Ideal.span {a}) V) :=
      principalAdicCompletion_isValuationRing K a ha0
    Module.FaithfullyFlat V (AdicCompletion (Ideal.span {a}) V) := by
  let A := AdicCompletion (Ideal.span {a}) V
  letI : IsDomain A := principalAdicCompletion_isDomain K a ha0
  letI : ValuationRing A := principalAdicCompletion_isValuationRing K a ha0
  letI : Module.IsTorsionFree V A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      change Function.Injective (AdicCompletion.of (Ideal.span {a}) V)
      exact AdicCompletion.of_injective _ _)
  letI : Module.Flat V A := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  letI : IsLocalHom (algebraMap V A) :=
    principalAdicCompletion_algebraMap_isLocalHom K a ha0 ha
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The extension of the original valuation to the completed fraction field is equivalent to the
canonical valuation attached to the completed valuation ring. Applying
`Valuation.IsEquiv.orderMonoidIso` gives the canonical ordered value-group isomorphism. -/
theorem principalAdicCompletion_extensionValuation_isEquiv
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    let A := AdicCompletion (Ideal.span {a}) V
    letI : IsDomain A := principalAdicCompletion_isDomain K a ha0
    letI : ValuationRing A := principalAdicCompletion_isValuationRing K a ha0
    letI : Algebra A (UniformSpace.Completion K) :=
      principalAdicCompletionFractionFieldAlgebra a ha0
    letI : IsFractionRing A (UniformSpace.Completion K) :=
      principalAdicCompletion_isFractionRing a ha0
    (Valued.v : Valuation (UniformSpace.Completion K) (ValueGroup V K)).IsEquiv
      (valuation A (UniformSpace.Completion K)) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let A := AdicCompletion (Ideal.span {a}) V
  let e := principalAdicCompletionRingEquiv (V := V) (K := K) a ha0
  letI : IsDomain A := principalAdicCompletion_isDomain K a ha0
  letI : ValuationRing A := principalAdicCompletion_isValuationRing K a ha0
  letI : Algebra A (UniformSpace.Completion K) :=
    principalAdicCompletionFractionFieldAlgebra a ha0
  letI : IsFractionRing A (UniformSpace.Completion K) :=
    principalAdicCompletion_isFractionRing a ha0
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  constructor
  · intro hx
    apply (ValuationRing.mem_integer_iff A (UniformSpace.Completion K) x).2
    let z : CompletionIntegers V K := ⟨x, hx⟩
    refine ⟨e.symm z, ?_⟩
    rw [principalAdicCompletionFractionFieldAlgebra_algebraMap]
    exact congrArg Subtype.val (e.apply_symm_apply z)
  · intro hx
    obtain ⟨z, hz⟩ :=
      (ValuationRing.mem_integer_iff A (UniformSpace.Completion K) x).1 hx
    have hez : ((e z : CompletionIntegers V K) : UniformSpace.Completion K) = x := by
      change algebraMap (CompletionIntegers V K) (UniformSpace.Completion K) (e z) = x
      rw [← principalAdicCompletionFractionFieldAlgebra_algebraMap a ha0 z]
      exact hz
    rw [← hez]
    exact (e z).2

/-- Contraction along a separated principal-adic completion map gives an order isomorphism on
prime spectra when the nonzero generator belongs to the maximal ideal. -/
noncomputable def principalAdicCompletionPrimeSpectrumOrderIso
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
    [IsHausdorff (Ideal.span {a}) V] :
    PrimeSpectrum (AdicCompletion (Ideal.span {a}) V) ≃o PrimeSpectrum V := by
  let A := AdicCompletion (Ideal.span {a}) V
  let f := algebraMap V A
  letI : IsDomain A := principalAdicCompletion_isDomain K a ha0
  letI : ValuationRing A := principalAdicCompletion_isValuationRing K a ha0
  letI : Module.FaithfullyFlat V A :=
    principalAdicCompletion_faithfullyFlat K a ha0 ha
  have hmapComap (J : Ideal A) : Ideal.map f (Ideal.comap f J) = J :=
    principalAdicCompletion_map_comap_eq K a ha0 J
  have hinj : Function.Injective (PrimeSpectrum.comap f) := by
    intro P Q hPQ
    apply PrimeSpectrum.ext
    rw [← hmapComap P.asIdeal, ← hmapComap Q.asIdeal]
    congr 1
    simpa only [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hPQ
  have hsurj : Function.Surjective (PrimeSpectrum.comap f) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  let e : PrimeSpectrum A ≃ PrimeSpectrum V :=
    Equiv.ofBijective (PrimeSpectrum.comap f) ⟨hinj, hsurj⟩
  exact
    { e with
      map_rel_iff' := by
        intro P Q
        change Ideal.comap f P.asIdeal ≤ Ideal.comap f Q.asIdeal ↔ P ≤ Q
        rw [← PrimeSpectrum.asIdeal_le_asIdeal]
        constructor
        · intro h
          rw [← hmapComap P.asIdeal, ← hmapComap Q.asIdeal]
          exact Ideal.map_mono h
        · exact Ideal.comap_mono }

/-- Corresponding primes of a separated principal-adic valuation-ring completion have the same
height. -/
theorem principalAdicCompletion_primeHeight_comap
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
    [IsHausdorff (Ideal.span {a}) V]
    (P : PrimeSpectrum (AdicCompletion (Ideal.span {a}) V)) :
    Order.height
        (PrimeSpectrum.comap
          (algebraMap V (AdicCompletion (Ideal.span {a}) V)) P) =
      Order.height P := by
  exact Order.height_orderIso
    (principalAdicCompletionPrimeSpectrumOrderIso K a ha0 ha) P

end ValuationRing
