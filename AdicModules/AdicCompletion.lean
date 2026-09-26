/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.Topology.UniformSpace.AbstractCompletion

/-!
# The adic inverse limit as an abstract completion

This file packages the inverse-limit `AdicCompletion I R` as an
`AbstractCompletion R` whenever the given uniform topology on `R` is the
`I`-adic topology and `I` is finitely generated.
-/

@[expose] public section

open Filter Set

set_option linter.style.haveILetI false

namespace AdicCompletion

universe u

private lemma mem_comap_map_pow_iff
    {R : Type u} [CommRing R] (I : Ideal R) (hfg : I.FG) (n : ℕ) (x : R) :
    algebraMap R (AdicCompletion I R) x ∈
        (I.map (algebraMap R (AdicCompletion I R))) ^ n ↔
      x ∈ I ^ n := by
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval hfg]
  simp only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    LinearMap.mem_ker]
  rw [AdicCompletion.eval_of]
  simp only [smul_eq_mul, Ideal.mul_top, Submodule.mkQ_apply,
    Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

/-- A finitely generated adic inverse limit, with the topology defined by the
image of the ideal, is a complete separated uniform-space completion of the
original ring with its adic topology. -/
noncomputable def abstractCompletion
    {R : Type u} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) :
    AbstractCompletion R := by
  have hmem (n : ℕ) (x : R) :
      algebraMap R (AdicCompletion I R) x ∈
          (I.map (algebraMap R (AdicCompletion I R))) ^ n ↔
        x ∈ I ^ n := by
    rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hfg]
    simp only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      LinearMap.mem_ker]
    rw [AdicCompletion.eval_of]
    simp only [smul_eq_mul, Ideal.mul_top, Submodule.mkQ_apply,
      Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  let A := AdicCompletion I R
  let J : Ideal A := I.map (algebraMap R A)
  letI : WithIdeal A := ⟨J⟩
  have hJ : IsAdic J := rfl
  have hac : IsAdicComplete J A :=
    (IsAdicComplete.map_algebraMap_iff I A).mpr (AdicCompletion.isAdicComplete hfg)
  have hcomplete : CompleteSpace A := (hJ.isAdicComplete_iff.mp hac).1
  have hseparation : T2Space A := (hJ.isAdicComplete_iff.mp hac).2
  letI : CompleteSpace A := hcomplete
  letI : T2Space A := hseparation
  refine
    { space := A
      coe := algebraMap R A
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := ?_
      dense := ?_ }
  · apply AddMonoidHom.isUniformInducing_of_isInducing
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    apply Filter.HasBasis.ext hI.hasBasis_nhds_zero (hJ.hasBasis_nhds_zero.comap _)
    · intro n _
      refine ⟨n, trivial, ?_⟩
      intro x hx
      exact (hmem n x).1 hx
    · intro n _
      refine ⟨n, trivial, ?_⟩
      intro x hx
      exact (hmem n x).2 hx
  · intro y
    refine (mem_closure_iff_nhds_basis (hJ.hasBasis_nhds y)).2 ?_
    intro n _
    rcases Ideal.Quotient.mk_surjective (y.1 n) with ⟨x, hx⟩
    refine ⟨algebraMap R A x, ⟨x, rfl⟩, ?_⟩
    refine ⟨algebraMap R A x - y, ?_, by simp⟩
    rw [← Ideal.map_pow]
    change algebraMap R A x - y ∈
      (I ^ n).map (algebraMap R A : R →+* A)
    rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hfg]
    simp only [LinearMap.mem_ker, map_sub]
    change AdicCompletion.eval I R n (AdicCompletion.of I R x) - y.1 n = 0
    rw [AdicCompletion.eval_of, sub_eq_zero]
    exact hx

@[simp]
theorem abstractCompletion_coe
    {R : Type u} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) :
    (abstractCompletion I hI hfg).coe = algebraMap R (AdicCompletion I R) :=
  rfl

/-- The canonical map to a finitely generated adic inverse limit induces the original
uniform structure when that structure is adic. -/
theorem isUniformInducing_algebraMap
    {R : Type u} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) :
    letI : WithIdeal (AdicCompletion I R) :=
      ⟨I.map (algebraMap R (AdicCompletion I R))⟩
    IsUniformInducing (algebraMap R (AdicCompletion I R)) := by
  letI : WithIdeal (AdicCompletion I R) :=
    ⟨I.map (algebraMap R (AdicCompletion I R))⟩
  exact (abstractCompletion I hI hfg).isUniformInducing

/-- The canonical image is dense in a finitely generated adic inverse limit. -/
theorem denseRange_algebraMap
    {R : Type u} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) :
    letI : WithIdeal (AdicCompletion I R) :=
      ⟨I.map (algebraMap R (AdicCompletion I R))⟩
    DenseRange (algebraMap R (AdicCompletion I R)) := by
  letI : WithIdeal (AdicCompletion I R) :=
    ⟨I.map (algebraMap R (AdicCompletion I R))⟩
  exact (abstractCompletion I hI hfg).dense

end AdicCompletion
