/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules

set_option warningAsError true

universe u

noncomputable section

#check AdicCompletion.abstractCompletion
#check AdicCompletion.abstractCompletion_coe
#check AdicCompletion.isUniformInducing_algebraMap
#check AdicCompletion.denseRange_algebraMap

section

variable {R : Type u} [CommRing R] (I : Ideal R) (hfg : I.FG)

private noncomputable def abstractCompletionClient :
    letI : WithIdeal R := ⟨I⟩
    AbstractCompletion R := by
  letI : WithIdeal R := ⟨I⟩
  exact AdicCompletion.abstractCompletion I rfl hfg

private theorem canonicalMapClient (x : R) :
    letI : WithIdeal R := ⟨I⟩
    (AdicCompletion.abstractCompletion I rfl hfg).coe x =
      algebraMap R (AdicCompletion I R) x := by
  rfl

end

section Nonseparated

variable (R : Type u) [CommRing R]

/-- The package also applies to the nonseparated top-adic topology. -/
private noncomputable def nonseparatedCompletionClient :
    letI : WithIdeal R := ⟨⊤⟩
    AbstractCompletion R := by
  letI : WithIdeal R := ⟨⊤⟩
  exact AdicCompletion.abstractCompletion ⊤ rfl (Ideal.fg_top R)

end Nonseparated


namespace AdicCompletion

open Filter Set

private lemma oldConstructionMemComapMapPow
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

set_option linter.style.haveILetI false in
/-- Replica of the accepted d8ceb6a5 construction, for whole-record regression only. -/
private noncomputable def oldAbstractCompletion
    {R : Type u} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) :
    AbstractCompletion R := by
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
      exact (oldConstructionMemComapMapPow I hfg n x).1 hx
    · intro n _
      refine ⟨n, trivial, ?_⟩
      intro x hx
      exact (oldConstructionMemComapMapPow I hfg n x).2 hx
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

private theorem abstractCompletionOldConstruction
    {R : Type u} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) :
    abstractCompletion I hI hfg = oldAbstractCompletion I hI hfg := rfl

#print axioms abstractCompletionOldConstruction

end AdicCompletion
