/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.ChangeIdeal
public import CoherentModules.RingTheory.Noetherian

/-!
# Changing ideals on Noetherian modules

For a Noetherian module over a commutative ring, containment of radicals after adjoining
its annihilator induces a canonical comparison of adic completions. Equality of these
effective radicals gives an equivalence linear over the original ring.

The ideal-power bounds come from `CoherentModules.RingTheory.Noetherian`; the comparisons,
equivalences and their characteristic laws use `AdicModules.AdicCompletion.ChangeIdeal`.

## Implementation notes

The module and its original scalar action are unchanged. Neither Noetherianity of the ring
nor finite generation of the original ideals is assumed. These are sufficient criteria,
not assertions of necessity or equivalences between completed coefficient rings.

For modules that are not Noetherian, the image-finite-generation criterion
`Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le_of_map_fg` can instead be
supplied directly to `AdicCompletion.mapOfPowSMulLE` or `AdicCompletion.equivOfCofinalSMul`.
-/

@[expose] public section

noncomputable section

universe uR uM uN

open Submodule

namespace AdicCompletion

variable {R : Type uR} [CommRing R]

/-- Effective radical containment on a Noetherian module induces a comparison of its
adic completions, linear over the original ring. -/
def mapOfRadicalSupAnnihilatorLE
    (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (h : (I ⊔ Module.annihilator R M).radical ≤
      (J ⊔ Module.annihilator R M).radical) :
    AdicCompletion I M →ₗ[R] AdicCompletion J M :=
  mapOfPowSMulLE I J M
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h)

/-- The effective-radical comparison agrees as a linear map with comparison from any
uniform power bound on the original module. -/
theorem mapOfRadicalSupAnnihilatorLE_eq_mapOfPowSMulLE
    (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (h : (I ⊔ Module.annihilator R M).radical ≤
      (J ⊔ Module.annihilator R M).radical)
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) :
    mapOfRadicalSupAnnihilatorLE I J M h = mapOfPowSMulLE I J M hIJ :=
  mapOfPowSMulLE_congr I J M
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h) hIJ

/-- At every admissible pair of quotient stages, the comparison is the canonical
factor map on arbitrary completed inputs. Either stage may be zero. -/
theorem eval_mapOfRadicalSupAnnihilatorLE
    (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (h : (I ⊔ Module.annihilator R M).radical ≤
      (J ⊔ Module.annihilator R M).radical)
    {m n : ℕ} (hmn : (I ^ m • ⊤ : Submodule R M) ≤ J ^ n • ⊤)
    (x : AdicCompletion I M) :
    eval J M n (mapOfRadicalSupAnnihilatorLE I J M h x) =
      factor hmn (eval I M m x) :=
  eval_mapOfPowSMulLE I J M
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h) hmn x

/-- Comparison preserves the canonical image of the original module. -/
@[simp]
theorem mapOfRadicalSupAnnihilatorLE_of
    (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (h : (I ⊔ Module.annihilator R M).radical ≤
      (J ⊔ Module.annihilator R M).radical) (x : M) :
    mapOfRadicalSupAnnihilatorLE I J M h (of I M x) = of J M x :=
  mapOfPowSMulLE_of I J M
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h) x

/-- Comparison is natural for maps of the original modules, with effective radical
containment assumed separately on the source and target modules. -/
theorem mapOfRadicalSupAnnihilatorLE_map
    (I J : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M] [IsNoetherian R M]
    {N : Type uN} [AddCommGroup N] [Module R N] [IsNoetherian R N]
    (hM : (I ⊔ Module.annihilator R M).radical ≤
      (J ⊔ Module.annihilator R M).radical)
    (hN : (I ⊔ Module.annihilator R N).radical ≤
      (J ⊔ Module.annihilator R N).radical)
    (f : M →ₗ[R] N) (x : AdicCompletion I M) :
    mapOfRadicalSupAnnihilatorLE I J N hN (map I f x) =
      map J f (mapOfRadicalSupAnnihilatorLE I J M hM x) :=
  mapOfPowSMulLE_map I J
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le hM)
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le hN) f x

/-- Equality of effective radicals on a Noetherian module gives a canonical equivalence
of its adic completions, linear over the original ring. -/
def equivOfRadicalSupAnnihilatorEq
    (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (h : (I ⊔ Module.annihilator R M).radical =
      (J ⊔ Module.annihilator R M).radical) :
    AdicCompletion I M ≃ₗ[R] AdicCompletion J M :=
  equivOfCofinalSMul I J M
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h.le)
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h.ge)

/-- The effective-radical equivalence agrees with the existing equivalence from any
pair of uniform power bounds on the original module. -/
theorem equivOfRadicalSupAnnihilatorEq_eq_equivOfCofinalSMul
    (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (h : (I ⊔ Module.annihilator R M).radical =
      (J ⊔ Module.annihilator R M).radical)
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hJI : ∃ b : ℕ, (J ^ b • ⊤ : Submodule R M) ≤ I • ⊤) :
    equivOfRadicalSupAnnihilatorEq I J M h =
      equivOfCofinalSMul I J M hIJ hJI :=
  equivOfCofinalSMul_congr I J M
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h.le) hIJ
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h.ge) hJI

/-- The forward linear map is the comparison induced by effective radical containment. -/
@[simp]
theorem equivOfRadicalSupAnnihilatorEq_toLinearMap
    (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (h : (I ⊔ Module.annihilator R M).radical =
      (J ⊔ Module.annihilator R M).radical) :
    (equivOfRadicalSupAnnihilatorEq I J M h).toLinearMap =
      mapOfRadicalSupAnnihilatorLE I J M h.le :=
  equivOfCofinalSMul_toLinearMap I J M
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h.le)
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h.ge)

/-- The forward application is the effective-radical comparison on every completed input. -/
theorem equivOfRadicalSupAnnihilatorEq_apply
    (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (h : (I ⊔ Module.annihilator R M).radical =
      (J ⊔ Module.annihilator R M).radical)
    (x : AdicCompletion I M) :
    equivOfRadicalSupAnnihilatorEq I J M h x =
      mapOfRadicalSupAnnihilatorLE I J M h.le x :=
  equivOfCofinalSMul_apply I J M
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h.le)
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h.ge) x

/-- Inverting the equivalence reverses the equality of effective radicals. -/
@[simp]
theorem equivOfRadicalSupAnnihilatorEq_symm
    (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (h : (I ⊔ Module.annihilator R M).radical =
      (J ⊔ Module.annihilator R M).radical) :
    (equivOfRadicalSupAnnihilatorEq I J M h).symm =
      equivOfRadicalSupAnnihilatorEq J I M h.symm :=
  equivOfCofinalSMul_symm I J M
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h.le)
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h.ge)

/-- The equivalence preserves the canonical image of the original module. -/
@[simp]
theorem equivOfRadicalSupAnnihilatorEq_of
    (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (h : (I ⊔ Module.annihilator R M).radical =
      (J ⊔ Module.annihilator R M).radical) (x : M) :
    equivOfRadicalSupAnnihilatorEq I J M h (of I M x) = of J M x :=
  equivOfCofinalSMul_of I J M
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h.le)
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le h.ge) x

/-- The equivalence is natural for maps of the original modules, with effective radical
equality assumed separately on the source and target modules. -/
theorem equivOfRadicalSupAnnihilatorEq_map
    (I J : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M] [IsNoetherian R M]
    {N : Type uN} [AddCommGroup N] [Module R N] [IsNoetherian R N]
    (hM : (I ⊔ Module.annihilator R M).radical =
      (J ⊔ Module.annihilator R M).radical)
    (hN : (I ⊔ Module.annihilator R N).radical =
      (J ⊔ Module.annihilator R N).radical)
    (f : M →ₗ[R] N) (x : AdicCompletion I M) :
    equivOfRadicalSupAnnihilatorEq I J N hN (map I f x) =
      map J f (equivOfRadicalSupAnnihilatorEq I J M hM x) :=
  equivOfCofinalSMul_map I J
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le hM.le)
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le hM.ge)
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le hN.le)
    (Ideal.exists_pow_smul_top_le_of_radical_sup_annihilator_le hN.ge) f x

end AdicCompletion
