/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.LinearMap
public import AdicModules.AdicCompletion.LocalRing
public import AdicModules.LinearAlgebra.LocalizedModule
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Adic completion at residual units

Localization at elements that are units modulo `I` leaves the canonical
`I`-adic completed map bijective. `localizedModuleEquiv` packages that same map
as an equivalence linear over `AdicCompletion I R`, with its canonical actions.
It is natural in the original module and agrees with comparison to any stock
module localization. Its inverse on a fraction uses the inverse denominator in
the completed coefficient ring, not in the original ring.

All ideals and independently universed modules are allowed. No finiteness,
Noetherianity, flatness, separation or completeness assumption is needed; the
original localization map need not be injective. The residual-unit condition is
necessary already for the ring as a module, not for each individual module.

The proof uses unit reflection by first evaluation, then evaluates those units
at every original quotient, including stage zero. Quotient localization and the
identity-localization comparison give injectivity at every stage. Surjectivity
uses Mathlib's whole first-quotient criterion. No intrinsic-completeness or
evaluation-kernel identification is used.

## References

The proof builds on Mathlib's module localization and quotient localization by
Andrew Yang and Jujian Zhang, and on the adic-completion
formalizations of Kenny Lau, Judith Ludwig, Christian Merten, Jiedong Jiang and
Bingyu Xia. Unit reflection is supplied by `AdicModules.AdicCompletion.LocalRing`.
-/

@[expose] public section

noncomputable section

universe uR uM uN uP

namespace AdicCompletion

private theorem isUnit_of_residue_unit
    {R : Type uR} [CommRing R] (I : Ideal R) (r : R)
    (hr : IsUnit (Ideal.Quotient.mk I r)) : IsUnit (of I R r) := by
  apply (isUnit_evalOne_iff I _).mp
  simpa only [evalOneₐ_of] using hr

/-- Localization at units modulo the ideal leaves the canonical completed map bijective. -/
theorem map_bijective_of_isLocalizedModule
    {R : Type uR} [CommRing R] (I : Ideal R) (U : Submonoid R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule U f]
    (hU : ∀ u : U, IsUnit (Ideal.Quotient.mk I (u : R))) :
    Function.Bijective (AdicCompletion.map I f) := by
  have hstage (n : ℕ) : Function.Bijective (f.reduceModIdeal (I ^ n)) := by
    apply IsLocalizedModule.reduceModIdeal_bijective U
    intro u
    simpa only [evalₐ_of] using
      (isUnit_of_residue_unit I (u : R) (hU u)).map (evalₐ I n)
  refine ⟨map_injective_of_reduceModIdeal_injective I f (fun n ↦ (hstage n).1), ?_⟩
  apply map_surjective_of_mkQ_comp_surjective
  intro y
  obtain ⟨x, hx⟩ := (IsLocalizedModule.reduceModIdeal_bijective U I f hU).2 y
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨m, hx⟩

/-- The canonical completed-scalar-linear equivalence induced by module localization. -/
noncomputable def localizedModuleEquiv
    {R : Type uR} [CommRing R] (I : Ideal R) (U : Submonoid R)
    (hU : ∀ u : U, IsUnit (Ideal.Quotient.mk I (u : R)))
    (M : Type uM) [AddCommGroup M] [Module R M] :
    AdicCompletion I M ≃ₗ[AdicCompletion I R]
      AdicCompletion I (LocalizedModule U M) :=
  LinearEquiv.ofBijective
    (AdicCompletion.map I (LocalizedModule.mkLinearMap U M))
    (map_bijective_of_isLocalizedModule I U (LocalizedModule.mkLinearMap U M) hU)

/-- The forward linear map is completion of the original localization map. -/
@[simp]
theorem localizedModuleEquiv_toLinearMap
    {R : Type uR} [CommRing R] (I : Ideal R) (U : Submonoid R)
    (hU : ∀ u : U, IsUnit (Ideal.Quotient.mk I (u : R)))
    {M : Type uM} [AddCommGroup M] [Module R M] :
    (localizedModuleEquiv I U hU M).toLinearMap =
      AdicCompletion.map I (LocalizedModule.mkLinearMap U M) :=
  rfl

/-- The equivalence sends an original representative to its localization. -/
@[simp]
theorem localizedModuleEquiv_of
    {R : Type uR} [CommRing R] (I : Ideal R) (U : Submonoid R)
    (hU : ∀ u : U, IsUnit (Ideal.Quotient.mk I (u : R)))
    {M : Type uM} [AddCommGroup M] [Module R M] (m : M) :
    localizedModuleEquiv I U hU M (AdicCompletion.of I M m) =
      AdicCompletion.of I (LocalizedModule U M) (LocalizedModule.mk m 1) :=
  map_of I (LocalizedModule.mkLinearMap U M) m

/-- The inverse equivalence recovers each original representative. -/
@[simp]
theorem localizedModuleEquiv_symm_of
    {R : Type uR} [CommRing R] (I : Ideal R) (U : Submonoid R)
    (hU : ∀ u : U, IsUnit (Ideal.Quotient.mk I (u : R)))
    {M : Type uM} [AddCommGroup M] [Module R M] (m : M) :
    (localizedModuleEquiv I U hU M).symm
      (AdicCompletion.of I (LocalizedModule U M) (LocalizedModule.mk m 1)) =
      AdicCompletion.of I M m := by
  rw [← localizedModuleEquiv_of I U hU m, LinearEquiv.symm_apply_apply]

private theorem of_smul_of_mk
    {R : Type uR} [CommRing R] (I : Ideal R) (U : Submonoid R)
    {M : Type uM} [AddCommGroup M] [Module R M] (m : M) (u : U) :
    of I R (u : R) • of I (LocalizedModule U M) (LocalizedModule.mk m u) =
      of I (LocalizedModule U M) (LocalizedModule.mk m 1) := by
  have ha : of I R (u : R) = algebraMap R (AdicCompletion I R) (u : R) := by
    simp only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [ha, algebraMap_smul, ← (of I (LocalizedModule U M)).map_smul]
  congr 1
  rw [LocalizedModule.smul'_mk, ← Submonoid.smul_def, LocalizedModule.mk_cancel]

/-- A localized representative is sent back by the inverse denominator in the completed ring. -/
theorem localizedModuleEquiv_symm_of_mk
    {R : Type uR} [CommRing R] (I : Ideal R) (U : Submonoid R)
    (hU : ∀ u : U, IsUnit (Ideal.Quotient.mk I (u : R)))
    {M : Type uM} [AddCommGroup M] [Module R M] (m : M) (u : U) :
    (localizedModuleEquiv I U hU M).symm
      (AdicCompletion.of I (LocalizedModule U M) (LocalizedModule.mk m u)) =
      Ring.inverse (AdicCompletion.of I R (u : R)) • AdicCompletion.of I M m := by
  have h := congrArg (localizedModuleEquiv I U hU M).symm (of_smul_of_mk I U m u)
  rw [map_smul, localizedModuleEquiv_symm_of] at h
  calc
    _ = Ring.inverse (of I R (u : R)) •
        (of I R (u : R) • (localizedModuleEquiv I U hU M).symm
          (of I (LocalizedModule U M) (LocalizedModule.mk m u))) := by
      rw [← mul_smul, Ring.inverse_mul_cancel _ (isUnit_of_residue_unit I _ (hU u)),
        one_smul]
    _ = _ := by rw [h]

/-- Comparison with any stock localization has the same completed forward map. -/
theorem congr_iso_comp_localizedModuleEquiv
    {R : Type uR} [CommRing R] (I : Ideal R) (U : Submonoid R)
    (hU : ∀ u : U, IsUnit (Ideal.Quotient.mk I (u : R)))
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule U f] :
    (AdicCompletion.congr I (IsLocalizedModule.iso U f)).toLinearMap.comp
      (localizedModuleEquiv I U hU M).toLinearMap = AdicCompletion.map I f := by
  rw [localizedModuleEquiv_toLinearMap]
  change (map I (IsLocalizedModule.iso U f).toLinearMap).comp
    (map I (LocalizedModule.mkLinearMap U M)) = map I f
  rw [map_comp]
  congr 1
  apply LinearMap.ext
  intro m
  exact IsLocalizedModule.iso_mk_one U f m

/-- The canonical completed localization equivalence is natural in the original module. -/
theorem localizedModuleEquiv_naturality
    {R : Type uR} [CommRing R] (I : Ideal R) (U : Submonoid R)
    (hU : ∀ u : U, IsUnit (Ideal.Quotient.mk I (u : R)))
    {M : Type uM} [AddCommGroup M] [Module R M]
    {P : Type uP} [AddCommGroup P] [Module R P] (g : M →ₗ[R] P) :
    (AdicCompletion.map I
      (IsLocalizedModule.map U (LocalizedModule.mkLinearMap U M)
        (LocalizedModule.mkLinearMap U P) g)).comp
      (localizedModuleEquiv I U hU M).toLinearMap =
      (localizedModuleEquiv I U hU P).toLinearMap.comp (AdicCompletion.map I g) := by
  simp only [localizedModuleEquiv_toLinearMap, map_comp, IsLocalizedModule.map_comp]

/-- For the ring as a module, invariance detects precisely the residue-unit condition. -/
theorem map_localizedModule_bijective_iff
    {R : Type uR} [CommRing R] (I : Ideal R) (U : Submonoid R) :
    Function.Bijective (AdicCompletion.map I (LocalizedModule.mkLinearMap U R)) ↔
      ∀ u : U, IsUnit (Ideal.Quotient.mk I (u : R)) := by
  constructor
  · intro hf u
    obtain ⟨x, hx⟩ := hf.2 (of I (LocalizedModule U R) (LocalizedModule.mk 1 u))
    have hmul : of I R (u : R) * x = of I R 1 := by
      apply hf.1
      rw [← smul_eq_mul, map_smul, hx, of_smul_of_mk, map_of]
      rfl
    apply IsUnit.of_mul_eq_one (evalOneₐ I x)
    have h := congrArg (evalOneₐ I) hmul
    simpa only [map_mul, evalOneₐ_of, map_one] using h
  · intro hU
    exact map_bijective_of_isLocalizedModule I U (LocalizedModule.mkLinearMap U R) hU

end AdicCompletion
