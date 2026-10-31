/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Reduction of localized modules

For any ideal `J`, reduction of a module localization is again a localization,
for the original scalar action. If every denominator is a unit modulo `J`, the
same reduction map is bijective. The original localization map need not be
injective, and the modules may have independent universes.

The quotient localization is transported from `Submodule.toLocalizedQuotient'`.
Its auxiliary `Localization U`-action is derived internally from
`IsLocalizedModule.module`; no localized-ring action is required on the original
modules. The agreement with the primed provider is checked on representatives.
Bijectivity uses the identity localization and the stock comparison equivalence.

## References

This file uses the localized-module formalization of Andrew Yang and Jujian Zhang,
and the quotient-localization formalization of Andrew Yang in
Mathlib, together with Mathlib's `LinearMap.reduceModIdeal`.
-/

@[expose] public section

universe uR uM uN uA

namespace IsLocalizedModule

section QuotientTransport

variable {R : Type uR} [CommRing R] (U : Submonoid R) (J : Ideal R)
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]
variable (f : M →ₗ[R] N) [IsLocalizedModule U f]
variable (A : Type uA) [CommRing A] [Algebra R A] [IsLocalization U A]
variable [Module A N] [IsScalarTower R A N]

-- This equality records agreement with the primed provider under its own hypotheses.
private theorem reduceModIdeal_eq_toLocalizedQuotient'
    (h : ((J • (⊤ : Submodule R M)).localized' A U f).restrictScalars R =
      J • (⊤ : Submodule R N)) :
    ((Submodule.quotEquivOfEq _ _ h).toLinearMap.comp
      (Submodule.Quotient.restrictScalarsEquiv R
        ((J • (⊤ : Submodule R M)).localized' A U f)).symm.toLinearMap).comp
      ((J • (⊤ : Submodule R M)).toLocalizedQuotient' A U f) =
        (f.reduceModIdeal J).restrictScalars R := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.toLocalizedQuotient'_mk,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.quotEquivOfEq_mk,
    LinearMap.restrictScalars_apply, LinearMap.reduceModIdeal_apply]

end QuotientTransport

/-- Reducing a module localization modulo an ideal is again a localization. -/
theorem reduceModIdeal
    {R : Type uR} [CommRing R] (U : Submonoid R) (J : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule U f] :
    IsLocalizedModule U ((f.reduceModIdeal J).restrictScalars R) := by
  let : Module (Localization U) N := IsLocalizedModule.module U f
  let : IsScalarTower R (Localization U) N := IsLocalizedModule.isScalarTower_module U f
  have h : ((J • (⊤ : Submodule R M)).localized' (Localization U) U f).restrictScalars R =
      J • (⊤ : Submodule R N) := by
    rw [Submodule.restrictScalars_localized', Submodule.localized₀_smul,
      Submodule.localized₀_top]
  rw [← reduceModIdeal_eq_toLocalizedQuotient' U J f (Localization U) h]
  exact IsLocalizedModule.of_linearEquiv U _
    ((Submodule.Quotient.restrictScalarsEquiv R _).symm.trans
      (Submodule.quotEquivOfEq _ _ h))

/-- A quotient localization is bijective when its denominators are residue units. -/
theorem reduceModIdeal_bijective
    {R : Type uR} [CommRing R] (U : Submonoid R) (J : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule U f]
    (hU : ∀ u : U, IsUnit (Ideal.Quotient.mk J (u : R))) :
    Function.Bijective (f.reduceModIdeal J) := by
  let : IsLocalizedModule U ((f.reduceModIdeal J).restrictScalars R) :=
    reduceModIdeal U J f
  let : IsLocalizedModule U
      (LinearMap.id : (M ⧸ (J • (⊤ : Submodule R M))) →ₗ[R] _) :=
    { map_units := fun u ↦ by
        rw [← (Algebra.lsmul R (A := R ⧸ J) R
          (M ⧸ (J • (⊤ : Submodule R M)))).commutes]
        exact (hU u).map _
      surj := fun x ↦ ⟨(x, 1), one_smul _ _⟩
      exists_of_eq := fun h ↦ ⟨1, congrArg (fun x ↦ (1 : U) • x) h⟩ }
  let e := IsLocalizedModule.linearEquiv U
    (LinearMap.id : (M ⧸ (J • (⊤ : Submodule R M))) →ₗ[R] _)
    ((f.reduceModIdeal J).restrictScalars R)
  have he : e.toLinearMap = (f.reduceModIdeal J).restrictScalars R := by
    apply LinearMap.ext
    intro x
    exact IsLocalizedModule.linearEquiv_apply U _ _ x
  change Function.Bijective ((f.reduceModIdeal J).restrictScalars R)
  rw [← he]
  exact e.bijective

end IsLocalizedModule
