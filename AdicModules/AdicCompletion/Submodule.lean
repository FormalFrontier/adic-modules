/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.LinearMap
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Fibres and submodules under completed scalars

For a finitely generated ideal `I`, fibres of an `R`-linear map to an
`I`-Hausdorff module are stable under a compatible action of `AdicCompletion I R`
on the source. The target has only its original `R`-module structure: no action
of the completed ring or target completeness is required.

Consequently, an original `R`-submodule with `I`-Hausdorff original quotient
coincides with the restriction to `R` of its span over the completed ring.
Neither result requires source separation, completeness or finiteness.

## Implementation notes

The scalar-orbit maps use Mathlib's `LinearMap.smulRight`. Their equality follows
from `AdicCompletion.ext_of`, applied with original module `R`. The submodule
result uses the original quotient projection and span induction, without
constructing an action of the completed ring on the quotient. These arguments
reuse the Formal Frontier uniqueness API and Mathlib's completion, linear-map,
quotient and span formalizations; see the library credits for their authors.
-/

@[expose] public section

universe uR uP uT

/-- Fibres of an R-linear map to an I-Hausdorff module are stable under
completed scalars acting compatibly on its source. -/
theorem LinearMap.map_smul_eq_map_smul_of_eq_adicCompletion
    {R : Type uR} [CommRing R] (I : Ideal R)
    {P : Type uP} [AddCommMonoid P] [Module R P]
    [Module (AdicCompletion I R) P]
    [IsScalarTower R (AdicCompletion I R) P]
    {T : Type uT} [AddCommGroup T] [Module R T]
    [IsHausdorff I T]
    (hI : I.FG) (F : P →ₗ[R] T)
    {p q : P} (hpq : F p = F q) (a : AdicCompletion I R) :
    F (a • p) = F (a • q) := by
  have horbit :
      F.comp ((LinearMap.id : AdicCompletion I R →ₗ[R] AdicCompletion I R).smulRight p) =
        F.comp ((LinearMap.id : AdicCompletion I R →ₗ[R] AdicCompletion I R).smulRight q) := by
    apply AdicCompletion.ext_of I hI
    intro r
    change F (AdicCompletion.of I R r • p) = F (AdicCompletion.of I R r • q)
    have hr : algebraMap R (AdicCompletion I R) r = AdicCompletion.of I R r := by
      simp only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← hr, algebraMap_smul, algebraMap_smul, F.map_smul, F.map_smul, hpq]
  exact congrArg (fun G : AdicCompletion I R →ₗ[R] T ↦ G a) horbit

/-- An R-submodule with I-Hausdorff quotient equals the restriction of
its span over the I-adic completion. -/
theorem Submodule.span_adicCompletion_restrictScalars_eq
    {R : Type uR} [CommRing R] (I : Ideal R)
    {P : Type uP} [AddCommGroup P] [Module R P]
    [Module (AdicCompletion I R) P]
    [IsScalarTower R (AdicCompletion I R) P]
    (hI : I.FG) (N : Submodule R P)
    [IsHausdorff I (P ⧸ N)] :
    (Submodule.span (AdicCompletion I R) (N : Set P)).restrictScalars R = N := by
  have hsmul (a : AdicCompletion I R) {p : P} (hp : p ∈ N) : a • p ∈ N := by
    apply (Submodule.Quotient.mk_eq_zero N).mp
    have hp0 : N.mkQ p = N.mkQ 0 := by
      rw [map_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hp
    simpa only [smul_zero, map_zero, Submodule.mkQ_apply] using
      LinearMap.map_smul_eq_map_smul_of_eq_adicCompletion I hI N.mkQ hp0 a
  apply le_antisymm
  · intro p hp
    exact Submodule.span_induction (fun _ hx ↦ hx) N.zero_mem
      (fun _ _ _ _ hx hy ↦ N.add_mem hx hy) (fun a _ _ hx ↦ hsmul a hx) hp
  · intro p hp
    exact Submodule.subset_span hp
