/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Exactness
public import Mathlib.RingTheory.Smooth.Quotient

/-!
# Flat cokernels and exactness of adic completion

Adic completion preserves injectivity of an original linear map with flat
original cokernel. It also preserves middle exactness of a right-surjective exact
pair when its last original module is flat; this middle-exactness result does not
require the first map to be injective. Together with preservation of surjectivity,
these give preservation of short exact sequences with flat original last module.

The ideal is arbitrary. No finiteness, separation, completeness or action of the
completed ring is assumed on the original modules. All completed maps and scalar
actions are the canonical ones.

## References

The proof uses Nailin Guan's Mathlib theorem
`LinearMap.ker_inf_smul_top_eq_smul_of_flat` and the range-cofinality completion
argument following Judith Ludwig and Christian Merten. Flatness makes the
induced and intrinsic filtrations on the first map's range agree at every power;
no new tensor or completion construction is needed. For injectivity, the existing
quotient maps are injective at every power, and the canonical completion map is
injective by coordinatewise extensionality, using Mathlib's completion-map API.
-/

@[expose] public section

universe uR uM uN uP

namespace AdicCompletion

/-- Completion preserves injectivity of an original linear map with flat original
cokernel. The ideal is arbitrary, and no finiteness, separation or completeness
assumption on the original modules is needed.

Mathlib's `LinearMap.ker_inf_smul_top_eq_smul_of_flat`, formalized by Nailin Guan,
makes the induced and intrinsic filtrations on the range agree. -/
theorem map_injective_of_flat_cokernel
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    {f : M →ₗ[R] N}
    [Module.Flat R (N ⧸ LinearMap.range f)]
    (hf : Function.Injective f) :
    Function.Injective (AdicCompletion.map I f) := by
  have hrange : Submodule.comap f f.range = ⊤ :=
    LinearMap.range_le_iff_comap.mp le_rfl
  have hlevel (n : ℕ) : Function.Injective (f.reduceModIdeal (I ^ n)) := by
    have hinter : f.range ⊓ (I ^ n • ⊤ : Submodule R N) = I ^ n • f.range := by
      simpa only [Submodule.ker_mkQ] using
        LinearMap.ker_inf_smul_top_eq_smul_of_flat (I ^ n) f.range.mkQ
          (Submodule.mkQ_surjective f.range)
    have hcomap : Submodule.comap f (I ^ n • ⊤ : Submodule R N) =
        I ^ n • (⊤ : Submodule R M) := by
      simpa only [Submodule.comap_inf, Submodule.comap_smul'' hf le_rfl,
        hrange, top_inf_eq] using congrArg (Submodule.comap f) hinter
    intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [LinearMap.reduceModIdeal_apply, LinearMap.reduceModIdeal_apply] at hxy
    apply (Submodule.Quotient.eq _).mpr
    rw [← hcomap, Submodule.mem_comap, map_sub]
    exact (Submodule.Quotient.eq _).mp hxy
  intro x y hxy
  apply AdicCompletion.ext
  intro n
  apply hlevel n
  simpa only [AdicCompletion.map_val_apply] using
    congrArg (fun z : AdicCompletion I N ↦ z.val n) hxy

/-- Completion preserves middle exactness of a right-surjective exact pair whose
last original module is flat. The first map need not be injective, and the ideal
need not be finitely generated.

This uses Mathlib's `LinearMap.ker_inf_smul_top_eq_smul_of_flat`, formalized by
Nailin Guan, to supply the range-cofinality criterion. -/
theorem map_exact_of_flat
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    {P : Type uP} [AddCommGroup P] [Module R P]
    [Module.Flat R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (map I f) (map I g) := by
  let : Module.Flat R (N ⧸ f.range) :=
    Module.Flat.of_linearEquiv (hfg.linearEquivOfSurjective hg)
  apply map_exact_of_range_cofinal hfg hg
  intro k
  refine ⟨k, ?_⟩
  simpa only [Submodule.ker_mkQ] using
    (LinearMap.ker_inf_smul_top_eq_smul_of_flat (I ^ k) f.range.mkQ
      (Submodule.mkQ_surjective f.range)).le

/-- Completion preserves a short exact sequence whose last original module is
flat, for any ideal.

The original quotient `N ⧸ LinearMap.range f` is linearly equivalent to `P`.
Injectivity follows from `map_injective_of_flat_cokernel`, middle exactness from
`map_exact_of_flat`, and surjectivity from Mathlib's `map_surjective`. -/
theorem map_shortExact_of_flat
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    {P : Type uP} [AddCommGroup P] [Module R P]
    [Module.Flat R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hf : Function.Injective f)
    (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Injective (AdicCompletion.map I f) ∧
      Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
      Function.Surjective (AdicCompletion.map I g) := by
  let : Module.Flat R (N ⧸ LinearMap.range f) :=
    Module.Flat.of_linearEquiv (hfg.linearEquivOfSurjective hg)
  exact ⟨map_injective_of_flat_cokernel I hf, map_exact_of_flat I hfg hg,
    map_surjective I hg⟩

end AdicCompletion
