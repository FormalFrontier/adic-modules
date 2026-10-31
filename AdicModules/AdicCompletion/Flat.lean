/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Exactness
public import AdicModules.AdicCompletion.Flat.Noetherian
public import AdicModules.AdicCompletion.LinearMap
public import AdicModules.LinearAlgebra.Quotient.Flat
public import Mathlib.RingTheory.Smooth.Quotient

/-!
# Flatness, inverse criteria and exactness of adic completion

Adic completion preserves injectivity of an original linear map with flat
original cokernel. It also preserves middle exactness of a right-surjective exact
pair when its last original module is flat; this middle-exactness result does not
require the first map to be injective. Together with preservation of surjectivity,
these give preservation of short exact sequences with flat original last module.

The ideal is arbitrary. No finiteness, separation, completeness or action of the
completed ring is assumed on the original modules. All completed maps and scalar
actions are the canonical ones.

For a map from an `I`-adically complete original source to an `I`-Hausdorff
original target, bijectivity modulo `I` implies original bijectivity if every
positive target quotient `N / IⁿN` is flat over `R / Iⁿ`. In particular, original
flatness of the target suffices. No complete base, finite generation or original
completed-ring action is required. The quotient-image nilpotence criterion gives
bijectivity at each positive stage; the canonical completed-map bridge and
Mathlib's original-map surjectivity criterion then give the conclusion.

The re-exported Noetherian criterion proves that an arbitrary intrinsically
complete module is flat when all its positive intrinsic quotients are flat over
the corresponding quotient rings. It requires neither a complete base ring nor
a finite first quotient.

## References

The proof uses Nailin Guan's Mathlib theorem
`LinearMap.ker_inf_smul_top_eq_smul_of_flat` and the range-cofinality completion
argument following Judith Ludwig and Christian Merten. Flatness makes the
induced and intrinsic filtrations on the first map's range agree at every power;
no new tensor or completion construction is needed. For injectivity, the existing
quotient maps are injective at every power, and the canonical completion map is
injective by coordinatewise extensionality, using Mathlib's completion-map API.
The inverse criterion also uses their first-quotient surjectivity theorem and
this library's nilpotent flat-target theorem and quotient flat base change.
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
  exact map_injective_of_reduceModIdeal_injective I f hlevel

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

/-- A map from an adically complete source to a Hausdorff target is bijective
if it is bijective modulo the ideal and every positive original target quotient
is flat over its coefficient quotient. Neither base completeness nor finiteness
of the ideal or either module is required. -/
theorem LinearMap.bijective_of_reduceModIdeal_bijective_of_flat_pow_quotients
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    [IsAdicComplete I M] [IsHausdorff I N]
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n) (N ⧸ (I ^ n • (⊤ : Submodule R N))))
    (f : M →ₗ[R] N)
    (hf : Function.Bijective (f.reduceModIdeal I)) :
    Function.Bijective f := by
  have hstage (n : ℕ) (hn : 0 < n) :
      Function.Bijective (f.reduceModIdeal (I ^ n)) := by
    let := hflat n hn
    exact f.bijective_reduceModIdeal_of_isNilpotent_map (I ^ n) I
      (Ideal.isNilpotent_map_quotient_pow I n) hf
  refine ⟨AdicCompletion.injective_of_map_injective I f
    (AdicCompletion.map_bijective_of_reduceModIdeal_bijective I f hstage).1, ?_⟩
  apply _root_.surjective_of_mkQ_comp_surjective (I := I)
  intro y
  obtain ⟨x, hx⟩ := hf.2 y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) x
  exact ⟨x, hx⟩

/-- For a flat Hausdorff target and an adically complete source, bijectivity
modulo the ideal implies bijectivity of the original linear map. -/
theorem LinearMap.bijective_of_reduceModIdeal_bijective_of_flat
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    [IsAdicComplete I M] [IsHausdorff I N] [Module.Flat R N]
    (f : M →ₗ[R] N)
    (hf : Function.Bijective (f.reduceModIdeal I)) :
    Function.Bijective f := by
  exact f.bijective_of_reduceModIdeal_bijective_of_flat_pow_quotients I
    (fun n _ ↦ Module.Flat.quotient_smul_top N (I ^ n)) hf
