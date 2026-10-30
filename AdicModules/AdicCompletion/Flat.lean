/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Exactness
public import Mathlib.RingTheory.Smooth.Quotient

/-!
# Adic completion with a flat last module

Adic completion preserves middle exactness of a right-surjective exact pair when
its last original module is flat. The ideal is arbitrary and the first map need
not be injective. No finiteness, separation or completeness assumption is imposed
on the original modules.

## References

The proof uses Nailin Guan's Mathlib theorem
`LinearMap.ker_inf_smul_top_eq_smul_of_flat` and the range-cofinality completion
argument following Judith Ludwig and Christian Merten. Flatness makes the
induced and intrinsic filtrations on the first map's range agree at every power;
no new tensor or completion construction is needed.
-/

@[expose] public section

universe uR uM uN uP

namespace AdicCompletion

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

end AdicCompletion
