/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Smooth.Quotient

/-!
# Detecting isomorphisms modulo nilpotent ideals

A linear map to a flat module is bijective if its reduction modulo a nilpotent
ideal is bijective. Neither module needs to be finitely generated, and the
source need not be flat.

The proof first kills the cokernel by iterating multiplication by the nilpotent
ideal. Reduced injectivity then puts the kernel inside the ideal times the
source. Flatness of the target identifies this intersection with the ideal
times the kernel, so the same nilpotent iteration kills the kernel.

## References

The kernel-intersection step uses Nailin Guan's Mathlib theorem
`LinearMap.ker_inf_smul_top_eq_smul_of_flat`. Reduction is Mathlib's
`LinearMap.reduceModIdeal`, formalized by Judith Ludwig and Christian Merten.
The nilpotent iteration is the standard elementary argument, with no
finite-generation form of Nakayama's lemma needed.
-/

@[expose] public section

universe uA uX uY

private theorem submodule_eq_bot_of_le_smul_of_isNilpotent
    {A : Type uA} [CommSemiring A]
    {X : Type uX} [AddCommMonoid X] [Module A X]
    (J : Ideal A) (hJ : IsNilpotent J) (P : Submodule A X)
    (hP : P ≤ J • P) : P = ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  have hpow (k : ℕ) : P ≤ J ^ k • P := by
    induction k with
    | zero => simpa only [pow_zero, one_smul] using (le_refl P)
    | succ k ih =>
      calc
        P ≤ J • P := hP
        _ ≤ J • (J ^ k • P) := smul_mono_right J ih
        _ = J ^ (k + 1) • P := by rw [pow_succ', Submodule.mul_smul]
  refine le_antisymm ?_ bot_le
  simpa only [hn, Ideal.zero_eq_bot, Submodule.bot_smul] using hpow n

/-- A linear map with flat target is bijective if it is bijective modulo a
nilpotent ideal. No finiteness or source-flatness hypothesis is required.

Surjectivity follows by nilpotent iteration on the cokernel. For injectivity,
Mathlib's `LinearMap.ker_inf_smul_top_eq_smul_of_flat`, formalized by Nailin Guan,
identifies the kernel with its ideal multiple, which nilpotence forces to vanish. -/
theorem LinearMap.bijective_of_reduceModIdeal_bijective_of_isNilpotent
    {A : Type uA} [CommRing A]
    {X : Type uX} [AddCommGroup X] [Module A X]
    {Y : Type uY} [AddCommGroup Y] [Module A Y]
    [Module.Flat A Y]
    (J : Ideal A) (hJ : IsNilpotent J) (f : X →ₗ[A] Y)
    (hf : Function.Bijective (f.reduceModIdeal J)) :
    Function.Bijective f := by
  have hsup : f.range ⊔ (J • (⊤ : Submodule A Y)) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨q, hq⟩ := hf.2 (Submodule.Quotient.mk
      (p := J • (⊤ : Submodule A Y)) y)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hy : y - f x ∈ J • (⊤ : Submodule A Y) := by
      apply (Submodule.Quotient.eq _).mp
      simpa only [LinearMap.reduceModIdeal_apply] using hq.symm
    exact Submodule.mem_sup.mpr ⟨f x, f.mem_range_self x, y - f x, hy,
      by rw [add_comm, sub_add_cancel]⟩
  have hquot : J • (⊤ : Submodule A (Y ⧸ f.range)) = ⊤ := by
    simpa only [Submodule.map_sup, Submodule.mkQ_map_self,
      Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ, bot_sup_eq]
      using congrArg (Submodule.map f.range.mkQ) hsup
  have hbot : (⊤ : Submodule A (Y ⧸ f.range)) = ⊥ :=
    submodule_eq_bot_of_le_smul_of_isNilpotent J hJ ⊤ hquot.ge
  have hs : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    intro y _
    apply (Submodule.Quotient.mk_eq_zero f.range).mp
    have hy : (Submodule.Quotient.mk y : Y ⧸ f.range) ∈
        (⊥ : Submodule A (Y ⧸ f.range)) := by
      rw [← hbot]
      exact Submodule.mem_top
    exact (Submodule.mem_bot A).mp hy
  have hk : f.ker ≤ J • (⊤ : Submodule A X) := by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply hf.1
    simp only [LinearMap.reduceModIdeal_apply, LinearMap.mem_ker.mp hx,
      Submodule.Quotient.mk_zero, map_zero]
  have hker : f.ker = ⊥ := by
    apply submodule_eq_bot_of_le_smul_of_isNilpotent J hJ f.ker
    rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat J f hs]
    exact le_inf le_rfl hk
  exact ⟨LinearMap.ker_eq_bot.mp hker, hs⟩
