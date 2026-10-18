/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Topology.Algebra.AdicCompactness
import AdicModules.Topology.Algebra.PadicInt
import Mathlib.Analysis.Normed.Ring.Int
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Adic compactness contracts on standard rings

The positive clients use the same standard normed ring `ℤ_[3]` and its ideal generated
by `3`. Completeness comes from the closed unit ball in the complete p-adic field.
Finiteness of the power quotients is obtained independently from `PadicInt.toZModPow`
and its kernel, using the finite rings `ZMod (3 ^ n)`. Neither compactness nor an output
of either compactness criterion is an input to these witnesses.

The integers retain their stock discrete metric topology. The bottom-adic example is
complete but its first quotient is infinite, so it is not compact. The stock one-element
ring `ZMod 1` checks the top-ideal and zeroth-power boundaries. No topology, uniformity
or global instance is defined here.

## References

* Mathlib's p-adic integers by Robert Y. Lewis, Mario Carneiro and Johan Commelin.
* Mathlib's quotient-ring equivalences, finite types and discrete integer metric.
* `PadicInt.isAdic_span_p` for the unchanged norm topology.
-/

private theorem padic_three_power_quotients_finite (n : ℕ) :
    Finite (ℤ_[3] ⧸ (Ideal.span {(3 : ℤ_[3])}) ^ n) := by
  letI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by decide)⟩
  have hker :
      RingHom.ker (PadicInt.toZModPow (p := 3) n) =
        Ideal.span {(3 : ℤ_[3]) ^ n} := by
    simpa only [Nat.cast_ofNat] using (PadicInt.ker_toZModPow (p := 3) n)
  rw [Ideal.span_singleton_pow, ← hker]
  let e : (ℤ_[3] ⧸ RingHom.ker (PadicInt.toZModPow (p := 3) n)) ≃+* ZMod (3 ^ n) :=
    RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective _)
  exact Finite.of_injective e e.injective

private theorem padic_three_compact_from_all_quotients : CompactSpace ℤ_[3] := by
  apply (IsAdic.compactSpace_iff (Ideal.span {(3 : ℤ_[3])})
    (PadicInt.isAdic_span_p 3)).2
  exact ⟨PadicInt.completeSpace 3, padic_three_power_quotients_finite⟩

private theorem padic_three_compact_from_first_quotient : CompactSpace ℤ_[3] := by
  have hfg : (Ideal.span {(3 : ℤ_[3])}).FG := Submodule.fg_span_singleton _
  have hfinite : Finite (ℤ_[3] ⧸ Ideal.span {(3 : ℤ_[3])}) := by
    simpa only [pow_one] using padic_three_power_quotients_finite 1
  exact (IsAdic.compactSpace_iff_of_fg (Ideal.span {(3 : ℤ_[3])})
    (PadicInt.isAdic_span_p 3) hfg).2 ⟨PadicInt.completeSpace 3, hfinite⟩

private theorem discrete_integers_bottom :
    IsAdic (⊥ : Ideal ℤ) ∧ CompleteSpace ℤ ∧
      Infinite (ℤ ⧸ (⊥ : Ideal ℤ) ^ 1) ∧ ¬ CompactSpace ℤ := by
  have hI : IsAdic (⊥ : Ideal ℤ) := is_bot_adic_iff.mpr inferInstance
  have hinfinite : Infinite (ℤ ⧸ (⊥ : Ideal ℤ) ^ 1) := by
    rw [pow_one]
    exact (RingEquiv.quotientBot ℤ).toEquiv.infinite_iff.mpr inferInstance
  refine ⟨hI, inferInstance, hinfinite, ?_⟩
  intro hc
  have hf := ((IsAdic.compactSpace_iff (⊥ : Ideal ℤ) hI).1 hc).2 1
  exact @Infinite.not_finite _ hinfinite hf

private theorem zero_ring_top_and_zeroth_power :
    (0 : ZMod 1) = 1 ∧ IsAdic (⊤ : Ideal (ZMod 1)) ∧
      (⊤ : Ideal (ZMod 1)) ^ 0 = ⊤ ∧
      Finite (ZMod 1 ⧸ (⊤ : Ideal (ZMod 1)) ^ 0) := by
  refine ⟨Subsingleton.elim _ _, ?_, ?_, ?_⟩
  · have h : (⊤ : Ideal (ZMod 1)) = ⊥ := Subsingleton.elim _ _
    rw [h]
    exact is_bot_adic_iff.mpr inferInstance
  · simp only [pow_zero, Ideal.one_eq_top]
  · simp only [pow_zero, Ideal.one_eq_top]
    infer_instance
