/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.LocalRing

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.NormNum

/-!
# Unit detection, Jacobson kernels, and locality for adic completions

This module records four proposition-valued specifications for the public API implemented
in `AdicModules.AdicCompletion.LocalRing`. These definitions state the contract, rather than
prove it; the concrete model below uses the imported universal results. They concern the
canonical ring and algebra structures on `AdicCompletion I R` and the canonical projection
`AdicCompletion.evalOneₐ I` to `R ⧸ I`. This projection is the first nontrivial stage,
indexed by `1`; stage `0` is the quotient by `I ^ 0 = ⊤`.

The unit and kernel specifications allow arbitrary commutative rings and arbitrary ideals,
including trivial rings and the top ideal. The locality specification assumes only
`IsLocalRing (R ⧸ I)`, whose definition includes nontriviality of the quotient. No finite
generation or Noetherian hypothesis is imposed.

The maximal-ideal completion of ℤ localized at (2) supplies a proper nonzero-ideal
model: 3 gives a unit distinct from 1, and 2 gives a nonzero nonunit killed by
reduction. Mathlib supplies its local and Noetherian structures and the concrete finite
generation and injectivity facts. The imported quotient-locality theorem establishes
completion locality first; the public local-homomorphism, unit-detection and Jacobson-kernel
results then supply the corresponding model conclusions.

## References

The completion and canonical projection are from Mathlib's
`Mathlib.RingTheory.AdicCompletion.Algebra`, by Judith Ludwig and Christian Merten; the
finitely generated local-ring results are from `Mathlib.RingTheory.AdicCompletion.LocalRing`,
by Nailin Guan. The specifications use Mathlib's `IsLocalHom`, due to Johan Commelin,
Chris Hughes, and Kevin Buzzard, its `IsLocalRing`, due to Kenny Lau, Chris Hughes, and
Mario Carneiro, and its ideal Jacobson radical, due to Kenny Lau, Devon Tuma, and
Wojciech Nawrocki. The concrete model also uses Mathlib’s
`Mathlib.RingTheory.Localization.AtPrime.Basic`,
`Mathlib.RingTheory.Localization.Submodule`, and
`Mathlib.RingTheory.AdicCompletion.Noetherian`. The arbitrary-ideal unit-detection,
local-homomorphism, Jacobson-kernel and quotient-locality results used here are provided by
`AdicModules.AdicCompletion.LocalRing`.
-/

set_option warningAsError true

noncomputable section

universe u

namespace AdicModulesTest.AdicCompletion.LocalRing

/-- Unit detection by the canonical first reduction of an adic completion. -/
private def isUnit_evalOne_iff : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) (x : AdicCompletion I R),
    IsUnit (AdicCompletion.evalOneₐ I x) ↔ IsUnit x

/-- Unit reflection by the canonical first reduction, expressed as a local homomorphism. -/
private def isLocalHom_evalOne : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R),
    IsLocalHom (AdicCompletion.evalOneₐ I).toRingHom

/-- The kernel of the canonical first reduction lies in the Jacobson radical. -/
private def ker_evalOne_le_jacobson : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R),
    RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom ≤
      Ideal.jacobson (⊥ : Ideal (AdicCompletion I R))

/-- Locality of an adic completion when the quotient by its defining ideal is local. -/
private def isLocalRing_of_quotient : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)],
    IsLocalRing (AdicCompletion I R)

private abbrev twoIdeal : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)

-- `Localization.AtPrime` takes a prime-ideal instance directly, not a `Fact` wrapper.
private instance twoIdeal_isPrime : twoIdeal.IsPrime :=
  Ideal.isPrime_span_singleton_of_prime Int.prime_two

private abbrev TwoLocalization := Localization.AtPrime twoIdeal

private theorem twoLocalization_quotient_isLocalRing :
    IsLocalRing (TwoLocalization ⧸ IsLocalRing.maximalIdeal TwoLocalization) := by
  -- This exact stock field structure extends the canonical quotient commutative ring.
  -- `Ideal.Quotient.field` is deliberately not an instance.
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal TwoLocalization)
  infer_instance

private theorem twoLocalization_completion_model :
    IsLocalRing TwoLocalization ∧
    IsNoetherianRing TwoLocalization ∧
    (IsLocalRing.maximalIdeal TwoLocalization).FG ∧
    IsLocalRing.maximalIdeal TwoLocalization ≠ ⊥ ∧
    IsLocalRing.maximalIdeal TwoLocalization ≠ ⊤ ∧
    IsLocalRing (TwoLocalization ⧸ IsLocalRing.maximalIdeal TwoLocalization) ∧
    IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal TwoLocalization) TwoLocalization) ∧
    IsLocalHom (AdicCompletion.evalOneₐ
      (IsLocalRing.maximalIdeal TwoLocalization)).toRingHom ∧
    (∀ x : AdicCompletion (IsLocalRing.maximalIdeal TwoLocalization) TwoLocalization,
      IsUnit (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal TwoLocalization) x) ↔
        IsUnit x) ∧
    RingHom.ker (AdicCompletion.evalOneₐ
      (IsLocalRing.maximalIdeal TwoLocalization)).toRingHom ≤
        Ideal.jacobson (⊥ : Ideal
          (AdicCompletion (IsLocalRing.maximalIdeal TwoLocalization) TwoLocalization)) ∧
    IsUnit (algebraMap TwoLocalization
      (AdicCompletion (IsLocalRing.maximalIdeal TwoLocalization) TwoLocalization)
        (algebraMap ℤ TwoLocalization 3)) ∧
    algebraMap TwoLocalization
      (AdicCompletion (IsLocalRing.maximalIdeal TwoLocalization) TwoLocalization)
        (algebraMap ℤ TwoLocalization 3) ≠ 1 ∧
    AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal TwoLocalization)
      (algebraMap TwoLocalization
        (AdicCompletion (IsLocalRing.maximalIdeal TwoLocalization) TwoLocalization)
          (algebraMap ℤ TwoLocalization 3)) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal TwoLocalization)
        (algebraMap ℤ TwoLocalization 3) ∧
    ¬ IsUnit (algebraMap TwoLocalization
      (AdicCompletion (IsLocalRing.maximalIdeal TwoLocalization) TwoLocalization)
        (algebraMap ℤ TwoLocalization 2)) ∧
    algebraMap TwoLocalization
      (AdicCompletion (IsLocalRing.maximalIdeal TwoLocalization) TwoLocalization)
        (algebraMap ℤ TwoLocalization 2) ≠ 0 ∧
    AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal TwoLocalization)
      (algebraMap TwoLocalization
        (AdicCompletion (IsLocalRing.maximalIdeal TwoLocalization) TwoLocalization)
          (algebraMap ℤ TwoLocalization 2)) = 0 := by
  let := twoLocalization_quotient_isLocalRing
  -- Use only quotient locality for the public completion-locality theorem.
  let := AdicCompletion.isLocalRing_of_quotient (IsLocalRing.maximalIdeal TwoLocalization)
  have hfg := Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal TwoLocalization)
  have hℤ : Function.Injective (algebraMap ℤ TwoLocalization) :=
    IsLocalization.injective TwoLocalization twoIdeal.primeCompl_le_nonZeroDivisors
  have hC : Function.Injective (algebraMap TwoLocalization
      (AdicCompletion (IsLocalRing.maximalIdeal TwoLocalization) TwoLocalization)) := by
    intro a b h
    apply AdicCompletion.of_injective (IsLocalRing.maximalIdeal TwoLocalization) TwoLocalization
    simpa only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply] using h
  have h₂ : algebraMap ℤ TwoLocalization 2 ≠ 0 := by
    intro h
    have : (2 : ℤ) = 0 := hℤ (by simpa only [map_zero] using h)
    norm_num at this
  have h₂m : algebraMap ℤ TwoLocalization 2 ∈
      IsLocalRing.maximalIdeal TwoLocalization :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff TwoLocalization twoIdeal 2).mpr
      (Ideal.mem_span_singleton_self (2 : ℤ))
  have h₃ : IsUnit (algebraMap ℤ TwoLocalization 3) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff TwoLocalization twoIdeal 3).mpr
    simp only [Ideal.mem_primeCompl_iff, twoIdeal, Ideal.mem_span_singleton]
    norm_num
  have hq := AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk
    (IsLocalRing.maximalIdeal TwoLocalization)
  have hq₂ : AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal TwoLocalization)
      (algebraMap TwoLocalization
        (AdicCompletion (IsLocalRing.maximalIdeal TwoLocalization) TwoLocalization)
          (algebraMap ℤ TwoLocalization 2)) = 0 := by
    calc
      _ = Ideal.Quotient.mk (IsLocalRing.maximalIdeal TwoLocalization)
          (algebraMap ℤ TwoLocalization 2) :=
        congrArg (fun f : TwoLocalization →+*
          TwoLocalization ⧸ IsLocalRing.maximalIdeal TwoLocalization =>
            f (algebraMap ℤ TwoLocalization 2)) hq
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h₂m
  refine ⟨inferInstance, inferInstance, hfg, ?_,
    (IsLocalRing.maximalIdeal.isMaximal TwoLocalization).ne_top,
    inferInstance, inferInstance,
    AdicCompletion.isLocalHom_evalOne (IsLocalRing.maximalIdeal TwoLocalization),
    AdicCompletion.isUnit_evalOne_iff (IsLocalRing.maximalIdeal TwoLocalization),
    AdicCompletion.ker_evalOne_le_jacobson (IsLocalRing.maximalIdeal TwoLocalization),
    h₃.map (algebraMap TwoLocalization _), ?_, ?_, ?_, ?_, hq₂⟩
  · intro h
    apply h₂
    simpa only [h, Submodule.mem_bot] using h₂m
  · intro h
    have h' : algebraMap ℤ TwoLocalization 3 = 1 :=
      hC (by simpa only [map_one] using h)
    have : (3 : ℤ) = 1 := hℤ (by simpa only [map_one] using h')
    norm_num at this
  · exact congrArg (fun f : TwoLocalization →+*
        TwoLocalization ⧸ IsLocalRing.maximalIdeal TwoLocalization =>
          f (algebraMap ℤ TwoLocalization 3)) hq
  · intro h
    have hu := h.map (AdicCompletion.evalOneₐ
      (IsLocalRing.maximalIdeal TwoLocalization))
    rw [hq₂] at hu
    exact not_isUnit_zero hu
  · intro h
    exact h₂ (hC (by simpa only [map_zero] using h))

/-- The bottom-ideal completion of ℤ recovers ℤ; all elements of the top-ideal completion
and its first quotient are units. -/
public theorem bottom_and_top_completion_boundaries :
    Nonempty (ℤ ≃ₐ[ℤ] AdicCompletion (⊥ : Ideal ℤ) ℤ) ∧
    ∀ x : AdicCompletion (⊤ : Ideal ℤ) ℤ,
      IsUnit x ∧ IsUnit (AdicCompletion.evalOneₐ (⊤ : Ideal ℤ) x) := by
  refine ⟨⟨AdicCompletion.ofAlgEquiv (⊥ : Ideal ℤ)⟩, ?_⟩
  intro x
  have hx : IsUnit (AdicCompletion.evalOneₐ (⊤ : Ideal ℤ) x) :=
    isUnit_of_subsingleton _
  exact ⟨(AdicCompletion.isUnit_evalOne_iff (⊤ : Ideal ℤ) x).mp hx, hx⟩

end AdicModulesTest.AdicCompletion.LocalRing
