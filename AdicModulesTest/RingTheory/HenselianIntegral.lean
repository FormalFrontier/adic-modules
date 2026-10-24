/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianPi
import AdicModules.RingTheory.HenselianTransport
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.NonLocalRing

/-!
# Integral ascent for a finite nonlocal algebra

For a prime `p`, the diagonal algebra `Fin 2 → ℤ_[p]` is finite over the nonzero
Henselian ring `ℤ_[p]` and is not local. The extended maximal ideal is exactly the
coordinatewise maximal ideal. The input facts below do not use integral ascent.

The final example uses integral ascent. Independently, `HenselianRing.pi` gives
Henselianity for the coordinatewise ideal from Henselianity of the factors; this
is an alternative result, not a hypothesis of the ascent example.
-/

open IsLocalRing

variable (p : ℕ) [Fact p.Prime]

example : maximalIdeal ℤ_[p] ≠ ⊥ := by
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact fun h => PadicInt.prime_p.ne_zero (Ideal.span_singleton_eq_bot.mp h)

example : maximalIdeal ℤ_[p] ≠ ⊤ :=
  Ideal.IsMaximal.ne_top inferInstance

example : Module.Finite ℤ_[p] (Fin 2 → ℤ_[p]) := inferInstance

example : Function.Injective (algebraMap ℤ_[p] (Fin 2 → ℤ_[p])) := by
  intro x y h
  exact congrFun h 0

example : ¬ IsLocalRing (Fin 2 → ℤ_[p]) :=
  IsLocalRing.not_isLocalRing_of_nontrivial_pi (fun _ : Fin 2 => ℤ_[p])

example : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (Fin 2 → ℤ_[p])) =
    Ideal.pi (fun _ : Fin 2 => maximalIdeal ℤ_[p]) := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton]
  exact (Ideal.pi_span (r := fun _ : Fin 2 => (p : ℤ_[p]))).symm

example : HenselianRing (Fin 2 → ℤ_[p])
    ((maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (Fin 2 → ℤ_[p]))) :=
  HenselianRing.map_of_isIntegral (maximalIdeal ℤ_[p])
    (algebraMap ℤ_[p] (Fin 2 → ℤ_[p]))
    (algebraMap_isIntegral_iff.mpr inferInstance)
