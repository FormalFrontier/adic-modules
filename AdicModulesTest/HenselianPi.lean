/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianPi
import AdicModulesTest.HenselianPiInputs

/-!
# Products of Henselian component examples

These examples specialize `HenselianRing.pi` and `HenselianRing.pi_iff` to pairs of
2-adic integers, and include empty products and products of trivial rings.
-/

private theorem padicIntTwo_pi :
    HenselianRing (Bool → PadicInt 2)
      (Ideal.pi (fun _ : Bool => IsLocalRing.maximalIdeal (PadicInt 2))) := by
  exact HenselianRing.pi
    (fun _ : Bool => IsLocalRing.maximalIdeal (PadicInt 2))

private theorem padicIntTwo_component_of_pi
    (h : HenselianRing (Bool → PadicInt 2)
      (Ideal.pi (fun _ : Bool => IsLocalRing.maximalIdeal (PadicInt 2)))) :
    HenselianRing (PadicInt 2) (IsLocalRing.maximalIdeal (PadicInt 2)) := by
  exact (HenselianRing.pi_iff
    (fun _ : Bool => IsLocalRing.maximalIdeal (PadicInt 2))).mp h false

private theorem empty_pi :
    HenselianRing (Empty → PadicInt 2)
      (Ideal.pi (fun _ : Empty => IsLocalRing.maximalIdeal (PadicInt 2))) := by
  exact HenselianRing.pi
    (fun _ : Empty => IsLocalRing.maximalIdeal (PadicInt 2))

private theorem zmodOne_pi :
    HenselianRing (Bool → ZMod 1)
      (Ideal.pi (fun _ : Bool => (⊥ : Ideal (ZMod 1)))) := by
  exact HenselianRing.pi (fun _ : Bool => (⊥ : Ideal (ZMod 1)))
