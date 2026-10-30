/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Bobbin
-/
module

public import AdicModules.AdicCompletion.Pi

@[expose] public section

universe uR uJ uM

example {R : Type uR} [CommRing R] (I : Ideal R) {J : Type uJ} (M : J → Type uM)
    [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] [∀ j, IsHausdorff I (M j)] :
    Function.Injective (AdicCompletion.of I (∀ j, M j)) :=
  AdicCompletion.of_injective_iff.mpr inferInstance
