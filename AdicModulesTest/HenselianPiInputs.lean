/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Henselian

/-!
# Henselian component examples

The 2-adic integers at their maximal ideal and the trivial ring at the zero ideal
provide component examples using Mathlib's instances.
-/

private theorem padicIntTwo_henselian :
    HenselianRing (PadicInt 2) (IsLocalRing.maximalIdeal (PadicInt 2)) :=
  inferInstance

private theorem zmodOne_henselian :
    HenselianRing (ZMod 1) (⊥ : Ideal (ZMod 1)) :=
  inferInstance
