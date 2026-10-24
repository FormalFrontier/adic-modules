/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.HenselianRadical
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Radicals and diagonal idempotents over the integers modulo four

The zero ideal of `ZMod 4` differs from its radical: the nonzero element `2` has square
zero. The canonical Henselian structure at the zero ideal therefore gives a Henselian
pair at a genuinely larger ideal by `HenselianRing.iff_radical`.

The diagonal algebra `ZMod 4 × ZMod 4` is module-finite. Its nonconstant idempotent
`(1, 0)` has idempotent images in the quotients by the extensions of the zero
ideal and its radical.
-/

@[expose] public section

local notation "R" => (ZMod 4)
local notation "B" => (R × R)
local notation "J" => (Ideal.map (algebraMap R B) (⊥ : Ideal R))
local notation "K" => (Ideal.map (algebraMap R B) (Ideal.radical (⊥ : Ideal R)))

example : (2 : R) ∈ (⊥ : Ideal R).radical ∧ (2 : R) ∉ (⊥ : Ideal R) := by
  constructor
  · refine Ideal.mem_radical_iff.mpr ⟨2, ?_⟩
    rw [Ideal.mem_bot]
    decide
  · rw [Ideal.mem_bot]
    decide

/-- The radical of the zero ideal in `ZMod 4` is Henselian. -/
theorem henselianRing_radical_bot_zmod_four :
    HenselianRing R ((⊥ : Ideal R).radical) := by
  exact (HenselianRing.iff_radical (⊥ : Ideal R)).mp
    (inferInstance : HenselianRing R (⊥ : Ideal R))

example : Module.Finite R B ∧
    ((1, 0) : B) ≠ 0 ∧ ((1, 0) : B) ≠ 1 ∧
    IsIdempotentElem ((1, 0) : B) ∧
    IsIdempotentElem (Ideal.Quotient.mk J ((1, 0) : B)) ∧
    IsIdempotentElem (Ideal.Quotient.mk K ((1, 0) : B)) := by
  let : Nontrivial R := ZMod.nontrivial_iff.mpr (by decide : (4 : ℕ) ≠ 1)
  have he : IsIdempotentElem ((1, 0) : B) := by
    simp [IsIdempotentElem]
  refine ⟨Module.Finite.of_finite, ?_, ?_, he,
    he.map (Ideal.Quotient.mk J), he.map (Ideal.Quotient.mk K)⟩
  · intro h
    exact one_ne_zero (congrArg Prod.fst h : (1 : R) = 0)
  · intro h
    exact zero_ne_one (congrArg Prod.snd h : (0 : R) = 1)
