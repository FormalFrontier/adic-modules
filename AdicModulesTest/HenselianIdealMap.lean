/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.HenselianIdeal
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Henselian ideals and reduction modulo four

The canonical reduction of the 2-adic integers modulo four has Henselian kernel.
The element two belongs to the image of the Henselian radical and is nonzero.
-/

public section

namespace HenselianIdealMap

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

local notation "reduction" => (PadicInt.toZModPow 2 : ℤ_[2] →+* ZMod 4)

/-- Canonical reduction modulo four is surjective. -/
theorem reduction_surjective : Function.Surjective reduction :=
  ZMod.ringHom_surjective reduction

/-- Two belongs to the Henselian radical of the 2-adic integers. -/
theorem two_mem_henselianRadical : (2 : ℤ_[2]) ∈ Ideal.henselianRadical ℤ_[2] := by
  have hmax : HenselianRing ℤ_[2] (IsLocalRing.maximalIdeal ℤ_[2]) := inferInstance
  apply Ideal.le_henselianRadical (IsLocalRing.maximalIdeal ℤ_[2]) hmax
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.subset_span (by simp)

/-- The kernel of reduction modulo four is a Henselian ideal. -/
instance reduction_henselian_ker : HenselianRing ℤ_[2] (RingHom.ker reduction) := by
  have : Fact (1 < (2 : ℕ) ^ 2) := ⟨by decide⟩
  apply (HenselianRing.iff_le_henselianRadical _).2
  have hmax : HenselianRing ℤ_[2] (IsLocalRing.maximalIdeal ℤ_[2]) := inferInstance
  exact (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top reduction)).trans
    (Ideal.le_henselianRadical (IsLocalRing.maximalIdeal ℤ_[2]) hmax)

/-- Two is nonzero modulo four. -/
theorem two_ne_zero : (2 : ZMod 4) ≠ 0 := by
  decide

/-- The image of the Henselian radical under reduction contains two. -/
theorem two_mem_image :
    (2 : ZMod 4) ∈ (Ideal.henselianRadical ℤ_[2]).map reduction := by
  simpa only [map_ofNat] using Ideal.mem_map_of_mem reduction two_mem_henselianRadical

/-- Reduction modulo four carries the greatest Henselian ideal onto the target's
greatest Henselian ideal. -/
example :
    (Ideal.henselianRadical ℤ_[2]).map reduction = Ideal.henselianRadical (ZMod 4) :=
  Ideal.map_henselianRadical_of_surjective_of_henselian_ker reduction reduction_surjective

end HenselianIdealMap
