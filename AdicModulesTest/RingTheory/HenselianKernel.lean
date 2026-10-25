/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianTransport
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Henselian transport from the 2-adic integers to their residue field

Let `K = (2)` in the 2-adic integers. The quotient map has nonnil kernel `K`, and
`K` is not contained in `K² = (4)`. The two applications below use the research
statements for downward closure and transport across a Henselian kernel.

The Henselian structure at `K` comes from the canonical local Henselian structure.
The image of `K²` is zero, and its Henselian structure comes independently from
completeness at the zero ideal. Neither input uses Henselianity at `K²`.
-/

namespace PadicInt

local notation "R" => PadicInt 2
local notation "K" => (Ideal.span {(2 : R)})
local notation "S" => R ⧸ K
local notation "f" => Ideal.Quotient.mk K

private theorem two_henselian_at_two : HenselianRing R K := by
  have h : IsLocalRing.maximalIdeal R = K := by
    simpa only [Nat.cast_ofNat] using (maximalIdeal_eq_span_p (p := 2))
  rw [← h]
  infer_instance

private theorem two_squared_image_eq_bot : (K ^ 2).map f = ⊥ := by
  exact Ideal.map_mk_eq_bot_of_le (Ideal.pow_le_self (by decide))

private theorem two_henselian_image : HenselianRing S ((K ^ 2).map f) := by
  rw [two_squared_image_eq_bot]
  exact IsAdicComplete.henselianRing S ⊥

/-- The quotient has genuinely nonnil kernel, outside the smaller nonzero proper ideal. -/
private theorem two_kernel_conditions :
    K ^ 2 = Ideal.span {(4 : R)} ∧ K ≠ ⊥ ∧ K ≠ ⊤ ∧
      K ^ 2 ≠ ⊥ ∧ K ^ 2 ≠ ⊤ ∧ Nontrivial S ∧
      (∃ x : R, x ∈ RingHom.ker f ∧ ¬ IsNilpotent x) ∧
      ¬ RingHom.ker f ≤ K ^ 2 := by
  have h2 : (2 : R) ≠ 0 := by norm_num
  have hnonunit : ¬ IsUnit (2 : R) := by
    simpa only [mem_nonunits_iff, Nat.cast_ofNat] using (p_nonunit (p := 2))
  have hlt : K ^ 2 < K := by
    rw [Ideal.span_singleton_pow, pow_two]
    exact Ideal.factors_decreasing (2 : R) (2 : R) h2 hnonunit
  have hKbot : K ≠ ⊥ := fun h => h2 (Ideal.span_singleton_eq_bot.mp h)
  have hKtop : K ≠ ⊤ := Ideal.span_singleton_ne_top hnonunit
  have hIbot : K ^ 2 ≠ ⊥ := by
    rw [Ideal.span_singleton_pow]
    exact fun h => pow_ne_zero 2 h2 (Ideal.span_singleton_eq_bot.mp h)
  refine ⟨by norm_num [Ideal.span_singleton_pow], hKbot, hKtop, hIbot,
    ne_top_of_le_ne_top hKtop hlt.le,
    (Ideal.Quotient.nontrivial_iff).mpr hKtop, ?_, ?_⟩
  · refine ⟨2, ?_, ?_⟩
    · rw [Ideal.mk_ker]
      exact Ideal.mem_span_singleton_self 2
    · rintro ⟨n, hn⟩
      exact (pow_ne_zero n h2) hn
  · simpa only [Ideal.mk_ker] using not_le_of_gt hlt

/-- Downward closure applies directly to `(4) ≤ (2)` in the 2-adic integers. -/
example : HenselianRing R (K ^ 2) := by
  let : HenselianRing R K := two_henselian_at_two
  exact HenselianRing.of_le (Ideal.pow_le_self (by decide))

/-- Reflection uses the independently Henselian zero ideal in the residue field. -/
example : HenselianRing R (K ^ 2) := by
  let : HenselianRing R (RingHom.ker f) := by
    rw [Ideal.mk_ker]
    exact two_henselian_at_two
  exact (HenselianRing.iff_map_of_surjective_of_henselian_ker
    (K ^ 2) f Ideal.Quotient.mk_surjective).mpr two_henselian_image

end PadicInt
