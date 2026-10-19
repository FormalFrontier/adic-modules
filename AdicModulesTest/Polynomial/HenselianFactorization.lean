/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Polynomial.Hensel
import Mathlib.Data.ZMod.Defs
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.LinearCombination

/-!
# Monic factor lifting over the 3-adic integers and the zero ring

The polynomial `X² - 4` over the 3-adic integers has the ordered coprime residue
factors `X - 1` and `X + 1` modulo `(3)`. The 3-adic example applies
`HenselianRing.exists_monic_factorization` to obtain monic factors with these
prescribed reductions. Completeness supplies the Henselian-pair instance, and
`3 = 0` in the quotient gives the coprime residue factorization.

The zero ring also admits factor lifting at its top ideal, which equals its
bottom ideal; no properness condition on the ideal is needed.
-/

open Polynomial

/-- Lifting the ordered residue factors of `X² - 4` over the 3-adic integers. -/
private theorem padicInt_three_monic_factorization :
    ∃ g h : (PadicInt 3)[X],
      g.Monic ∧ h.Monic ∧ (X ^ 2 - 4 : (PadicInt 3)[X]) = g * h ∧
        g.map (Ideal.Quotient.mk (Ideal.span {(3 : PadicInt 3)})) = X - 1 ∧
        h.map (Ideal.Quotient.mk (Ideal.span {(3 : PadicInt 3)})) = X + 1 := by
  letI : HenselianRing (PadicInt 3) (Ideal.span {(3 : PadicInt 3)}) := by
    have hmax : IsLocalRing.maximalIdeal (PadicInt 3) =
        Ideal.span {(3 : PadicInt 3)} := by
      simpa only [Nat.cast_ofNat] using (PadicInt.maximalIdeal_eq_span_p (p := 3))
    rw [← hmax]
    exact IsAdicComplete.henselianRing _ _
  have hquot : (3 : PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)}) = 0 := by
    have hmem : (3 : PadicInt 3) ∈ Ideal.span {(3 : PadicInt 3)} :=
      Ideal.subset_span (by simp)
    simpa only [map_ofNat] using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hthree : (3 : (PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)})[X]) = 0 := by
    simpa only [C_ofNat, map_zero] using congrArg
      (C : (PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)}) →+*
        (PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)})[X]) hquot
  have hcop : IsCoprime
      (X - 1 : (PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)})[X]) (X + 1) := by
    refine ⟨1, -1, ?_⟩
    linear_combination -hthree
  have hfac : (X ^ 2 - 4 : (PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)})[X]) =
      (X - 1) * (X + 1) := by
    linear_combination -hthree
  exact HenselianRing.exists_monic_factorization (Ideal.span {(3 : PadicInt 3)})
    (by simpa only [C_ofNat] using
      (monic_X_pow_sub_C (4 : PadicInt 3) (by decide : (2 : ℕ) ≠ 0)))
    (by simpa using (monic_X_sub_C (1 : PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)})))
    (by simpa using (monic_X_add_C (1 : PadicInt 3 ⧸ Ideal.span {(3 : PadicInt 3)})))
    hcop (by simpa using hfac)

/-- Factor lifting at the top ideal of the zero ring. -/
private theorem zmod_one_monic_factorization :
    ∃ g h : (ZMod 1)[X],
      g.Monic ∧ h.Monic ∧ (1 : (ZMod 1)[X]) = g * h ∧
        g.map (Ideal.Quotient.mk (⊤ : Ideal (ZMod 1))) = 1 ∧
        h.map (Ideal.Quotient.mk (⊤ : Ideal (ZMod 1))) = 1 := by
  letI : HenselianRing (ZMod 1) (⊤ : Ideal (ZMod 1)) :=
    IsAdicComplete.henselianRing (ZMod 1) ⊤
  obtain ⟨g, h, hgm, hhm, _, hgh, hredg, hredh⟩ :=
    Polynomial.exists_monic_factorization_of_isAdicComplete (⊤ : Ideal (ZMod 1))
      monic_one monic_one monic_one isCoprime_one_left (by simp)
  exact ⟨g, h, hgm, hhm, hgh, hredg, hredh⟩
