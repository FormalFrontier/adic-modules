/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules
import Mathlib.Tactic.NormNum

/-!
# A nonzero class in the first principal-power quotient

For the ideal `(5)` in `ℤ`, the generator chosen by a proof of principality has
nonzero class in `I / (I • ⊤)`. The inverse representative formula recovers the
nonzero class of `1` modulo `(5)`, without identifying the chosen generator
with `5`.
-/

namespace Ideal

private theorem five_isPrincipal : (Ideal.span {(5 : ℤ)}).IsPrincipal :=
  inferInstance

private theorem chosen_generator_class_ne_zero :
    let I : Ideal ℤ := Ideal.span {(5 : ℤ)}
    Submodule.Quotient.mk
        (⟨five_isPrincipal.principal.choose, by
          have hg : five_isPrincipal.principal.choose ∈ I :=
            five_isPrincipal.principal.choose_spec.ge (Ideal.mem_span_singleton_self _)
          simpa only [pow_one] using hg⟩ : (I ^ 1 : Ideal ℤ)) ≠
      (0 : (I ^ 1 : Ideal ℤ) ⧸ (I • ⊤ : Submodule ℤ (I ^ 1 : Ideal ℤ))) := by
  dsimp only
  have hI : Ideal.span {(5 : ℤ)} ≠ ⊥ := by
    norm_num [Ideal.span_singleton_eq_bot]
  have h1 : Quotient.mk (Ideal.span {(5 : ℤ)}) (1 : ℤ) ≠ 0 := by
    intro hzero
    have hm := Quotient.eq_zero_iff_mem.mp hzero
    norm_num [Ideal.mem_span_singleton] at hm
  have hinv := quotEquivPowQuotPowSucc_symm_apply_mk five_isPrincipal hI 1 (1 : ℤ)
  intro hzero
  apply h1
  have hinv' :
      (quotEquivPowQuotPowSucc five_isPrincipal hI 1).symm
          (Submodule.Quotient.mk
            (⟨five_isPrincipal.principal.choose, by
              have hg : five_isPrincipal.principal.choose ∈ Ideal.span {(5 : ℤ)} :=
                five_isPrincipal.principal.choose_spec.ge (Ideal.mem_span_singleton_self _)
              simpa only [pow_one] using hg⟩ : ((Ideal.span {(5 : ℤ)}) ^ 1 : Ideal ℤ))) =
        Quotient.mk (Ideal.span {(5 : ℤ)}) (1 : ℤ) := by
    simpa only [one_mul, pow_one] using hinv
  rw [← hinv', hzero, map_zero]

end Ideal
