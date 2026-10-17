/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.AdicCompletion.Kernel
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Integer calibration for the completion evaluation kernel

The closed model uses `R = M = ℤ`, the ideal `(2)`, and evaluation at degree one.
Its kernel equality comes from Mathlib's existing finitely generated ideal theorem,
independently of the fixed-degree finite-generation headline. The value at the
canonical image of one is nonzero, calibrated directly by the stock equivalence
between `ℤ/(2)` and `ZMod 2`.

The ground ring has characteristic zero and the residue calibration has
characteristic two. No characteristic is assigned here to the completion. At
degree zero, for the same inputs, the evaluation kernel is the whole module and
the ideal quotient has characteristic one.

The separate recovery client uses the fixed-degree headline and `Ideal.FG.pow`
to recover exactly the old `I.FG` statement. It is not part of the independent
closed-model argument.

## References

Mathlib's `RingTheory.AdicCompletion.Completeness` supplies the old kernel
identity; `Data.ZMod.QuotientRing` supplies the integer residue equivalence.
-/

set_option linter.privateModule false

namespace AdicCompletionKernelTest

universe u v

private theorem kernel_of_fg
    {R : Type u} [CommRing R] {I : Ideal R}
    {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (h : I.FG) :
    I ^ n • ⊤ = (AdicCompletion.eval I M n).ker :=
  AdicCompletion.pow_smul_top_eq_ker_eval_of_fg_pow (Ideal.FG.pow (n := n) h)

private theorem integerTwo_kernel_and_nonzero_eval :
    (Ideal.span ({(2 : ℤ)} : Set ℤ)) ^ 1 •
        (⊤ : Submodule ℤ (AdicCompletion (Ideal.span ({(2 : ℤ)} : Set ℤ)) ℤ)) =
      (AdicCompletion.eval (Ideal.span ({(2 : ℤ)} : Set ℤ)) ℤ 1).ker ∧
    AdicCompletion.eval (Ideal.span ({(2 : ℤ)} : Set ℤ)) ℤ 1
        (AdicCompletion.of (Ideal.span ({(2 : ℤ)} : Set ℤ)) ℤ 1) ≠ 0 := by
  have hfg : (Ideal.span ({(2 : ℤ)} : Set ℤ)).FG :=
    Submodule.fg_span_singleton (R := ℤ) (2 : ℤ)
  constructor
  · exact AdicCompletion.pow_smul_top_eq_ker_eval hfg
  · intro h
    have hmem : (1 : ℤ) ∈
        (Ideal.span ({(2 : ℤ)} : Set ℤ)) ^ 1 • (⊤ : Submodule ℤ ℤ) := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      simpa only [Submodule.mkQ_apply] using
        (AdicCompletion.eval_of (Ideal.span ({(2 : ℤ)} : Set ℤ)) ℤ 1 (1 : ℤ)).symm.trans h
    have hres : Ideal.Quotient.mk (Ideal.span ({(2 : ℤ)} : Set ℤ)) 1 = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa only [pow_one, Ideal.smul_eq_mul, Ideal.mul_top] using hmem
    have hmod : (1 : ZMod 2) = 0 := by
      simpa only [map_one, map_zero] using
        congrArg (Int.quotientSpanNatEquivZMod 2) hres
    exact one_ne_zero hmod

private theorem integerTwo_zero_boundary :
    (Ideal.span ({(2 : ℤ)} : Set ℤ)) ^ 0 •
        (⊤ : Submodule ℤ (AdicCompletion (Ideal.span ({(2 : ℤ)} : Set ℤ)) ℤ)) =
      (AdicCompletion.eval (Ideal.span ({(2 : ℤ)} : Set ℤ)) ℤ 0).ker ∧
    (AdicCompletion.eval (Ideal.span ({(2 : ℤ)} : Set ℤ)) ℤ 0).ker = ⊤ ∧
    ringChar (ℤ ⧸ (Ideal.span ({(2 : ℤ)} : Set ℤ)) ^ 0) = 1 := by
  have hfg : (Ideal.span ({(2 : ℤ)} : Set ℤ)).FG :=
    Submodule.fg_span_singleton (R := ℤ) (2 : ℤ)
  have hkernel := AdicCompletion.pow_smul_top_eq_ker_eval (M := ℤ) (n := 0) hfg
  refine ⟨hkernel, ?_, ?_⟩
  · rw [← hkernel, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  · apply ringChar.ringChar_eq_one.mpr
    apply Ideal.Quotient.subsingleton_iff.mpr
    rw [pow_zero, Ideal.one_eq_top]

private theorem integerTwo_kernel :
    (Ideal.span ({(2 : ℤ)} : Set ℤ)) ^ 1 •
        (⊤ : Submodule ℤ (AdicCompletion (Ideal.span ({(2 : ℤ)} : Set ℤ)) ℤ)) =
      (AdicCompletion.eval (Ideal.span ({(2 : ℤ)} : Set ℤ)) ℤ 1).ker := by
  have hfg : (Ideal.span ({(2 : ℤ)} : Set ℤ)).FG :=
    Submodule.fg_span_singleton (R := ℤ) (2 : ℤ)
  exact AdicCompletion.pow_smul_top_eq_ker_eval_of_fg_pow (Ideal.FG.pow (n := 1) hfg)

end AdicCompletionKernelTest
