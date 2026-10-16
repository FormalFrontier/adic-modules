/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.PadicInt

/-!
# Nonzero integer-completion and p-adic inputs

The canonical image of `1` in the `(2)`-adic completion of `ℤ` is nonzero: the existing
completion evaluation at precision one detects its nonzero residue in `ZMod 2`.
The p-adic integer `1` is independently nonzero. Neither assertion uses the comparison
or any of its characteristic laws.

At precision zero the residue ring is `ZMod 1`, so the same nonzero element has zero
coordinate there. The unit generator also has only the trivial residue ring.
-/

namespace AdicModulesTest.AdicCompletion.PadicInt

private theorem integer_completion_two_one_ne_zero :
    AdicCompletion.of (Ideal.span {(2 : ℤ)}) ℤ 1 ≠ 0 := by
  intro h
  have heval := congrArg (AdicCompletion.evalₐ (Ideal.span {(2 : ℤ)}) 1) h
  rw [AdicCompletion.evalₐ_of, map_zero] at heval
  have hres := congrArg (Ideal.quotEquivOfEq (pow_one (Ideal.span {(2 : ℤ)}))) heval
  have hmod : (1 : ZMod 2) = 0 := by
    simpa using congrArg (Int.quotientSpanNatEquivZMod 2) hres
  exact one_ne_zero hmod

private theorem padicInt_two_one_ne_zero : (1 : ℤ_[2]) ≠ 0 := one_ne_zero

private theorem integer_completion_precision_zero :
    AdicCompletion.evalZModPow 2 0
      (AdicCompletion.of (Ideal.span {(2 : ℤ)}) ℤ 1) = 0 := by
  have : Subsingleton (ZMod (2 ^ 0)) := by
    rw [pow_zero]
    infer_instance
  exact Subsingleton.elim _ _

private theorem integer_completion_unit_residue (n : ℕ)
    (x : AdicCompletion (Ideal.span {(1 : ℤ)}) ℤ) :
    AdicCompletion.evalZModPow 1 n x = 0 := by
  have : Subsingleton (ZMod (1 ^ n)) := by
    rw [one_pow]
    infer_instance
  exact Subsingleton.elim _ _

/-- The canonical integer-completion input and the p-adic integer input at two are nonzero. -/
public theorem integer_completion_and_padicInt_two_one_ne_zero :
    AdicCompletion.of (Ideal.span {(2 : ℤ)}) ℤ 1 ≠ 0 ∧ (1 : ℤ_[2]) ≠ 0 :=
  ⟨integer_completion_two_one_ne_zero, padicInt_two_one_ne_zero⟩

private theorem integer_completion_two_comparison (a : ℤ) (n : ℕ) :
    AdicCompletion.padicIntEquiv 2
        (AdicCompletion.of (Ideal.span {(2 : ℤ)}) ℤ a) = (a : ℤ_[2]) ∧
      PadicInt.toZModPow n
        (AdicCompletion.padicIntEquiv 2
          (AdicCompletion.of (Ideal.span {(2 : ℤ)}) ℤ a)) = (a : ZMod (2 ^ n)) ∧
      AdicCompletion.evalZModPow 2 n
        ((AdicCompletion.padicIntEquiv 2).symm (a : ℤ_[2])) = (a : ZMod (2 ^ n)) ∧
      (AdicCompletion.padicIntEquiv 2).symm (a : ℤ_[2]) =
        AdicCompletion.of (Ideal.span {(2 : ℤ)}) ℤ a := by
  refine ⟨AdicCompletion.padicIntEquiv_of 2 a, ?_, ?_,
    AdicCompletion.padicIntEquiv_symm_intCast 2 a⟩
  · rw [AdicCompletion.toZModPow_padicIntEquiv 2 n]
    exact AdicCompletion.evalZModPow_of 2 n a
  · rw [AdicCompletion.evalZModPow_padicIntEquiv_symm 2 n]
    exact map_intCast (PadicInt.toZModPow n) a

end AdicModulesTest.AdicCompletion.PadicInt
