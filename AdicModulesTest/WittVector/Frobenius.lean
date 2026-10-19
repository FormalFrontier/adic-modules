/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.WittVector.Frobenius
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Witt Frobenius over a product and over dual numbers

The product of two copies of `ZMod 2` is perfect and has explicit nonzero zero divisors.
Its Witt Frobenius fixes every Witt vector. In contrast, the Teichmüller lift of the
square-zero element of `DualNumber (ZMod 2)` is a nonzero element killed by Witt Frobenius.
These coefficient computations also exhibit the failure of perfection for the dual numbers.
The bijectivity criterion specializes to both rings.

## References

The arguments use Mathlib's product and finite-field instances, dual-number laws, and
coefficient formulas for Witt Frobenius and Teichmüller lifts.
-/

@[expose] public section

namespace WittVector

private theorem zmod_two_prod_perfect : PerfectRing ((ZMod 2) × (ZMod 2)) 2 := by
  exact instPerfectRingProd (R := ZMod 2) (p := 2) (ZMod 2)

private theorem zmod_two_prod_zero_divisors :
    ((1, 0) : (ZMod 2) × (ZMod 2)) ≠ 0 ∧
      ((0, 1) : (ZMod 2) × (ZMod 2)) ≠ 0 ∧
      ((1, 0) : (ZMod 2) × (ZMod 2)) * (0, 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact one_ne_zero (show (1 : ZMod 2) = 0 from congrArg Prod.fst h)
  · intro h
    exact one_ne_zero (show (1 : ZMod 2) = 0 from congrArg Prod.snd h)
  · apply Prod.ext <;> simp

private theorem zmod_two_prod_not_isDomain : ¬ IsDomain ((ZMod 2) × (ZMod 2)) := by
  intro h
  letI : IsDomain ((ZMod 2) × (ZMod 2)) := h
  exact (mul_eq_zero.mp zmod_two_prod_zero_divisors.2.2).elim
    zmod_two_prod_zero_divisors.1 zmod_two_prod_zero_divisors.2.1

private theorem zmod_two_prod_sq (x : (ZMod 2) × (ZMod 2)) : x ^ 2 = x := by
  rw [Prod.pow_def]
  exact Prod.ext (ZMod.pow_card x.1) (ZMod.pow_card x.2)

private theorem zmod_two_prod_frobenius_eq_self
    (x : WittVector 2 ((ZMod 2) × (ZMod 2))) :
    WittVector.frobenius x = x := by
  apply WittVector.ext
  intro n
  rw [WittVector.coeff_frobenius_charP]
  exact zmod_two_prod_sq (x.coeff n)

private theorem dual_number_charP : CharP (DualNumber (ZMod 2)) 2 := by
  exact charP_of_injective_ringHom
    (f := TrivSqZeroExt.inlHom (ZMod 2) (ZMod 2))
    TrivSqZeroExt.inl_injective 2

private theorem dual_number_eps_ne_zero :
    (DualNumber.eps : DualNumber (ZMod 2)) ≠ 0 := by
  intro h
  have h10 : (1 : ZMod 2) = 0 := by
    simpa only [DualNumber.snd_eps, TrivSqZeroExt.snd_zero] using
      congrArg (TrivSqZeroExt.snd : DualNumber (ZMod 2) → ZMod 2) h
  exact one_ne_zero h10

private theorem dual_number_eps_sq :
    (DualNumber.eps : DualNumber (ZMod 2)) ^ 2 = 0 := by
  exact DualNumber.eps_pow_two

private theorem dual_number_not_perfect : ¬ PerfectRing (DualNumber (ZMod 2)) 2 := by
  intro h
  have hinj : Function.Injective (fun x : DualNumber (ZMod 2) => x ^ 2) :=
    (@PerfectRing.bijective_frobenius (DualNumber (ZMod 2)) 2 _ h).1
  apply dual_number_eps_ne_zero
  apply hinj
  simpa only [zero_pow (by decide : 2 ≠ 0)] using dual_number_eps_sq

private theorem dual_number_teichmuller_eps_ne_zero :
    WittVector.teichmuller 2 (DualNumber.eps : DualNumber (ZMod 2)) ≠ 0 := by
  intro h
  apply dual_number_eps_ne_zero
  simpa only [WittVector.teichmuller_coeff_zero, WittVector.zero_coeff] using
    congrArg (fun x : WittVector 2 (DualNumber (ZMod 2)) => x.coeff 0) h

private theorem dual_number_frobenius_teichmuller_eps :
    WittVector.frobenius
      (WittVector.teichmuller 2 (DualNumber.eps : DualNumber (ZMod 2))) = 0 := by
  letI : CharP (DualNumber (ZMod 2)) 2 := dual_number_charP
  apply WittVector.ext
  intro n
  rw [WittVector.coeff_frobenius_charP]
  cases n with
  | zero =>
      rw [WittVector.teichmuller_coeff_zero, dual_number_eps_sq, WittVector.zero_coeff]
  | succ n =>
      rw [WittVector.teichmuller_coeff_pos 2 _ (n + 1) (Nat.succ_pos n),
        zero_pow (by decide : 2 ≠ 0), WittVector.zero_coeff]

private theorem dual_number_frobenius_not_injective :
    ¬ Function.Injective (@WittVector.frobenius 2 (DualNumber (ZMod 2)) _ _) := by
  intro h
  apply dual_number_teichmuller_eps_ne_zero
  apply h
  rw [dual_number_frobenius_teichmuller_eps, map_zero]

private theorem dual_number_frobenius_not_bijective :
    ¬ Function.Bijective (@WittVector.frobenius 2 (DualNumber (ZMod 2)) _ _) := by
  intro h
  exact dual_number_frobenius_not_injective h.1

private theorem zmod_two_prod_frobenius_bijective :
    Function.Bijective (@WittVector.frobenius 2 ((ZMod 2) × (ZMod 2)) _ _) := by
  exact (WittVector.frobenius_bijective_iff 2 ((ZMod 2) × (ZMod 2))).mpr
    zmod_two_prod_perfect

private theorem dual_number_frobenius_not_bijective_of_criterion :
    ¬ Function.Bijective (@WittVector.frobenius 2 (DualNumber (ZMod 2)) _ _) := by
  letI : CharP (DualNumber (ZMod 2)) 2 := dual_number_charP
  exact (WittVector.frobenius_bijective_iff 2 (DualNumber (ZMod 2))).not.mpr
    dual_number_not_perfect

end WittVector
