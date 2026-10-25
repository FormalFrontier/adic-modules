/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.WittVector
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Coeff
import AdicModules.RingTheory.WittVector
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.LocalRing.NonLocalRing
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.Identities
import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Witt vector arithmetic and Teichmüller expansions

Examples cover characteristic casts, units, locality, reducedness and prime multiplication.

Although `3` vanishes in each coefficient ring of the two characteristic-three
cast examples below, its cast into the Witt
vectors is nonzero. Besides the prime field `ZMod 3`, the characteristic-zero
tests include the nonperfect, nonfield coefficient ring `(ZMod 3)[X]`.

Over `ZMod 2`, the Witt vector ring is local and `2` is a nonzero nonunit.
Over `PowerSeries (ZMod 2)`, a local nonfield in which `X` is not a square,
Teichmüller representatives of `1 + X` and `X` give a unit and a nonunit.
The product `ZMod 2 × ZMod 2` gives a nonlocal Witt vector ring.

The reducedness examples at prime `2` use the mixed-characteristic reduced ring
`ℤ × ZMod 2`, where `2` is a nonzero zero divisor; the nonreduced ring `ZMod 4`,
whose Teichmüller lift of `2` is nonzero and square-zero; and the zero ring `ZMod 1`.

The coefficient ring `Polynomial (ZMod 3) × ZMod 3` is reduced, has nonzero zero
divisors, and is not perfect: a cube root of `(X, 0)` would give a polynomial
cube root of `X`, contradicting its degree. The regularity criterion gives
injectivity of multiplication by `3` on its Witt vectors.

In contrast, the trivial square-zero extension of `ZMod 3` by itself contains a
nonzero square-zero element. Its Teichmüller lift is nonzero and is killed by
`3`, as follows directly from the characteristic-three coefficient identities.
The coefficientwise kernel criterion also applies to this torsion element.
For perfect coefficient rings, the kernel criterion is compared with Mathlib's
zero-kernel theorem and injectivity of Frobenius.

The Teichmüller lifts of `1` over `ZMod 2` and of `X` over `(ZMod 2)[X]`
give nonzero finite expansions. Each canonical digit sequence satisfies every
approximation hypothesis and agrees with any digit sequence approximating the
same fixed Witt vector. The polynomial coefficient ring is reduced but not perfect.
-/

@[expose] public section

universe u

namespace WittVector

open Polynomial

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

example : (3 : WittVector 3 (ZMod 3)) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by decide)

example : (3 : WittVector 3 ((ZMod 3)[X])) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by decide)

/-- The Witt vectors over the field with two elements form a local ring in which
`2` is nonzero but not a unit. -/
theorem zmod_two_local_nonzero_nonunit :
    IsLocalRing (WittVector 2 (ZMod 2)) ∧
    (2 : WittVector 2 (ZMod 2)) ≠ 0 ∧
    ¬IsUnit (2 : WittVector 2 (ZMod 2)) := by
  refine ⟨(isLocalRing_iff (p := 2) (R := ZMod 2)).2 inferInstance, ?_, ?_⟩
  · exact Nat.cast_ne_zero.mpr (by decide)
  · rw [isUnit_iff_isUnit_coeff_zero]
    change ¬IsUnit (WittVector.constantCoeff (p := 2) (R := ZMod 2) 2)
    rw [map_ofNat, CharP.ofNat_eq_zero (ZMod 2) 2]
    exact not_isUnit_zero

/-- Power series over the field with two elements give local, nonfield coefficients
with nonsquare `X`. Their Witt vectors are local, with a unit represented by `1 + X`
and a nonunit represented by `X`. -/
theorem powerSeries_zmod_two_local_units :
    IsLocalRing (WittVector 2 (PowerSeries (ZMod 2))) ∧
    ¬IsField (PowerSeries (ZMod 2)) ∧
    (¬∃ f : PowerSeries (ZMod 2), f ^ 2 = PowerSeries.X) ∧
    IsUnit (WittVector.teichmuller 2
      (1 + PowerSeries.X : PowerSeries (ZMod 2))) ∧
    ¬IsUnit (WittVector.teichmuller 2
      (PowerSeries.X : PowerSeries (ZMod 2))) := by
  let : CharP (PowerSeries (ZMod 2)) 2 :=
    charP_of_injective_ringHom
      (f := PowerSeries.C (R := ZMod 2)) PowerSeries.C_injective 2
  refine ⟨(isLocalRing_iff (p := 2) (R := PowerSeries (ZMod 2))).2 inferInstance,
    PowerSeries.not_isField, ?_, ?_, ?_⟩
  · rintro ⟨f, hf⟩
    have h2 : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
    simpa [PowerSeries.coeff_one_pow, h2] using congrArg (PowerSeries.coeff 1) hf
  · rw [isUnit_iff_isUnit_coeff_zero, WittVector.teichmuller_coeff_zero,
      PowerSeries.isUnit_iff_constantCoeff]
    simp
  · rw [isUnit_iff_isUnit_coeff_zero, WittVector.teichmuller_coeff_zero,
      PowerSeries.isUnit_iff_constantCoeff]
    simp

/-- The product of two fields with two elements is a nonlocal coefficient ring,
and its Witt vector ring is nonlocal as well. -/
theorem prod_zmod_two_not_isLocalRing :
    ¬IsLocalRing (WittVector 2 (ZMod 2 × ZMod 2)) := by
  intro h
  exact IsLocalRing.not_isLocalRing_of_prod_of_nontrivial
    (ZMod 2) (ZMod 2)
    ((isLocalRing_iff (p := 2) (R := ZMod 2 × ZMod 2)).1 h)

-- Reducedness does not require a domain, prime characteristic, or regularity of `p`.
example : IsReduced (WittVector 2 (ℤ × ZMod 2)) ∧
    (2 : ℤ × ZMod 2) ≠ 0 ∧ ((0, 1) : ℤ × ZMod 2) ≠ 0 ∧
    (2 : ℤ × ZMod 2) * (0, 1) = 0 := by
  refine ⟨(isReduced_iff (p := 2) (R := ℤ × ZMod 2)).2 inferInstance, ?_, ?_, ?_⟩ <;>
    decide

-- A concrete square-zero lift and the converse direction of the reducedness equivalence.
example : teichmuller 2 (2 : ZMod 4) ≠ 0 ∧
    (teichmuller 2 (2 : ZMod 4)) ^ 2 = 0 ∧ ¬ IsReduced (WittVector 2 (ZMod 4)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hz : (2 : ZMod 4) = 0 := by
      simpa only [teichmuller_coeff_zero, zero_coeff]
        using congrArg (fun w : WittVector 2 (ZMod 4) => w.coeff 0) h
    exact (by decide : (2 : ZMod 4) ≠ 0) hz
  · rw [← map_pow, show (2 : ZMod 4) ^ 2 = 0 by decide, teichmuller_zero]
  · intro hw
    have : IsReduced (ZMod 4) := (isReduced_iff (p := 2) (R := ZMod 4)).1 hw
    exact (by decide : (2 : ZMod 4) ≠ 0)
      (eq_zero_of_pow_eq_zero (n := 2) (by decide : (2 : ZMod 4) ^ 2 = 0))

-- The zero coefficient ring is allowed, without a prime-characteristic premise.
example : (0 : ZMod 1) = 1 ∧ Subsingleton (WittVector 2 (ZMod 1)) ∧
    IsReduced (WittVector 2 (ZMod 1)) := by
  refine ⟨Subsingleton.elim _ _, ?_,
    (isReduced_iff (p := 2) (R := ZMod 1)).2 inferInstance⟩
  exact ⟨fun x y => WittVector.ext fun n => Subsingleton.elim _ _⟩

/-- The nonzero Teichmüller lift of `1` over `ZMod 2` has the canonical finite
digit expansion, which agrees with every expansion of the same Witt vector. -/
theorem teichmuller_expansion_zmod_two :
    teichmuller 2 (1 : ZMod 2) ≠ 0 ∧
    (∀ n : ℕ, (2 : WittVector 2 (ZMod 2)) ^ (n + 1) ∣
      teichmuller 2 (1 : ZMod 2) - ∑ i ∈ Finset.range (n + 1),
        teichmuller 2 (if i = 0 then (1 : ZMod 2) else 0) *
          (2 : WittVector 2 (ZMod 2)) ^ i) ∧
    (∀ b : ℕ → ZMod 2,
      (∀ n : ℕ, (2 : WittVector 2 (ZMod 2)) ^ (n + 1) ∣
        teichmuller 2 (1 : ZMod 2) - ∑ i ∈ Finset.range (n + 1),
          teichmuller 2 (b i) * (2 : WittVector 2 (ZMod 2)) ^ i) →
      (fun i : ℕ => if i = 0 then (1 : ZMod 2) else 0) = b) := by
  have ha : ∀ n : ℕ, (2 : WittVector 2 (ZMod 2)) ^ (n + 1) ∣
      teichmuller 2 (1 : ZMod 2) - ∑ i ∈ Finset.range (n + 1),
        teichmuller 2 (if i = 0 then (1 : ZMod 2) else 0) *
          (2 : WittVector 2 (ZMod 2)) ^ i := by
    intro n
    have hs : (∑ i ∈ Finset.range (n + 1),
        teichmuller 2 (if i = 0 then (1 : ZMod 2) else 0) *
          (2 : WittVector 2 (ZMod 2)) ^ i) = teichmuller 2 (1 : ZMod 2) := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro i hi hi0
        simp [hi0]
      · intro h0
        exact (h0 (Finset.mem_range.mpr (Nat.succ_pos n))).elim
    rw [hs, sub_self]
    exact dvd_zero _
  refine ⟨?_, ha, ?_⟩
  · intro h
    have hcoeff := congrArg (fun z : WittVector 2 (ZMod 2) => z.coeff 0) h
    apply (one_ne_zero : (1 : ZMod 2) ≠ 0)
    simpa only [teichmuller_coeff_zero, zero_coeff] using hcoeff
  · intro b hb
    exact teichmuller_expansion_unique (p := 2) (R := ZMod 2)
      (teichmuller 2 (1 : ZMod 2))
      (fun i : ℕ => if i = 0 then (1 : ZMod 2) else 0) b ha hb

/-- The nonzero Teichmüller lift of `X` over `(ZMod 2)[X]` has a canonical finite
expansion agreeing with every expansion, over a reduced, nonperfect ring. -/
theorem teichmuller_expansion_polynomial_zmod_two :
    teichmuller 2 (Polynomial.X : Polynomial (ZMod 2)) ≠ 0 ∧
    (∀ n : ℕ, (2 : WittVector 2 (Polynomial (ZMod 2))) ^ (n + 1) ∣
      teichmuller 2 (Polynomial.X : Polynomial (ZMod 2)) -
        ∑ i ∈ Finset.range (n + 1),
          teichmuller 2 (if i = 0 then (Polynomial.X : Polynomial (ZMod 2)) else 0) *
            (2 : WittVector 2 (Polynomial (ZMod 2))) ^ i) ∧
    (∀ b : ℕ → Polynomial (ZMod 2),
      (∀ n : ℕ, (2 : WittVector 2 (Polynomial (ZMod 2))) ^ (n + 1) ∣
        teichmuller 2 (Polynomial.X : Polynomial (ZMod 2)) -
          ∑ i ∈ Finset.range (n + 1),
            teichmuller 2 (b i) * (2 : WittVector 2 (Polynomial (ZMod 2))) ^ i) →
      (fun i : ℕ => if i = 0 then (Polynomial.X : Polynomial (ZMod 2)) else 0) = b) := by
  have ha : ∀ n : ℕ, (2 : WittVector 2 (Polynomial (ZMod 2))) ^ (n + 1) ∣
      teichmuller 2 (Polynomial.X : Polynomial (ZMod 2)) -
        ∑ i ∈ Finset.range (n + 1),
          teichmuller 2 (if i = 0 then (Polynomial.X : Polynomial (ZMod 2)) else 0) *
            (2 : WittVector 2 (Polynomial (ZMod 2))) ^ i := by
    intro n
    have hs : (∑ i ∈ Finset.range (n + 1),
        teichmuller 2 (if i = 0 then (Polynomial.X : Polynomial (ZMod 2)) else 0) *
          (2 : WittVector 2 (Polynomial (ZMod 2))) ^ i) =
        teichmuller 2 (Polynomial.X : Polynomial (ZMod 2)) := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro i hi hi0
        simp [hi0]
      · intro h0
        exact (h0 (Finset.mem_range.mpr (Nat.succ_pos n))).elim
    rw [hs, sub_self]
    exact dvd_zero _
  refine ⟨?_, ha, ?_⟩
  · intro h
    have hcoeff :=
      congrArg (fun z : WittVector 2 (Polynomial (ZMod 2)) => z.coeff 0) h
    apply (Polynomial.X_ne_zero : (Polynomial.X : Polynomial (ZMod 2)) ≠ 0)
    simpa only [teichmuller_coeff_zero, zero_coeff] using hcoeff
  · intro b hb
    exact teichmuller_expansion_unique (p := 2) (R := Polynomial (ZMod 2))
      (teichmuller 2 (Polynomial.X : Polynomial (ZMod 2)))
      (fun i : ℕ => if i = 0 then (Polynomial.X : Polynomial (ZMod 2)) else 0) b ha hb

private theorem polynomial_zmod_three_prod_zero_divisors :
    ((1, 0) : Polynomial (ZMod 3) × ZMod 3) ≠ 0 ∧
      ((0, 1) : Polynomial (ZMod 3) × ZMod 3) ≠ 0 ∧
      ((1, 0) : Polynomial (ZMod 3) × ZMod 3) * (0, 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact one_ne_zero (congrArg Prod.fst h)
  · intro h
    exact one_ne_zero (congrArg Prod.snd h)
  · ext <;> simp

private theorem polynomial_zmod_three_prod_X_not_cube :
    ¬ ∃ y : Polynomial (ZMod 3) × ZMod 3, y ^ 3 = (X, 0) := by
  rintro ⟨y, hy⟩
  have hpoly : y.1 ^ 3 = (X : Polynomial (ZMod 3)) := by
    simpa only [map_pow, RingHom.coe_fst] using
      congrArg (RingHom.fst (Polynomial (ZMod 3)) (ZMod 3)) hy
  have hdegree := congrArg Polynomial.natDegree hpoly
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X] at hdegree
  exact (by decide : ¬ (3 : ℕ) ∣ 1) ⟨y.1.natDegree, hdegree.symm⟩

private theorem polynomial_zmod_three_prod_not_perfect :
    ¬ PerfectRing (Polynomial (ZMod 3) × ZMod 3) 3 := by
  rintro ⟨⟨_, hsurj⟩⟩
  exact polynomial_zmod_three_prod_X_not_cube (hsurj (X, 0))

private theorem polynomial_zmod_three_prod_mul_three_injective :
    Function.Injective (fun x : WittVector 3 (Polynomial (ZMod 3) × ZMod 3) =>
      x * (3 : WittVector 3 (Polynomial (ZMod 3) × ZMod 3))) := by
  exact ((isRegular_p_iff_isReduced (p := 3)
    (k := Polynomial (ZMod 3) × ZMod 3)).mpr
    (inferInstance : IsReduced (Polynomial (ZMod 3) × ZMod 3))).right

private theorem trivSqZeroExt_zmod_three_epsilon_ne_zero :
    (TrivSqZeroExt.inr (1 : ZMod 3) : TrivSqZeroExt (ZMod 3) (ZMod 3)) ≠ 0 := by
  intro h
  apply (one_ne_zero : (1 : ZMod 3) ≠ 0)
  simpa only [TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero] using
    congrArg (TrivSqZeroExt.snd : TrivSqZeroExt (ZMod 3) (ZMod 3) → ZMod 3) h

private theorem trivSqZeroExt_zmod_three_epsilon_sq_eq_zero :
    (TrivSqZeroExt.inr (1 : ZMod 3) : TrivSqZeroExt (ZMod 3) (ZMod 3)) ^ 2 = 0 := by
  rw [pow_two]
  exact TrivSqZeroExt.inr_mul_inr (ZMod 3) (1 : ZMod 3) (1 : ZMod 3)

private theorem trivSqZeroExt_zmod_three_epsilon_cube_eq_zero :
    (TrivSqZeroExt.inr (1 : ZMod 3) : TrivSqZeroExt (ZMod 3) (ZMod 3)) ^ 3 = 0 := by
  exact pow_eq_zero_of_le (by decide : 2 ≤ 3)
    trivSqZeroExt_zmod_three_epsilon_sq_eq_zero

private theorem trivSqZeroExt_zmod_three_teichmuller_torsion :
    teichmuller 3 (TrivSqZeroExt.inr (1 : ZMod 3) : TrivSqZeroExt (ZMod 3) (ZMod 3)) ≠ 0 ∧
      teichmuller 3 (TrivSqZeroExt.inr (1 : ZMod 3) : TrivSqZeroExt (ZMod 3) (ZMod 3)) *
        (3 : WittVector 3 (TrivSqZeroExt (ZMod 3) (ZMod 3))) = 0 := by
  have : CharP (TrivSqZeroExt (ZMod 3) (ZMod 3)) 3 :=
    charP_of_injective_ringHom
      (f := TrivSqZeroExt.inlHom (ZMod 3) (ZMod 3)) TrivSqZeroExt.inl_injective 3
  constructor
  · intro h
    apply trivSqZeroExt_zmod_three_epsilon_ne_zero
    simpa only [teichmuller_coeff_zero, zero_coeff] using
      congrArg (fun x : WittVector 3 (TrivSqZeroExt (ZMod 3) (ZMod 3)) => x.coeff 0) h
  · apply WittVector.ext
    intro n
    cases n with
    | zero =>
        simpa only [Nat.cast_ofNat, zero_coeff] using mul_charP_coeff_zero (p := 3)
          (teichmuller 3
            (TrivSqZeroExt.inr (1 : ZMod 3) : TrivSqZeroExt (ZMod 3) (ZMod 3)))
    | succ n =>
        rw [← Nat.cast_ofNat (R := WittVector 3 (TrivSqZeroExt (ZMod 3) (ZMod 3))) (n := 3),
          mul_charP_coeff_succ (p := 3), zero_coeff]
        cases n with
        | zero =>
            simpa only [teichmuller_coeff_zero] using
              trivSqZeroExt_zmod_three_epsilon_cube_eq_zero
        | succ n =>
            rw [teichmuller_coeff_pos 3 _ _ (Nat.succ_pos _), zero_pow (by decide)]

private theorem trivSqZeroExt_zmod_three_teichmuller_coeff_cube_eq_zero :
    ∀ n : ℕ,
      (teichmuller 3
        (TrivSqZeroExt.inr (1 : ZMod 3) : TrivSqZeroExt (ZMod 3) (ZMod 3))).coeff n ^ 3 = 0 := by
  have : CharP (TrivSqZeroExt (ZMod 3) (ZMod 3)) 3 :=
    charP_of_injective_ringHom
      (f := TrivSqZeroExt.inlHom (ZMod 3) (ZMod 3)) TrivSqZeroExt.inl_injective 3
  exact (mul_p_eq_zero_iff_coeff_pow_eq_zero
    (teichmuller 3
      (TrivSqZeroExt.inr (1 : ZMod 3) : TrivSqZeroExt (ZMod 3) (ZMod 3)))).mp
    trivSqZeroExt_zmod_three_teichmuller_torsion.2

private theorem perfect_mul_p_kernel_comparison
    {p : ℕ} [hp : Fact p.Prime] {k : Type u} [CommRing k] [CharP k p]
    [PerfectRing k p] (x : WittVector p k) :
    x * (p : WittVector p k) = 0 ↔ ∀ n : ℕ, x.coeff n ^ p = 0 := by
  constructor
  · intro h n
    rw [eq_zero_of_p_mul_eq_zero x h, zero_coeff, zero_pow hp.out.ne_zero]
  · intro h
    have hx : x = 0 := by
      apply WittVector.ext
      intro n
      rw [zero_coeff]
      apply _root_.injective_frobenius k p
      change x.coeff n ^ p = (0 : k) ^ p
      rw [h n, zero_pow hp.out.ne_zero]
    rw [hx, zero_mul]

/-- The same reduced, imperfect product ring has a Teichmüller lift that survives every
power of `3`; the case `n = 0` also detects that the lift itself is nonzero. -/
private theorem polynomial_zmod_three_prod_teichmuller_mul_three_pow_ne_zero (n : ℕ) :
    teichmuller 3 ((X, 0) : Polynomial (ZMod 3) × ZMod 3) *
      (3 : WittVector 3 (Polynomial (ZMod 3) × ZMod 3)) ^ n ≠ 0 := by
  intro h
  have hcoeff := (mul_p_pow_eq_zero_iff_coeff_pow_eq_zero
    (teichmuller 3 ((X, 0) : Polynomial (ZMod 3) × ZMod 3)) n).mp h 0
  have hX : (X : Polynomial (ZMod 3)) ^ (3 ^ n) = 0 := by
    simpa only [teichmuller_coeff_zero, map_pow, map_zero, RingHom.coe_fst] using
      congrArg (RingHom.fst (Polynomial (ZMod 3)) (ZMod 3)) hcoeff
  exact (pow_ne_zero _ Polynomial.X_ne_zero) hX

/-- In `(ZMod 3)[X]/(X^4)`, the Teichmüller lift of the root is nonzero and is killed
by `3^2`, but not by `3`. -/
private theorem adjoinRoot_zmod_three_X_fourth_teichmuller_torsion :
    teichmuller 3 (AdjoinRoot.root ((X : Polynomial (ZMod 3)) ^ 4)) ≠ 0 ∧
      teichmuller 3 (AdjoinRoot.root ((X : Polynomial (ZMod 3)) ^ 4)) *
        (3 : WittVector 3 (AdjoinRoot ((X : Polynomial (ZMod 3)) ^ 4))) ≠ 0 ∧
      teichmuller 3 (AdjoinRoot.root ((X : Polynomial (ZMod 3)) ^ 4)) *
        (3 : WittVector 3 (AdjoinRoot ((X : Polynomial (ZMod 3)) ^ 4))) ^ 2 = 0 := by
  let f : Polynomial (ZMod 3) := X ^ 4
  let t : AdjoinRoot f := AdjoinRoot.root f
  let x : WittVector 3 (AdjoinRoot f) := teichmuller 3 t
  have hf : f.Monic := Polynomial.monic_X_pow 4
  have : CharP (AdjoinRoot f) 3 :=
    charP_of_injective_ringHom (f := AdjoinRoot.of f)
      (AdjoinRoot.of.injective_of_monic_of_degree_pos hf (by simp [f])) 3
  have ht_cube : t ^ 3 ≠ 0 := by
    have h := AdjoinRoot.mk_ne_zero_of_natDegree_lt (f := f) hf
      (g := (X : Polynomial (ZMod 3)) ^ 3)
      (pow_ne_zero 3 Polynomial.X_ne_zero) (by simp [f])
    simpa only [map_pow, AdjoinRoot.mk_X, t] using h
  have ht_fourth : t ^ 4 = 0 := by
    calc
      t ^ 4 = AdjoinRoot.mk f ((X : Polynomial (ZMod 3)) ^ 4) :=
        (map_pow (AdjoinRoot.mk f) X 4).symm
      _ = 0 := AdjoinRoot.mk_self
  change x ≠ 0 ∧ x * (3 : WittVector 3 (AdjoinRoot f)) ≠ 0 ∧
    x * (3 : WittVector 3 (AdjoinRoot f)) ^ 2 = 0
  refine ⟨?_, ?_, ?_⟩
  · intro hx
    have ht : t = 0 := by
      simpa only [x, teichmuller_coeff_zero, zero_coeff] using
        congrArg (fun y : WittVector 3 (AdjoinRoot f) => y.coeff 0) hx
    apply ht_cube
    rw [ht, zero_pow (by decide)]
  · intro hx
    apply ht_cube
    simpa only [x, teichmuller_coeff_zero] using
      (mul_p_eq_zero_iff_coeff_pow_eq_zero x).mp hx 0
  · apply (mul_p_pow_eq_zero_iff_coeff_pow_eq_zero x 2).mpr
    intro i
    cases i with
    | zero =>
        change t ^ (3 ^ 2) = 0
        exact pow_eq_zero_of_le (by decide : 4 ≤ 3 ^ 2) ht_fourth
    | succ i =>
        change (teichmuller 3 t).coeff (i + 1) ^ (3 ^ 2) = 0
        rw [teichmuller_coeff_pos 3 _ _ (Nat.succ_pos _), zero_pow (by decide)]

/-- The characteristic-`p` hypothesis in the coefficientwise multiplication kernel
criterion is necessary: over `ZMod 4`, the Teichmüller lift of `2` has zero cubed
coefficients but is not killed by `3`. -/
private theorem zmod_four_teichmuller_coeff_cube_zero_mul_three_ne_zero :
    ¬CharP (ZMod 4) 3 ∧
      (∀ i : ℕ, (teichmuller 3 (2 : ZMod 4)).coeff i ^ 3 = 0) ∧
      teichmuller 3 (2 : ZMod 4) * (3 : WittVector 3 (ZMod 4)) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : CharP (ZMod 4) 3 := h
    exact (by decide : (3 : ZMod 4) ≠ 0) (CharP.cast_eq_zero (ZMod 4) 3)
  · intro i
    cases i with
    | zero =>
        rw [teichmuller_coeff_zero]
        decide
    | succ i =>
        rw [teichmuller_coeff_pos 3 _ _ (Nat.succ_pos _), zero_pow (by decide)]
  · intro h
    have hcoeff := congrArg (constantCoeff : WittVector 3 (ZMod 4) →+* ZMod 4) h
    rw [map_mul,
      map_ofNat (constantCoeff : WittVector 3 (ZMod 4) →+* ZMod 4) 3,
      map_zero, constantCoeff_apply, teichmuller_coeff_zero] at hcoeff
    exact (by decide : (2 : ZMod 4) * 3 ≠ 0) hcoeff

end WittVector
