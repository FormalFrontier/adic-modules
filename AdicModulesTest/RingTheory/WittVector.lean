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
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.Identities
import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Characteristic casts and prime multiplication and Teichmüller expansions in Witt vectors

Although `3` vanishes in each coefficient ring of the two characteristic-three
cast examples below, its cast into the Witt
vectors is nonzero. Besides the prime field `ZMod 3`, the characteristic-zero
tests include the nonperfect, nonfield coefficient ring `(ZMod 3)[X]`.

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
  letI : CharP (TrivSqZeroExt (ZMod 3) (ZMod 3)) 3 :=
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
  letI : CharP (TrivSqZeroExt (ZMod 3) (ZMod 3)) 3 :=
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

end WittVector
