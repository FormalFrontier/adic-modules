/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Algebra.Module.Int
public import Mathlib.LinearAlgebra.Matrix.Defs

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Data.Matrix.Basis
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Integer singleton-span clients

The integers and every `ZMod n` have surjective integer casts and are generated
by `1` as integer modules. The span of `2` in the integers is nevertheless
proper, so a proper singleton span does not imply nonsurjectivity of casts.
The `ZMod 0`, `ZMod 1` and subsingleton cases retain the characteristic-zero
and zero-ring boundaries.

For two-by-two integer matrices, an off-diagonal matrix unit is not an integer
cast, hence every singleton integer span is proper. Two off-diagonal matrix
units fail to commute, and the integer span of one of them contains itself but
not the identity matrix. These clients use Mathlib's matrix-unit and
singleton-span interfaces without introducing a new ring or scalar action.
-/

@[expose] public section

universe u

namespace AdicModulesTest.IntSpan

private lemma int_span_one_eq_top :
    Submodule.span ℤ ({1} : Set ℤ) = ⊤ := by
  apply (Submodule.span_singleton_eq_top_iff ℤ (1 : ℤ)).2
  intro z
  exact ⟨z, by simp⟩

private lemma int_cast_surjective : Function.Surjective (Int.cast : ℤ → ℤ) :=
  Submodule.intCast_surjective_of_span_singleton_eq_top int_span_one_eq_top

private lemma int_one_notMem_span_two :
    (1 : ℤ) ∉ Submodule.span ℤ ({2} : Set ℤ) := by
  intro h
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp h
  have hmul : (2 : ℤ) * z = 1 := by
    simpa only [smul_eq_mul, mul_comm] using hz
  have hunit := Int.eq_one_or_neg_one_of_mul_eq_one hmul
  exact (by decide : ¬ ((2 : ℤ) = 1 ∨ (2 : ℤ) = -1)) hunit

/-- Integer casts into the integers are surjective, but the integer span of `2`
is proper: it misses `1`. Thus properness of one singleton span does not imply
nonsurjectivity of integer casts. -/
lemma _root_.Int.cast_surjective_and_span_two_ne_top :
    Function.Surjective (Int.cast : ℤ → ℤ) ∧
      Submodule.span ℤ ({2} : Set ℤ) ≠ ⊤ := by
  refine ⟨int_cast_surjective, ?_⟩
  intro htop
  apply int_one_notMem_span_two
  rw [htop]
  exact Submodule.mem_top

private lemma zmod_span_one_eq_top (n : ℕ) :
    Submodule.span ℤ ({1} : Set (ZMod n)) = ⊤ := by
  apply (Submodule.span_singleton_eq_top_iff ℤ (1 : ZMod n)).2
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  exact ⟨z, Int.smul_one_eq_cast z⟩

private lemma zmod_cast_surjective (n : ℕ) :
    Function.Surjective (Int.cast : ℤ → ZMod n) :=
  IsAddCyclic.intCast_surjective

private lemma zmod_zero_span_one_eq_top :
    Submodule.span ℤ ({1} : Set (ZMod 0)) = ⊤ :=
  zmod_span_one_eq_top 0

private lemma zmod_zero_cast_surjective :
    Function.Surjective (Int.cast : ℤ → ZMod 0) :=
  zmod_cast_surjective 0

private lemma subsingleton_span_eq_top
    {R : Type u} [NonAssocRing R] [Subsingleton R] (x : R) :
    Submodule.span ℤ ({x} : Set R) = ⊤ := by
  apply (Submodule.span_singleton_eq_top_iff ℤ x).2
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

private lemma subsingleton_span_eq_bot
    {R : Type u} [NonAssocRing R] [Subsingleton R] (x : R) :
    Submodule.span ℤ ({x} : Set R) = ⊥ := by
  rw [Subsingleton.elim x (0 : R), Submodule.span_zero_singleton]

private lemma subsingleton_cast_surjective
    {R : Type u} [NonAssocRing R] [Subsingleton R] :
    Function.Surjective (Int.cast : ℤ → R) :=
  IsAddCyclic.intCast_surjective

private lemma zmod_one_zero_span_eq_top_and_top_eq_bot :
    Submodule.span ℤ ({0} : Set (ZMod 1)) = ⊤ ∧
      (⊤ : Submodule ℤ (ZMod 1)) = ⊥ :=
  ⟨subsingleton_span_eq_top 0,
    (subsingleton_span_eq_top (0 : ZMod 1)).symm.trans (subsingleton_span_eq_bot 0)⟩

private lemma zmod_one_cast_surjective :
    Function.Surjective (Int.cast : ℤ → ZMod 1) :=
  subsingleton_cast_surjective

private lemma matrix_offDiagonal_not_intCast (z : ℤ) :
    (z : Matrix (Fin 2) (Fin 2) ℤ) ≠ Matrix.single 0 1 1 := by
  intro h
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ ↦ A 0 1) h
  have h01' : (0 : ℤ) = 1 := by
    simpa only [Matrix.intCast_apply, Matrix.single_apply_same, Int.cast_zero,
      ite_eq_right (by decide : (0 : Fin 2) ≠ 1)] using h01
  exact zero_ne_one h01'

private lemma matrix_cast_not_surjective :
    ¬ Function.Surjective (Int.cast : ℤ → Matrix (Fin 2) (Fin 2) ℤ) := by
  intro h
  obtain ⟨z, hz⟩ := h (Matrix.single 0 1 (1 : ℤ))
  exact matrix_offDiagonal_not_intCast z hz

/-- Every singleton integer span in the two-by-two integer matrix ring is proper,
including the span of zero. The matrix unit `Matrix.single 0 1 1` is not an
integer cast, so this ring satisfies the nonsurjectivity hypothesis of
`Submodule.int_span_singleton_ne_top_of_not_surjective_intCast`.

The span of this nonzero matrix unit contains itself but not the identity matrix;
the matrix units at `(0, 1)` and `(1, 0)` do not commute. -/
lemma _root_.Matrix.int_span_singleton_ne_top (x : Matrix (Fin 2) (Fin 2) ℤ) :
    Submodule.span ℤ ({x} : Set (Matrix (Fin 2) (Fin 2) ℤ)) ≠ ⊤ :=
  Submodule.int_span_singleton_ne_top_of_not_surjective_intCast
    matrix_cast_not_surjective x

private lemma matrix_offDiagonal_mem_own_span :
    Matrix.single 0 1 (1 : ℤ) ∈
      Submodule.span ℤ ({Matrix.single 0 1 1} : Set (Matrix (Fin 2) (Fin 2) ℤ)) :=
  Submodule.mem_span_singleton_self _

private lemma matrix_one_notMem_offDiagonal_span :
    (1 : Matrix (Fin 2) (Fin 2) ℤ) ∉
      Submodule.span ℤ ({Matrix.single 0 1 1} : Set (Matrix (Fin 2) (Fin 2) ℤ)) := by
  intro h
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp h
  rw [Matrix.smul_single] at hz
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ ↦ A 0 0) hz
  have h00' : (0 : ℤ) = 1 := by
    simpa only [Matrix.single_apply_of_ne (0 : Fin 2) 1 (z • (1 : ℤ)) 0 0
      (by decide : ¬ ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 0)),
      Matrix.one_apply_eq] using h00
  exact zero_ne_one h00'

private lemma matrix_offDiagonal_units_not_commute :
    (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℤ) *
        (Matrix.single 1 0 1 : Matrix (Fin 2) (Fin 2) ℤ) ≠
      (Matrix.single 1 0 1 : Matrix (Fin 2) (Fin 2) ℤ) *
        (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ ↦ A 0 0) h
  have h00' : (1 : ℤ) = 0 := by
    simpa only [Matrix.single_mul_single_same, one_mul, Matrix.single_apply_same,
      Matrix.single_apply,
      ite_eq_right (by decide : ¬ ((1 : Fin 2) = 0 ∧ (1 : Fin 2) = 0))] using h00
  exact one_ne_zero h00'

end AdicModulesTest.IntSpan
