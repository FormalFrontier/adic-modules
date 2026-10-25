/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianPi
import AdicModules.RingTheory.HenselianTransport
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.NonLocalRing
import Mathlib.Tactic.NormNum

/-!
# A mixed-coordinate ideal in a finite diagonal algebra

The diagonal from the 2-adic integers to their square is finite free, hence
integral and faithfully flat. The coordinate ideals (2) and (4) give a
Henselian pair by the dependent-Pi instance and downward closure from the stock
maximal-ideal instance. Its contraction is (4), but extending that contraction
is strictly smaller than the mixed-coordinate ideal.

Contraction and strictness are computed directly by coordinate membership.
The scalar action is the canonical action of the diagonal algebra map.
-/

namespace HenselianIntegralComap

private abbrev R := ℤ_[2]
private abbrev S := Fin 2 → R
private noncomputable abbrev f : R →+* S := algebraMap R S
private noncomputable abbrev twoIdeal : Ideal R := Ideal.span {(2 : R)}
private noncomputable abbrev fourIdeal : Ideal R := Ideal.span {(4 : R)}
private noncomputable abbrev coordinateIdeal (i : Fin 2) : Ideal R :=
  if i = 0 then twoIdeal else fourIdeal
private noncomputable abbrev J : Ideal S := Ideal.pi coordinateIdeal

private theorem two_eq_maximal : twoIdeal = IsLocalRing.maximalIdeal R :=
  (PadicInt.maximalIdeal_eq_span_p (p := 2)).symm

private theorem two_ne_top : twoIdeal ≠ ⊤ := by
  rw [two_eq_maximal]
  exact Ideal.IsMaximal.ne_top inferInstance

private theorem four_le_two : fourIdeal ≤ twoIdeal :=
  Ideal.span_singleton_le_span_singleton.mpr ⟨(2 : R), by norm_num⟩

private theorem two_ne_zero : (2 : R) ≠ 0 := PadicInt.prime_p.ne_zero

private theorem four_ne_zero : (4 : R) ≠ 0 := by norm_num

/-- Integrality uses the finite canonical Pi algebra. -/
private theorem diagonal_integral : RingHom.IsIntegral f :=
  algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R S)

/-- The finite Pi module is free and nontrivial with its canonical action. -/
private theorem diagonal_faithfullyFlat : RingHom.FaithfullyFlat f :=
  RingHom.faithfullyFlat_algebraMap_iff.mpr
    (inferInstance : Module.FaithfullyFlat R S)

/-- The mixed-coordinate ideal is Henselian. -/
private theorem target_henselian : HenselianRing S J := by
  let : HenselianRing R twoIdeal := by
    rw [two_eq_maximal]
    infer_instance
  let : HenselianRing R fourIdeal := HenselianRing.of_le four_le_two
  let (i : Fin 2) : HenselianRing R (coordinateIdeal i) := by
    by_cases hi : i = 0 <;> simp only [coordinateIdeal, hi, ite_true, ite_false] <;>
      infer_instance
  exact HenselianRing.pi coordinateIdeal

/-- A diagonal tuple belongs to both coordinate ideals precisely when it is in (4). -/
private theorem contraction_eq_four : J.comap f = fourIdeal := by
  ext x
  change (∀ i : Fin 2, x ∈ coordinateIdeal i) ↔ x ∈ fourIdeal
  constructor
  · intro h
    simpa only [coordinateIdeal, show (1 : Fin 2) ≠ 0 by decide, ite_false] using h 1
  · intro hx i
    by_cases hi : i = 0
    · simpa only [coordinateIdeal, hi, ite_true] using four_le_two hx
    · simpa only [coordinateIdeal, hi, ite_false] using hx

private theorem two_not_mem_four : (2 : R) ∉ fourIdeal := by
  intro h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h
  have hmul : (2 : R) * 2 = 4 := by norm_num
  have ha' : a * (2 : R) = 1 := by
    apply mul_right_cancel₀ two_ne_zero
    simpa only [mul_assoc, hmul, one_mul] using ha
  have hunit : IsUnit (2 : R) :=
    isUnit_iff_exists.mpr ⟨a, (mul_comm _ _).trans ha', ha'⟩
  exact two_ne_top (Ideal.span_singleton_eq_top.mpr hunit)

/-- Extension of the contraction has (4) in both coordinates. -/
private theorem extension_eq_pi_four :
    (J.comap f).map f = Ideal.pi (fun _ : Fin 2 => fourIdeal) := by
  rw [contraction_eq_four, Ideal.map_span, Set.image_singleton]
  exact (Ideal.pi_span (r := fun _ : Fin 2 => (4 : R))).symm

private noncomputable abbrev offDiagonal : S := fun i => if i = 0 then 2 else 0

private theorem offDiagonal_mem : offDiagonal ∈ J := by
  apply (Ideal.mem_pi coordinateIdeal offDiagonal).mpr
  intro i
  by_cases hi : i = 0
  · simpa only [offDiagonal, coordinateIdeal, hi, ite_true] using
      Ideal.mem_span_singleton_self (2 : R)
  · simp only [offDiagonal, coordinateIdeal, hi, ite_false, Ideal.zero_mem]

private theorem offDiagonal_not_mem_extension : offDiagonal ∉ (J.comap f).map f := by
  rw [extension_eq_pi_four]
  intro h
  exact two_not_mem_four (by
    simpa [offDiagonal] using (Ideal.mem_pi (fun _ : Fin 2 => fourIdeal) _).mp h 0)

/-- The mixed-coordinate ideal is not the extension of its contraction. -/
private theorem extension_lt : (J.comap f).map f < J := by
  refine lt_of_le_of_ne Ideal.map_comap_le ?_
  intro h
  exact offDiagonal_not_mem_extension (h.symm ▸ offDiagonal_mem)

private theorem offDiagonal_not_nilpotent : ¬ IsNilpotent offDiagonal := by
  intro h
  apply two_ne_zero
  simpa [offDiagonal] using
    (h.map (Pi.evalRingHom (fun _ : Fin 2 => R) 0)).eq_zero

/-- The contraction is proper and contains the nonzero, nonnilpotent element 4. -/
private theorem contraction_boundaries :
    J.comap f ≠ ⊥ ∧ J.comap f ≠ ⊤ ∧
      (4 : R) ∈ J.comap f ∧ ¬ IsNilpotent (4 : R) := by
  rw [contraction_eq_four]
  refine ⟨?_, ?_, Ideal.mem_span_singleton_self _, ?_⟩
  · intro h
    exact four_ne_zero (Ideal.mem_bot.mp (h ▸ Ideal.mem_span_singleton_self (4 : R)))
  · intro h
    exact two_ne_top (top_unique (h ▸ four_le_two))
  · intro h
    exact four_ne_zero h.eq_zero

/-- The target is nonlocal, and its proper ideal has a nonnilpotent coordinate witness. -/
private theorem target_boundaries :
    J ≠ ⊥ ∧ J ≠ ⊤ ∧ offDiagonal ∈ J ∧
      ¬ IsNilpotent offDiagonal ∧ ¬ IsLocalRing S := by
  refine ⟨?_, ?_, offDiagonal_mem, offDiagonal_not_nilpotent,
    IsLocalRing.not_isLocalRing_of_nontrivial_pi (fun _ : Fin 2 => R)⟩
  · intro h
    have hz : offDiagonal = 0 := Ideal.mem_bot.mp (h ▸ offDiagonal_mem)
    exact two_ne_zero (by simpa [offDiagonal] using congrFun hz 0)
  · intro h
    exact contraction_boundaries.2.1 (by rw [h, Ideal.comap_top])

/-- The mixed-coordinate ideal contracts to a Henselian ideal. -/
private theorem contraction_henselian : HenselianRing R (J.comap f) := by
  let : HenselianRing S J := target_henselian
  exact HenselianRing.comap_of_isIntegral_of_faithfullyFlat
    J f diagonal_integral diagonal_faithfullyFlat

#print axioms target_henselian
#print axioms extension_lt

example : (Ideal.henselianRadical S).comap f = Ideal.henselianRadical R := by
  exact Ideal.comap_henselianRadical_of_isIntegral_of_faithfullyFlat
    f diagonal_integral diagonal_faithfullyFlat

end HenselianIntegralComap
