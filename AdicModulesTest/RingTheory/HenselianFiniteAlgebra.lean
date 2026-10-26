/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianFiniteAlgebra
import Mathlib.Algebra.Group.Prod
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finite algebras over a Henselian local ring: the diagonal 2-adic product

The diagonal algebra of pairs of 2-adic integers is finite over the 2-adic
integers, but is neither zero nor local. Its complementary coordinate elements
are nonunits whose sum is one.
-/

noncomputable section

universe u v

-- Quotient factors retain module finiteness through the standard instance.
example {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] (J : Ideal S) :
    Module.Finite R (S ⧸ J) := inferInstance

-- A trivial algebra admits the empty product, without any locality assumption.
example {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Subsingleton S] :
    ∃ (n : ℕ) (J : Fin n → Ideal S),
      (∀ i, IsLocalRing (S ⧸ J i)) ∧
        Nonempty (S ≃ₐ[R] ∀ i, S ⧸ J i) := by
  refine ⟨0, Fin.elim0, ?_, ⟨default⟩⟩
  intro i
  exact Fin.elim0 i

namespace TwoAdicProduct

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private abbrev R := PadicInt 2
private abbrev S := R × R

example : CommRing R := inferInstance
example : IsLocalRing R := inferInstance
example : IsAdicComplete (IsLocalRing.maximalIdeal R) R := inferInstance

example : HenselianRing R (IsLocalRing.maximalIdeal R) :=
  IsAdicComplete.henselianRing R (IsLocalRing.maximalIdeal R)

example : CommRing S := inferInstance
example : Algebra R S := inferInstance

-- The stock product algebra has the diagonal structural map.
example (r : R) : algebraMap R S r = (r, r) := rfl

example : Module.Finite R R := Module.Finite.self R
example : Module.Finite R S := Module.Finite.prod

private theorem left_ne_zero : ((1, 0) : S) ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg Prod.fst h)

example : Nontrivial S := nontrivial_of_ne _ _ left_ne_zero

private theorem left_not_isUnit : ¬ IsUnit ((1, 0) : S) := by
  intro h
  exact not_isUnit_zero (Prod.isUnit_iff.mp h).2

private theorem right_not_isUnit : ¬ IsUnit ((0, 1) : S) := by
  intro h
  exact not_isUnit_zero (Prod.isUnit_iff.mp h).1

private theorem left_add_right : ((1, 0) : S) + (0, 1) = 1 := by
  ext <;> simp

private theorem not_isLocalRing : ¬ IsLocalRing S := by
  intro h
  have : IsLocalRing S := h
  have hunit : IsUnit (((1, 0) : S) + (0, 1)) := by
    rw [left_add_right]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hunit with hleft | hright
  · exact left_not_isUnit hleft
  · exact right_not_isUnit hright

example :
    ∃ (n : ℕ) (J : Fin n → Ideal S),
      (∀ i, IsLocalRing (S ⧸ J i)) ∧
        Nonempty (S ≃ₐ[R] ∀ i, S ⧸ J i) :=
  HenselianRing.exists_algEquiv_pi_quotient R S

end TwoAdicProduct
