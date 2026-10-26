/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianLocality
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integral closure over the 2-adic integers

The integral closure of `PadicInt 2` in an algebraic closure of `Padic 2` is
integral over `PadicInt 2` and is a domain.
The domain and integrality inputs come from stock subalgebra and integral-closure
instances. Its locality follows by applying the locality theorem to the canonical
algebra map. The Henselian base structure comes from maximal-ideal completeness.
-/

example :
    IsLocalRing (integralClosure (PadicInt 2) (AlgebraicClosure (Padic 2))) := by
  let : HenselianRing (PadicInt 2) (IsLocalRing.maximalIdeal (PadicInt 2)) :=
    IsAdicComplete.henselianRing _ _
  let : HenselianLocalRing (PadicInt 2) :=
    HenselianRing.toHenselianLocalRing (PadicInt 2)
  exact HenselianLocalRing.isLocalRing_of_isIntegral
    (algebraMap (PadicInt 2)
      (integralClosure (PadicInt 2) (AlgebraicClosure (Padic 2))))
    (algebraMap_isIntegral_iff.mpr inferInstance)

-- The element (0, 1) is nonzero and square-zero, so this extension is not a domain.
example :
    ((IsLocalRing.maximalIdeal (PadicInt 2)).map
      (TrivSqZeroExt.inlHom (PadicInt 2) (PadicInt 2))).radical =
        Ideal.jacobson (⊥ : Ideal (TrivSqZeroExt (PadicInt 2) (PadicInt 2))) ∧
      HenselianLocalRing (TrivSqZeroExt (PadicInt 2) (PadicInt 2)) := by
  let : HenselianRing (PadicInt 2) (IsLocalRing.maximalIdeal (PadicInt 2)) :=
    IsAdicComplete.henselianRing _ _
  let : HenselianLocalRing (PadicInt 2) :=
    HenselianRing.toHenselianLocalRing (PadicInt 2)
  let : IsLocalRing (TrivSqZeroExt (PadicInt 2) (PadicInt 2)) :=
    IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst with h | h
      · exact Or.inl (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr h)
      · exact Or.inr (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (by simpa using h))
  have hf : (TrivSqZeroExt.inlHom (PadicInt 2) (PadicInt 2)).IsIntegral := by
    intro x
    refine ⟨(Polynomial.X - Polynomial.C x.fst) ^ 2,
      (Polynomial.monic_X_sub_C x.fst).pow 2, ?_⟩
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    have hx : x - (TrivSqZeroExt.inlHom (PadicInt 2) (PadicInt 2)) x.fst =
        TrivSqZeroExt.inr x.snd := by
      ext <;> simp
    rw [hx, pow_two, TrivSqZeroExt.inr_mul_inr]
  exact ⟨Ideal.radical_map_maximalIdeal_eq_jacobson_bot _ hf,
    HenselianLocalRing.of_isIntegral _ hf⟩

-- The quotient by the top ideal tests the zero-target boundary.
example {R : Type*} [CommRing R] [IsLocalRing R] :
    ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (⊤ : Ideal R))).radical =
      Ideal.jacobson (⊥ : Ideal (R ⧸ (⊤ : Ideal R))) := by
  have hf : (Ideal.Quotient.mk (⊤ : Ideal R)).IsIntegral := by
    intro x
    refine ⟨Polynomial.X, Polynomial.monic_X, ?_⟩
    rw [Polynomial.eval₂_X]
    exact Subsingleton.elim _ _
  exact Ideal.radical_map_maximalIdeal_eq_jacobson_bot _ hf
