/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Polynomial.Hensel
import Mathlib.Data.ZMod.Defs
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Uniqueness of factors under coefficient maps

The constant-coefficient map from power series over the integers to the integers reflects
units, although neither coefficient ring is local and the map is not injective. The right
factor `C (PowerSeries.X) * X ^ 2 + X - 1` is not monic, and its image is coprime to `X`.
The power-series uniqueness conclusion applies `Monic.eq_factors_of_isCoprime_map`.
The zero ring is a boundary case with no nontriviality hypothesis.
-/

namespace Polynomial

private theorem eq_factors_powerSeries_int
    (g h : (PowerSeries ℤ)[X]) (hg : g.Monic)
    (hprod : g * h = X * (C (PowerSeries.X : PowerSeries ℤ) * X ^ 2 + X - 1))
    (hmap : g.map (PowerSeries.constantCoeff (R := ℤ)) = X) :
    g = X ∧ h = C (PowerSeries.X : PowerSeries ℤ) * X ^ 2 + X - 1 := by
  have : IsLocalHom (PowerSeries.constantCoeff (R := ℤ)) :=
    ⟨fun _ hu => PowerSeries.isUnit_iff_constantCoeff.mpr hu⟩
  have hhmap : h.map (PowerSeries.constantCoeff (R := ℤ)) = X - 1 := by
    apply (monic_X : (X : ℤ[X]).Monic).isRegular.left
    simpa only [Polynomial.map_mul, hmap, map_X, Polynomial.map_sub,
      Polynomial.map_add, map_C, Polynomial.map_pow, PowerSeries.constantCoeff_X,
      C_0, zero_mul, zero_add, Polynomial.map_one] using
      congrArg (fun p : (PowerSeries ℤ)[X] =>
        p.map (PowerSeries.constantCoeff (R := ℤ))) hprod
  have hcoprime : IsCoprime (g.map (PowerSeries.constantCoeff (R := ℤ)))
      (h.map (PowerSeries.constantCoeff (R := ℤ))) := by
    rw [hmap, hhmap]
    refine ⟨1, -1, ?_⟩
    simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using
      (sub_sub_cancel (X : ℤ[X]) 1)
  exact Monic.eq_factors_of_isCoprime_map (PowerSeries.constantCoeff (R := ℤ))
    hg monic_X hprod (by simpa only [map_X] using hmap) hcoprime

private theorem eq_factors_zmod_one (g h : (ZMod 1)[X]) :
    g = X ∧ h = X - 1 := by
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end Polynomial

namespace Polynomial

/-- Projection from a product ring admits distinct monic factor lifts with the same coprime
images, so unit reflection cannot be omitted from factor uniqueness. -/
private theorem not_eq_factors_prod_fst :
    (X : (ℤ × ℤ)[X]).Monic ∧
      (X - C (0, 1) : (ℤ × ℤ)[X]).Monic ∧
      (X : (ℤ × ℤ)[X]) * (X - 1) =
        (X - C (0, 1)) * (X - C (1, 0)) ∧
      (X : (ℤ × ℤ)[X]).map (RingHom.fst ℤ ℤ) =
        (X - C (0, 1) : (ℤ × ℤ)[X]).map (RingHom.fst ℤ ℤ) ∧
      IsCoprime ((X : (ℤ × ℤ)[X]).map (RingHom.fst ℤ ℤ))
        ((X - 1 : (ℤ × ℤ)[X]).map (RingHom.fst ℤ ℤ)) ∧
      (X : (ℤ × ℤ)[X]) ≠ X - C (0, 1) := by
  refine ⟨monic_X, monic_X_sub_C _, ?_, ?_, ?_, ?_⟩
  · have hadd : C ((1, 0) : ℤ × ℤ) + C (0, 1) = (1 : (ℤ × ℤ)[X]) := by
      rw [← C_add]
      change C (1 : ℤ × ℤ) = 1
      exact C_1
    have hmul : C ((0, 1) : ℤ × ℤ) * C (1, 0) = (0 : (ℤ × ℤ)[X]) := by
      rw [← C_mul]
      change C (0 : ℤ × ℤ) = 0
      exact C_0
    calc
      (X : (ℤ × ℤ)[X]) * (X - 1) = X * X - X := by rw [mul_sub, mul_one]
      _ = X * X - X * (C ((1, 0) : ℤ × ℤ) + C (0, 1)) := by rw [hadd, mul_one]
      _ = (X - C (0, 1)) * (X - C (1, 0)) := by
        rw [sub_mul, mul_sub, mul_sub, hmul, sub_zero, mul_add,
          sub_add_eq_sub_sub, mul_comm (C ((0, 1) : ℤ × ℤ)) X]
  · simp only [map_X, Polynomial.map_sub, map_C, RingHom.coe_fst, C_0, sub_zero]
  · simp only [map_X, Polynomial.map_sub, Polynomial.map_one]
    refine ⟨1, -1, ?_⟩
    simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using
      (sub_sub_cancel (X : ℤ[X]) 1)
  · intro heq
    have hcoeff := congrArg (fun p : (ℤ × ℤ)[X] => (p.coeff 0).2) heq
    simp at hcoeff

end Polynomial
