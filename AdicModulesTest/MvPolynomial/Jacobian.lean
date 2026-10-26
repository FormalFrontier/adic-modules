/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.MvPolynomial.Jacobian
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.FinCases

/-!
# A coupled polynomial map over the 2-adic integers

The map `(x, y) ↦ (x + y² + 2, y + x² + 2)` has identity Jacobian at zero.
The ideal containment and Jacobian calculation below are independent of the
injectivity theorem. The injectivity conclusion follows from Jacobson-ideal injectivity.
-/

@[expose] public section

open MvPolynomial

example :
    Set.InjOn
      (fun x : Fin 2 → PadicInt 2 => fun i =>
        MvPolynomial.eval x (![X 0 + X 1 ^ 2 + C 2, X 1 + X 0 ^ 2 + C 2] i))
      {x | ∀ i, x i - (0 : PadicInt 2) ∈ IsLocalRing.maximalIdeal (PadicInt 2)} := by
  let P : Fin 2 → MvPolynomial (Fin 2) (PadicInt 2) :=
    ![X 0 + X 1 ^ 2 + C 2, X 1 + X 0 ^ 2 + C 2]
  have hI : IsLocalRing.maximalIdeal (PadicInt 2) ≤
      Ideal.jacobson (⊥ : Ideal (PadicInt 2)) :=
    IsLocalRing.maximalIdeal_le_jacobson ⊥
  have hJacId :
      (fun i j => MvPolynomial.eval (fun _ => (0 : PadicInt 2))
        (MvPolynomial.pderiv j (P i))) =
        (1 : Matrix (Fin 2) (Fin 2) (PadicInt 2)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P]
  have hdet : IsUnit (Matrix.det
      (fun i j => MvPolynomial.eval (fun _ => (0 : PadicInt 2))
        (MvPolynomial.pderiv j (P i)))) := by
    rw [hJacId, Matrix.det_one]
    exact isUnit_one
  simpa only [P] using
    (MvPolynomial.injOn_eval_of_isUnit_det_jacobian
      (IsLocalRing.maximalIdeal (PadicInt 2)) hI P (fun _ => 0) hdet)
