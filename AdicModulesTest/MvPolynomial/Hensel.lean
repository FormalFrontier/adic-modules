/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.MvPolynomial.Hensel
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.FinCases

/-!
# A coupled polynomial system over the 2-adic integers

At the origin, both `X₀ + X₁² + 2` and `X₁ + X₀² + 2` lie in the
maximal ideal, and their Jacobian is the identity. Adic completeness supplies
Mathlib's scalar Henselian instance independently of the system statement.

Both equations involve both coordinates; neither is a separate scalar equation.
-/

open MvPolynomial

example :
    ∃! b : Fin 2 → PadicInt 2,
      (∀ i, MvPolynomial.eval b
        (![X 0 + X 1 ^ 2 + C 2, X 1 + X 0 ^ 2 + C 2] i) = 0) ∧
        ∀ i, b i ∈ IsLocalRing.maximalIdeal (PadicInt 2) := by
  let P : Fin 2 → MvPolynomial (Fin 2) (PadicInt 2) :=
    ![X 0 + X 1 ^ 2 + C 2, X 1 + X 0 ^ 2 + C 2]
  let : HenselianRing (PadicInt 2) (IsLocalRing.maximalIdeal (PadicInt 2)) :=
    IsAdicComplete.henselianRing _ _
  have htwo : (2 : PadicInt 2) ∈ IsLocalRing.maximalIdeal (PadicInt 2) := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (Set.mem_singleton (2 : PadicInt 2))
  have hzero : ∀ i, MvPolynomial.eval (fun _ => (0 : PadicInt 2)) (P i) ∈
      IsLocalRing.maximalIdeal (PadicInt 2) := by
    intro i
    fin_cases i <;> simpa [P] using htwo
  have hjac :
      (fun i j => MvPolynomial.eval (fun _ => (0 : PadicInt 2))
        (MvPolynomial.pderiv j (P i))) =
        (1 : Matrix (Fin 2) (Fin 2) (PadicInt 2)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P]
  have hdet : IsUnit (Matrix.det
      (fun i j => MvPolynomial.eval (fun _ => (0 : PadicInt 2))
        (MvPolynomial.pderiv j (P i)))) := by
    rw [hjac, Matrix.det_one]
    exact isUnit_one
  simpa only [sub_zero] using
    (HenselianRing.existsUnique_root_of_isUnit_det_jacobian
      (I := IsLocalRing.maximalIdeal (PadicInt 2)) P (fun _ => 0) hzero hdet)
