/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.MvPolynomial.Jacobian
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Polynomial evaluation on scaled Jacobson-ideal neighborhoods

If `I` lies in the Jacobson radical and `b - a ∈ (g(a)) I`, then `g(b)` and `g(a)`
are associated in the coefficient ring. Applying this to `g = f.derivative` gives
stability of the derivative up to a unit without requiring that derivative to be a unit.

The condition on `I` makes elements of `1 + I` units. Together with polynomial evaluation
congruence, this avoids cancelling `g(a)` and includes zero values, zero divisors and the
zero ring. No Henselian or completeness hypothesis is involved.

For semiring coefficients evaluated in a commutative ring through a coefficient map,
a regular derivative `d` at an arbitrary target point gives injectivity on the
scaled neighborhood modulo `(d)I`. This specializes the multivariate Jacobian
criterion via Mathlib's equivalence for polynomials in a unique variable.

## References

The derivative application is motivated by the small-error Hensel argument in
I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition
(2002), II, §1, Corollary 3. This module concerns only association of polynomial values,
not root existence or that whole corollary.

The formulation uses Mathlib's `Polynomial.sub_dvd_eval_sub` (Chris Hughes, Johannes Hölzl,
Kim Morrison and Jens Wagemaker's polynomial division API) and the Jacobson radical API
of Kenny Lau, Devon Tuma and Wojciech Nawrocki.
-/

@[expose] public section

universe u v w

namespace MvPolynomial

/-- The one-variable equivalence transports the polynomial derivative to the partial
derivative in the unique variable. -/
theorem pderiv_uniqueAlgEquiv_symm
    {C : Type u} [CommSemiring C] {σ : Type w} [Unique σ]
    (P : Polynomial C) (i : σ) :
    pderiv i ((uniqueAlgEquiv C σ).symm P) =
      (uniqueAlgEquiv C σ).symm P.derivative := by
  classical
  ext d
  simp only [coeff_pderiv, coeff_uniqueAlgEquiv_symm, Polynomial.coeff_derivative,
    Finsupp.add_apply, Unique.eq_default i, Finsupp.single_eq_same]

end MvPolynomial

namespace Polynomial

/-- Evaluation through a coefficient map is injective on the `(d)I` neighborhood of
an arbitrary target point, where `d` is the evaluated derivative, provided `d` is a
non-zero-divisor and `I` lies in the target Jacobson radical. No root at the center
or invertibility of the derivative is required. -/
theorem injOn_eval₂_of_mem_nonZeroDivisors_derivative
    {C : Type u} {R : Type v} [CommSemiring C] [CommRing R]
    (φ : C →+* R) (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (P : Polynomial C) (a : R)
    (hd : P.derivative.eval₂ φ a ∈ nonZeroDivisors R) :
    Set.InjOn (P.eval₂ φ)
      {b : R | b - a ∈ Ideal.span {P.derivative.eval₂ φ a} * I} := by
  let Q := (MvPolynomial.uniqueAlgEquiv C Unit).symm P
  let J : Matrix Unit Unit R := Matrix.of fun _ j =>
    MvPolynomial.eval₂ φ (fun _ => a) (MvPolynomial.pderiv j Q)
  have hdet : Matrix.det J = P.derivative.eval₂ φ a := by
    rw [Matrix.det_unique]
    change MvPolynomial.eval₂ φ (fun _ => a) (MvPolynomial.pderiv () Q) = _
    dsimp only [Q]
    rw [MvPolynomial.pderiv_uniqueAlgEquiv_symm,
      MvPolynomial.eval₂_const_uniqueAlgEquiv_symm]
  have hinj := MvPolynomial.injOn_eval₂_of_mem_nonZeroDivisors_det_jacobian
    φ I hI (fun _ : Unit => Q) (fun _ => a)
    (by change Matrix.det J ∈ nonZeroDivisors R; rwa [hdet])
  intro b hb c hc hbc
  have hpoints : (fun _ : Unit => b) = (fun _ : Unit => c) := by
    apply hinj
    · intro i
      change b - a ∈ Ideal.span {Matrix.det J} * I
      simpa only [Set.mem_ofPred_eq, hdet] using hb
    · intro i
      change c - a ∈ Ideal.span {Matrix.det J} * I
      simpa only [Set.mem_ofPred_eq, hdet] using hc
    · funext i
      simpa only [Q, MvPolynomial.eval₂_const_uniqueAlgEquiv_symm] using hbc
  exact congrFun hpoints ()

variable {R : Type u} [CommRing R]

/-- Polynomial values at `a` and `b` are associated when `b - a` belongs to
`Ideal.span {g.eval a} * I` and `I` lies in the Jacobson radical of the coefficient ring.

In particular, use `g = f.derivative` to compare derivative values. The association is
in `R` itself, not in a fraction field, and permits `g.eval a = 0`. The Jacobson condition
ensures that the multiplicative correction is a unit; no cancellation is required. -/
theorem associated_eval_of_sub_mem_span_mul (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) (g : R[X]) (a b : R)
    (hab : b - a ∈ Ideal.span {g.eval a} * I) :
    Associated (g.eval b) (g.eval a) := by
  obtain ⟨i, hi, hiab⟩ := Ideal.mem_span_singleton_mul.mp hab
  obtain ⟨q, hq⟩ := sub_dvd_eval_sub b a g
  have hmul : g.eval b = g.eval a * (1 + i * q) := by
    calc
      g.eval b = (g.eval b - g.eval a) + g.eval a := by ring
      _ = (b - a) * q + g.eval a := by rw [hq]
      _ = (g.eval a * i) * q + g.eval a := by rw [← hiab]
      _ = g.eval a * (1 + i * q) := by ring
  have hu : IsUnit (1 + i * q) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    simpa only [add_sub_cancel_left] using hI (I.mul_mem_right q hi)
  rw [hmul]
  exact associated_mul_unit_left _ _ hu

end Polynomial
