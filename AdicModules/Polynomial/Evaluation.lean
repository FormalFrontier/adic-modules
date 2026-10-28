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
two points in the same `(d)I` neighborhood of an arbitrary target point have value
difference associated to `d` times their difference, where `d` is the derivative at
the center. The coefficient semiring need not be commutative. If `d` is regular,
this gives injectivity on that neighborhood.

## References

The derivative application is motivated by the small-error Hensel argument in
I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition
(2002), II, §1, Corollary 3. This module concerns association of polynomial values
and differences, and injectivity, not root existence or that whole corollary.

The formulation uses Mathlib's `Polynomial.sub_dvd_eval_sub` and
`Polynomial.X_sub_C_dvd_sub_C_eval` (Chris Hughes, Johannes Hölzl,
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

section

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

end

/-- On the same `(d)I` neighborhood of a target point `a`, the difference of two
polynomial values is associated to the linearized difference `d * (b - c)`, where
`d = P.derivative.eval₂ φ a` and `I` lies in the target Jacobson radical.

The coefficient semiring may be noncommutative, and the target points need not lie
in the coefficient map's image. No root condition or regularity of `d` is required. -/
theorem associated_eval₂_sub_eval₂_of_sub_mem_span_derivative_mul
    {C : Type u} {R : Type v} [Semiring C] [CommRing R]
    (φ : C →+* R) (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (P : Polynomial C) (a b c : R)
    (hb : b - a ∈ Ideal.span {P.derivative.eval₂ φ a} * I)
    (hc : c - a ∈ Ideal.span {P.derivative.eval₂ φ a} * I) :
    Associated (P.eval₂ φ b - P.eval₂ φ c) (P.derivative.eval₂ φ a * (b - c)) := by
  let Q : R[X] := P.map φ
  have hderiv (x : R) : Q.derivative.eval x = P.derivative.eval₂ φ x := by
    simp only [Q, derivative_map, eval_map]
  have hα := associated_eval_of_sub_mem_span_mul I hI Q.derivative a c
    (by simpa only [hderiv] using hc)
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (p := Q) (a := c)
  have heval : Q.eval b - Q.eval c = (b - c) * q.eval b := by
    simpa only [eval_sub, eval_C, eval_mul, eval_X] using congrArg (eval b) hq
  have hqc : Q.derivative.eval c = q.eval c := by
    have h := congrArg (fun f : R[X] => f.derivative.eval c) hq
    simpa only [derivative_sub, derivative_C, derivative_X, sub_zero, derivative_mul,
      eval_add, eval_mul, eval_one, one_mul, eval_sub,
      eval_X, eval_C, sub_self, zero_mul, add_zero] using h
  obtain ⟨rb, hrb, hb_eq⟩ := Ideal.mem_span_singleton_mul.mp hb
  obtain ⟨rc, hrc, hc_eq⟩ := Ideal.mem_span_singleton_mul.mp hc
  obtain ⟨t, ht⟩ := hα.dvd
  have hbox : b - c ∈ Ideal.span {q.eval c} * I := by
    refine Ideal.mem_span_singleton_mul.mpr
      ⟨t * (rb - rc), I.mul_mem_left t (I.sub_mem hrb hrc), ?_⟩
    rw [← hqc, ← mul_assoc, ← ht, hderiv, mul_sub, hb_eq, hc_eq]
    ring
  have hassoc : Associated (q.eval b) (Q.derivative.eval a) := by
    have hqassoc := associated_eval_of_sub_mem_span_mul I hI q c b hbox
    rw [← hqc] at hqassoc
    exact hqassoc.trans hα
  have hmul := Associated.mul_left (b - c) hassoc
  rw [← heval, hderiv] at hmul
  simpa only [Q, eval_map, mul_comm] using hmul

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
  intro b hb c hc hbc
  have hassoc := associated_eval₂_sub_eval₂_of_sub_mem_span_derivative_mul
    φ I hI P a b c hb hc
  have hz : P.derivative.eval₂ φ a * (b - c) = 0 :=
    hassoc.eq_zero_iff.mp (sub_eq_zero.mpr hbc)
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hd).1 _ hz)

/-- On a derivative-scaled Jacobson neighborhood with regular derivative `d`, congruence
of polynomial values modulo `(d)J` is equivalent to congruence of the points modulo `J`.

Here `d = P.derivative.eval₂ φ a`, and `J` is arbitrary: no containment in the
neighborhood ideal `I` is required. -/
theorem eval₂_sub_eval₂_mem_span_derivative_mul_iff
    {C : Type u} {R : Type v} [Semiring C] [CommRing R]
    (φ : C →+* R) (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (P : Polynomial C) (a b c : R)
    (hb : b - a ∈ Ideal.span {P.derivative.eval₂ φ a} * I)
    (hc : c - a ∈ Ideal.span {P.derivative.eval₂ φ a} * I)
    (hd : P.derivative.eval₂ φ a ∈ nonZeroDivisors R)
    (J : Ideal R) :
    P.eval₂ φ b - P.eval₂ φ c ∈
        Ideal.span {P.derivative.eval₂ φ a} * J ↔
      b - c ∈ J := by
  rw [Ideal.mem_iff_of_associated
    (associated_eval₂_sub_eval₂_of_sub_mem_span_derivative_mul φ I hI P a b c hb hc),
    Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨z, hz, hdz⟩
    exact (mul_cancel_left_mem_nonZeroDivisors hd).mp hdz ▸ hz
  · intro hbc
    exact ⟨b - c, hbc, rfl⟩

end Polynomial
