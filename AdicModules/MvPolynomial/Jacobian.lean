/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Polynomial injectivity on a scaled Jacobson-ideal neighborhood

For polynomials with coefficients in a commutative semiring, evaluated through a
coefficient map into a commutative ring, a regular evaluated Jacobian determinant
`d` at a point gives injectivity on its coordinatewise neighborhood modulo `(d)I`,
where `I` is contained in the target Jacobson radical. When `d` is a unit this is
the full neighborhood modulo `I`.

The proof reuses a two-point polynomial expansion over the target ring. Its
coefficient matrix is congruent to the evaluated Jacobian modulo `(d)I`, so its
determinant is `d` times a unit. Adjugate multiplication and regularity then give
injectivity. No root at the center or root-existence hypothesis is needed.
-/

@[expose] public section

namespace MvPolynomial

open scoped BigOperators

universe u v w

private theorem exists_eval_sub_eq_sum
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
    (I : Ideal R) (a b c : ι → R)
    (hb : ∀ i, b i - a i ∈ I) (hc : ∀ i, c i - a i ∈ I)
    (p : MvPolynomial ι R) :
    ∃ d : ι → R, eval b p - eval c p = ∑ j, d j * (b j - c j) ∧
      ∀ j, d j - eval a (pderiv j p) ∈ I := by
  classical
  have hca (q : MvPolynomial ι R) : eval c q - eval a q ∈ I := by
    apply Ideal.Quotient.eq.mp
    simpa only [map_eval, Function.comp_def] using
      congrArg (fun x : ι → R ⧸ I => eval x (map (Ideal.Quotient.mk I) q))
        (funext fun i => Ideal.Quotient.eq.mpr (hc i))
  induction p using MvPolynomial.induction_on with
  | C r =>
    refine ⟨0, ?_, ?_⟩
    · simp
    · intro j
      simp
  | add p q hp hq =>
    obtain ⟨d, hd, hdj⟩ := hp
    obtain ⟨e, he, hej⟩ := hq
    refine ⟨fun j => d j + e j, ?_, ?_⟩
    · calc
        eval b (p + q) - eval c (p + q) =
            (eval b p - eval c p) + (eval b q - eval c q) := by
          simp only [map_add]
          ring
        _ = (∑ j, d j * (b j - c j)) + ∑ j, e j * (b j - c j) := by rw [hd, he]
        _ = ∑ j, (d j + e j) * (b j - c j) := by
          simp only [add_mul, Finset.sum_add_distrib]
    · intro j
      (convert I.add_mem (hdj j) (hej j) using 1; simp only [map_add]; ring)
  | mul_X p i hp =>
    obtain ⟨d, hd, hdj⟩ := hp
    refine ⟨fun j => b i * d j + if j = i then eval c p else 0, ?_, ?_⟩
    · calc
        eval b (p * X i) - eval c (p * X i) =
            b i * (eval b p - eval c p) + eval c p * (b i - c i) := by
          simp only [map_mul, eval_X]
          ring
        _ = b i * (∑ j, d j * (b j - c j)) + eval c p * (b i - c i) := by rw [hd]
        _ = ∑ j, (b i * d j + if j = i then eval c p else 0) * (b j - c j) := by
          simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    · intro j
      by_cases hji : j = i
      · subst j
        (convert I.add_mem
          (I.add_mem (I.mul_mem_right (d i) (hb i)) (I.mul_mem_left (a i) (hdj i)))
          (hca p) using 1; simp; ring)
      · (convert I.add_mem (I.mul_mem_right (d j) (hb i))
          (I.mul_mem_left (a i) (hdj j)) using 1;
          simp [hji, Ne.symm hji]; ring)

/-- A square polynomial system, evaluated through a coefficient map into `R`, is
injective on the coordinatewise `(d)I` neighborhood of `a` if its evaluated
Jacobian determinant `d` is a non-zero-divisor in `R` and `I` lies in the Jacobson
radical. For unit `d`, this is the whole `I` neighborhood. No assumption on the
value at `a`, or on root existence, is needed. -/
theorem injOn_eval₂_of_mem_nonZeroDivisors_det_jacobian
    {C : Type u} {R : Type v} [CommSemiring C] [CommRing R]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (φ : C →+* R) (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (P : ι → MvPolynomial ι C) (a : ι → R)
    (hj : Matrix.det (fun i j => eval₂ φ a (pderiv j (P i))) ∈ nonZeroDivisors R) :
    Set.InjOn (fun x : ι → R => fun i => eval₂ φ x (P i))
      {x | ∀ i, x i - a i ∈
        Ideal.span {Matrix.det (fun i j => eval₂ φ a (pderiv j (P i)))} * I} := by
  classical
  let J : Matrix ι ι R := fun i j => eval₂ φ a (pderiv j (P i))
  let d := Matrix.det J
  let K : Ideal R := Ideal.span {d} * I
  intro b hb c hc hbc
  have hex (i : ι) : ∃ e : ι → R,
      eval₂ φ b (P i) - eval₂ φ c (P i) = ∑ j, e j * (b j - c j) ∧
        ∀ j, e j - J i j ∈ K := by
    simpa only [pderiv_map, eval_map] using
      exists_eval_sub_eq_sum K a b c hb hc (map φ (P i))
  choose e hE hEJ using hex
  let A : Matrix ι ι R := Matrix.of e
  let q := Ideal.Quotient.mk K
  have hmap : q.mapMatrix A = q.mapMatrix J := by
    apply Matrix.ext
    intro i j
    exact Ideal.Quotient.eq.mpr (hEJ i j)
  have hdet : Matrix.det A - d ∈ K := by
    apply Ideal.Quotient.eq.mp
    rw [q.map_det, hmap, ← q.map_det]
  obtain ⟨r, hr, hdr⟩ := Ideal.mem_span_singleton_mul.mp hdet
  have hfactor : Matrix.det A = d * (1 + r) := by
    calc
      Matrix.det A = d + d * r := by rw [hdr]; ring
      _ = d * (1 + r) := by ring
  have hunit : IsUnit (1 + r) :=
    Ideal.isUnit_of_sub_one_mem_jacobson_bot (1 + r) (by simpa using hI hr)
  have hregular : Matrix.det A ∈ nonZeroDivisors R := by
    rw [hfactor]
    exact mul_mem hj hunit.mem_nonZeroDivisors
  have hz : Matrix.mulVec A (b - c) = 0 := by
    funext i
    change (∑ j, e i j * (b j - c j)) = 0
    rw [← hE i]
    exact sub_eq_zero.mpr (congrFun hbc i)
  exact sub_eq_zero.mp
    (Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hregular hz)

/-- A square polynomial map with unit Jacobian determinant at `a` is injective on
the congruence class of `a` modulo a Jacobson ideal `I`.
No assumption on the value of the polynomial map at `a` is needed. -/
theorem injOn_eval_of_isUnit_det_jacobian
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (P : ι → MvPolynomial ι R) (a : ι → R)
    (hj : IsUnit (Matrix.det (fun i j => eval a (pderiv j (P i))))) :
    Set.InjOn (fun x : ι → R => fun i => eval x (P i))
      {x | ∀ i, x i - a i ∈ I} := by
  have hspan : Ideal.span {Matrix.det (fun i j => eval a (pderiv j (P i)))} * I = I := by
    rw [Ideal.span_singleton_eq_top.mpr hj, Ideal.top_mul]
  simpa only [eval₂_id, hspan] using
    injOn_eval₂_of_mem_nonZeroDivisors_det_jacobian (RingHom.id R) I hI P a
      hj.mem_nonZeroDivisors

end MvPolynomial
