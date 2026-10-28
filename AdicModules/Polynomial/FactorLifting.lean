/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.MvPolynomial.HenselDeterminant
public import MultivariatePolynomials.CoefficientProductSylvester

/-!
# Polynomial factor lifting controlled by a resultant

For a Henselian pair `(R, I)`, let `A`, `B`, and `F` have nominal degree bounds
`m`, `n`, and `m + n`, with `F.coeff (m + n) = A.coeff m * B.coeff n`.
If the coefficient error of `F - A * B` lies in `(r²)I`, it lifts to a factorization
with coefficient corrections in `(r)I`, where `r` is the resultant at those bounds.
The factors retain the seed coefficients at the bounds; they need not be monic.

The coefficient equations have the bounded Sylvester matrix as their Jacobian
at the seed factors. Determinant-controlled lifting solves these equations, and
the coefficient at the sum of the bounds determines the remaining term.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

open scoped BigOperators

universe u v

namespace Polynomial

/-- A polynomial bounded by the sum of the factor bounds equals their product
if its lower coefficients agree and its coefficient at the sum is the ordered
product of the two bounding coefficients. -/
private theorem eq_mul_of_coeff_eq_below_add
    {R : Type u} [Semiring R] (m n : ℕ) (F G H : Polynomial R)
    (hF : F.natDegree ≤ m + n) (hG : G.natDegree ≤ m) (hH : H.natDegree ≤ n)
    (hlow : ∀ k : ℕ, k < m + n → F.coeff k = (G * H).coeff k)
    (htop : F.coeff (m + n) = G.coeff m * H.coeff n) :
    F = G * H := by
  have hGH : (G * H).natDegree ≤ m + n :=
    (Polynomial.natDegree_mul_le : (G * H).natDegree ≤ G.natDegree + H.natDegree).trans
      (Nat.add_le_add hG hH)
  apply Polynomial.ext
  intro k
  rcases lt_trichotomy k (m + n) with hk | hk | hk
  · exact hlow k hk
  · subst k
    exact htop.trans (Polynomial.coeff_mul_add_eq_of_natDegree_le hG hH).symm
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hF hk),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hGH hk)]

end Polynomial

namespace HenselianRing

private theorem det_coefficientProduct_zero_eq_resultant
    {R : Type u} [CommRing R] (m n : ℕ) (A B : Polynomial R)
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ n) :
    Matrix.det (fun i j : Fin (m + n) =>
      MvPolynomial.eval₂Hom (RingHom.id R) (0 : Fin (m + n) → R)
        (MvPolynomial.pderiv j (MvPolynomial.coefficientProduct m n A B i))) =
      Polynomial.resultant A B m n := by
  have hSylvester :=
    MvPolynomial.eval₂Hom_pderiv_coefficientProduct_eq_sylvester
      m n A B (RingHom.id R) (0 : Fin (m + n) → R)
  -- The lower-degree corrections vanish at the zero coordinate vector.
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hSylvester
  have hG : (A.map (RingHom.id R) + 0).natDegree ≤ m := by
    simpa only [Polynomial.map_id, add_zero] using hA
  have hH : (B.map (RingHom.id R) + 0).natDegree ≤ n := by
    simpa only [Polynomial.map_id, add_zero] using hB
  have hmatrix :
      (fun i j : Fin (m + n) =>
        MvPolynomial.eval₂Hom (RingHom.id R) (0 : Fin (m + n) → R)
          (MvPolynomial.pderiv j (MvPolynomial.coefficientProduct m n A B i))) =
        Polynomial.sylvester A B m n := by
    simpa only [Polynomial.map_id, Prod.fst_zero, Prod.snd_zero, Submodule.coe_zero,
      add_zero] using hSylvester hG hH
  have hresultant :
      Polynomial.resultant A B m n =
        Matrix.det (Polynomial.sylvester A B m n) := rfl
  exact (congrArg Matrix.det hmatrix).trans hresultant.symm

end HenselianRing

namespace HenselianRing

private theorem monomial_sum_coeff_eq_zero_of_le
    {R : Type u} [Semiring R] (d : ℕ) (c : Fin d → R)
    (k : ℕ) (hk : d ≤ k) :
    (∑ i : Fin d, Polynomial.monomial i.val (c i)).coeff k = 0 := by
  classical
  have hmono (i : Fin d) :
      (Polynomial.monomial i.val (c i)).coeff k = 0 := by
    have hik : i.val ≠ k := ne_of_lt (lt_of_lt_of_le i.isLt hk)
    simp [Polynomial.coeff_monomial, hik]
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_eq_zero (fun i _ => hmono i)

private theorem monomial_sum_coeff_mem
    {R : Type u} [Semiring R] (d : ℕ) (J : Ideal R)
    (c : Fin d → R) (hc : ∀ i, c i ∈ J) (k : ℕ) :
    (∑ i : Fin d, Polynomial.monomial i.val (c i)).coeff k ∈ J := by
  classical
  have hmono (i : Fin d) :
      (Polynomial.monomial i.val (c i)).coeff k ∈ J := by
    by_cases hik : i.val = k
    · simp [hik, hc]
    · simp [Polynomial.coeff_monomial, hik]
  rw [Polynomial.finsetSum_coeff]
  apply J.sum_mem
  intro i hi
  exact hmono i

private theorem map_monomial_sum_eval₂Hom
    {R : Type u} [CommSemiring R] {σ : Type v}
    (d : ℕ) (x : Fin d → σ) (b : σ → R) :
    (∑ i : Fin d, Polynomial.monomial i.val (MvPolynomial.X (x i))).map
        (MvPolynomial.eval₂Hom (RingHom.id R) b) =
      ∑ i : Fin d, Polynomial.monomial i.val (b (x i)) := by
  classical
  have hsum (s : Finset (Fin d)) :
      (∑ i ∈ s, Polynomial.monomial i.val (MvPolynomial.X (x i))).map
          (MvPolynomial.eval₂Hom (RingHom.id R) b) =
        ∑ i ∈ s, Polynomial.monomial i.val (b (x i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp [Finset.sum_insert hi, Polynomial.map_add, ih]
  exact hsum Finset.univ

private theorem coefficientProduct_eval_zero
    {R : Type u} [CommRing R] (m n : ℕ) (A B : Polynomial R)
    (i : Fin (m + n)) :
    MvPolynomial.eval₂Hom (RingHom.id R) (0 : Fin (m + n) → R)
      (MvPolynomial.coefficientProduct m n A B i) = (A * B).coeff i.val := by
  -- The zero coordinate vector gives the seed product.
  simpa only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, Prod.fst_zero,
    Prod.snd_zero, Submodule.coe_zero, Polynomial.map_id, add_zero] using
    (MvPolynomial.eval₂Hom_coefficientProduct m n A B (RingHom.id R)
      (0 : Fin (m + n) → R) i)

private theorem exists_factors_of_coefficientProduct_point
    {R : Type u} [CommRing R] (m n : ℕ) (A B : Polynomial R)
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ n)
    (J : Ideal R) (b : Fin (m + n) → R) (hb : ∀ i, b i ∈ J) :
    ∃ G H : Polynomial R,
      G.natDegree ≤ m ∧ H.natDegree ≤ n ∧
      G.coeff m = A.coeff m ∧ H.coeff n = B.coeff n ∧
      (∀ k : ℕ, (G - A).coeff k ∈ J) ∧
      (∀ k : ℕ, (H - B).coeff k ∈ J) ∧
      ∀ i : Fin (m + n),
        MvPolynomial.eval₂Hom (RingHom.id R) b
          (MvPolynomial.coefficientProduct m n A B i) = (G * H).coeff i.val := by
  classical
  let P : Polynomial R :=
    ∑ i : Fin m, Polynomial.monomial i.val (b (i.castAdd n))
  let Q : Polynomial R :=
    ∑ j : Fin n, Polynomial.monomial j.val (b (j.natAdd m))
  have hPzero (k : ℕ) (hk : m ≤ k) : P.coeff k = 0 :=
    monomial_sum_coeff_eq_zero_of_le m (fun i => b (i.castAdd n)) k hk
  have hQzero (k : ℕ) (hk : n ≤ k) : Q.coeff k = 0 :=
    monomial_sum_coeff_eq_zero_of_le n (fun j => b (j.natAdd m)) k hk
  refine ⟨A + P, B + Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [Polynomial.coeff_add,
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hA hk),
      hPzero k (Nat.le_of_lt hk), zero_add]
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [Polynomial.coeff_add,
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hB hk),
      hQzero k (Nat.le_of_lt hk), zero_add]
  · rw [Polynomial.coeff_add, hPzero m le_rfl, add_zero]
  · rw [Polynomial.coeff_add, hQzero n le_rfl, add_zero]
  · intro k
    simpa only [add_sub_cancel_left] using
      (monomial_sum_coeff_mem m J (fun i => b (i.castAdd n))
        (fun i => hb (i.castAdd n)) k)
  · intro k
    simpa only [add_sub_cancel_left] using
      (monomial_sum_coeff_mem n J (fun j => b (j.natAdd m))
        (fun j => hb (j.natAdd m)) k)
  · intro i
    let e : MvPolynomial (Fin (m + n)) R →+* R :=
      MvPolynomial.eval₂Hom (RingHom.id R) b
    have heC : e.comp MvPolynomial.C = RingHom.id R := by
      ext r
      simp [e]
    have heA : (A.map MvPolynomial.C).map e = A := by
      rw [Polynomial.map_map, heC, Polynomial.map_id]
    have heB : (B.map MvPolynomial.C).map e = B := by
      rw [Polynomial.map_map, heC, Polynomial.map_id]
    have heP :
        (∑ j : Fin m, Polynomial.monomial j.val
          (MvPolynomial.X (j.castAdd n))).map e = P := by
      exact map_monomial_sum_eval₂Hom m (fun j => j.castAdd n) b
    have heQ :
        (∑ j : Fin n, Polynomial.monomial j.val
          (MvPolynomial.X (j.natAdd m))).map e = Q := by
      exact map_monomial_sum_eval₂Hom n (fun j => j.natAdd m) b
    -- Commute coefficient extraction with the coefficient-ring map.
    rw [MvPolynomial.coefficientProduct_apply]
    change e
        (((A.map MvPolynomial.C +
            ∑ j : Fin m, Polynomial.monomial j.val (MvPolynomial.X (j.castAdd n))) *
          (B.map MvPolynomial.C +
            ∑ j : Fin n, Polynomial.monomial j.val (MvPolynomial.X (j.natAdd m)))).coeff
          i.val) =
      ((A + P) * (B + Q)).coeff i.val
    rw [← Polynomial.coeff_map]
    simp only [Polynomial.map_mul, Polynomial.map_add, heA, heB, heP, heQ]

end HenselianRing

namespace HenselianRing

/-- Suppose `A`, `B`, and `F` have nominal degree bounds `m`, `n`, and `m + n`,
and `F.coeff (m + n) = A.coeff m * B.coeff n`. An approximate factorization whose
coefficient error is divisible by the squared nominal resultant times a Henselian
ideal lifts to a factorization. The factors preserve the seed coefficients at
their respective bounds, and their coefficient corrections lie in the resultant
ideal times the same Henselian ideal. -/
theorem exists_eq_mul_of_coeff_sub_mul_mem_span_resultant_sq_mul
    {R : Type u} [CommRing R] {I : Ideal R} [HenselianRing R I]
    (m n : ℕ) (A B F : Polynomial R)
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ n)
    (hF : F.natDegree ≤ m + n)
    (hFtop : F.coeff (m + n) = A.coeff m * B.coeff n) :
    let r : R := Polynomial.resultant A B m n
    (∀ k : ℕ, (F - A * B).coeff k ∈ Ideal.span ({r ^ 2} : Set R) * I) →
      ∃ G H : Polynomial R,
        F = G * H ∧
        G.natDegree ≤ m ∧
        H.natDegree ≤ n ∧
        G.coeff m = A.coeff m ∧
        H.coeff n = B.coeff n ∧
        (∀ k : ℕ, (G - A).coeff k ∈ Ideal.span ({r} : Set R) * I) ∧
        (∀ k : ℕ, (H - B).coeff k ∈ Ideal.span ({r} : Set R) * I) := by
  classical
  dsimp only
  intro hErr
  let r : R := Polynomial.resultant A B m n
  let P : Fin (m + n) → MvPolynomial (Fin (m + n)) R :=
    MvPolynomial.coefficientProduct m n A B
  let d : R := Matrix.det (fun i j : Fin (m + n) =>
    MvPolynomial.eval₂Hom (RingHom.id R) (0 : Fin (m + n) → R)
      (MvPolynomial.pderiv j (P i)))
  have hd : d = r :=
    det_coefficientProduct_zero_eq_resultant m n A B hA hB
  have hresidual : ∀ i : Fin (m + n),
      MvPolynomial.eval₂Hom (RingHom.id R) (0 : Fin (m + n) → R) (P i) -
          F.coeff i.val ∈ Ideal.span ({d ^ 2} : Set R) * I := by
    intro i
    rw [hd]
    change
      MvPolynomial.eval₂Hom (RingHom.id R) (0 : Fin (m + n) → R)
          (MvPolynomial.coefficientProduct m n A B i) - F.coeff i.val ∈
        Ideal.span ({r ^ 2} : Set R) * I
    rw [coefficientProduct_eval_zero m n A B i]
    simpa only [Polynomial.coeff_sub, neg_sub] using
      ((Ideal.span ({r ^ 2} : Set R) * I).neg_mem (hErr i.val))
  have hroot :
      ∃ b : Fin (m + n) → R,
        (∀ i, MvPolynomial.eval₂Hom (RingHom.id R) b (P i) = F.coeff i.val) ∧
        ∀ i, b i - (0 : R) ∈ Ideal.span ({d} : Set R) * I := by
    exact exists_eval₂_eq_of_sub_mem_det_sq_mul
      (C := R) (R := R) (I := I) (ι := Fin (m + n))
      (RingHom.id R) P (0 : Fin (m + n) → R) (fun i => F.coeff i.val)
      hresidual
  obtain ⟨b, hb_eq, hb_mem⟩ := hroot
  have hb_mem' : ∀ i, b i ∈ Ideal.span ({r} : Set R) * I := by
    intro i
    simpa only [hd, sub_zero] using hb_mem i
  obtain ⟨G, H, hG, hH, hGtop, hHtop, hGA, hHB, hcoeff⟩ :=
    exists_factors_of_coefficientProduct_point m n A B hA hB
      (Ideal.span ({r} : Set R) * I) b hb_mem'
  refine ⟨G, H, ?_, hG, hH, hGtop, hHtop, hGA, hHB⟩
  apply Polynomial.eq_mul_of_coeff_eq_below_add m n F G H hF hG hH
  · intro k hk
    exact (hb_eq ⟨k, hk⟩).symm.trans (hcoeff ⟨k, hk⟩)
  · rw [hGtop, hHtop]
    exact hFtop

end HenselianRing
