/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Polynomial.Hensel
import AdicModules.MvPolynomial.Hensel
import AdicModules.RingTheory.HenselianTransport
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.RingTheory.Nakayama

/-!
# Resultant-controlled factorization and uniqueness

A sufficiently small error in a polynomial factorization can be corrected with
strict prescribed degree bounds. For `natDegree g₀ ≤ n` and `natDegree h₀ ≤ m`,
the required error ideal is the square of the fixed-index resultant
`resultant g₀ h₀ n m` times the Henselian ideal; the corrections lie in that
resultant times the ideal. Coefficients at and above `n`, `m` are preserved.

Unlike coprime monic factor lifting, the initial factors need not be monic and
the resultant need not be a unit or a non-zero-divisor. The strict degree bound
on the error fixes coefficients at and above `n + m`. Neither the target product's
actual degree nor its leading coefficient is thereby determined. Loose bounds
need not preserve the initial factor degrees or leading coefficients; specializing
to their natural degrees preserves both individual leading coefficients.

For an ideal contained in the Jacobson radical, a regular resultant gives
uniqueness among pairs with the same product when only the pair differences have
strict degree bounds and the two crossed reference corrections have coefficients
in the resultant times the ideal. Those reference corrections may have arbitrary
degree. This uniqueness requires neither a Henselian pair nor an error bound.
The earlier strict reference-correction neighborhood is a special case; combining
it with Henselian lifting gives a unique pair of corrected polynomials.

A coefficient-map theorem applies the fixed-bound existence result in a Henselian
target containing the image of the source ideal. It requires no Henselian source
and retains both prescribed bounds and the image of the source resultant when
degrees drop. Regularity does not in general pass to the target.

The proofs use Mathlib's Sylvester map and its adjugate. For uniqueness, a
single regular-cancellation stage reduces the assertion to Nakayama's lemma for
the finitely generated ideal of bounded pair-difference coefficients. The
crossed-congruence reduction and coefficient-ideal argument are due to Formal
Frontier Agents.

## Source and generalization

This is a ring-theoretic generalization of I. B. Fesenko and S. V. Vostokov,
*Local Fields and Their Extensions*, second edition (2002), Chapter II, §1,
Proposition (1.1), p. 36. That proposition concerns the integer ring of a complete
discrete valuation field. It prescribes the target degree and its leading
coefficient; its construction preserves both individual factor leading
coefficients. Here arbitrary Henselian pairs replace completeness, prescribed upper bounds
replace the initial natural degrees, and the strict error-degree bound permits
cancellation of the nominal top coefficient over rings with zero divisors. The
book's target-degree and top-product premises recover its case.

For the book's maximal ideal `M`, write `t = v(d) ≤ s`, where `d` is the
resultant. The precision correspondence is `I = M^(s+1-t)`: then
`(d)I = M^(s+1)` and `(d²)I = M^(s+t+1)`, so the book's error ideal
`M^(2s+1)` is contained in `(d²)I`. Completeness supplies the Henselian-pair
input for this power ideal. This uses the full inequality `t ≤ s`, not only
`t = s`, and gives the book's `M^(s+1)` corrections without a uniqueness claim.
-/

@[expose] public section

universe u v w

namespace Polynomial

/-- Factor coefficientwise ideal divisibility without enlarging the original degree bound. -/
private theorem exists_mul_of_coeff_mem_span_singleton_mul
    {R : Type u} [CommSemiring R] (I : Ideal R) (a : R) {p : R[X]} {N : ℕ}
    (hdegree : p.degree < (N : WithBot ℕ))
    (hcoeff : ∀ i : ℕ, p.coeff i ∈ Ideal.span {a} * I) :
    ∃ Q : R[X], Q.degree < (N : WithBot ℕ) ∧
      (∀ i : ℕ, Q.coeff i ∈ I) ∧ p = C a * Q := by
  classical
  choose e heI he using fun i : Fin N ↦
    Ideal.mem_span_singleton_mul.mp (hcoeff (i : ℕ))
  refine ⟨ofFn N e, ofFn_degree_lt e, ?_, ?_⟩
  · intro i
    by_cases hi : i < N
    · simpa only [ofFn_coeff_eq_val_of_lt e hi] using heI ⟨i, hi⟩
    · rw [ofFn_coeff_eq_zero_of_ge e (Nat.le_of_not_gt hi)]
      exact I.zero_mem
  · ext i
    rw [coeff_C_mul]
    by_cases hi : i < N
    · rw [ofFn_coeff_eq_val_of_lt e hi]
      exact (he ⟨i, hi⟩).symm
    · rw [ofFn_coeff_eq_zero_of_ge e (Nat.le_of_not_gt hi), mul_zero]
      exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdegree
        (WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hi)))

end Polynomial

namespace Polynomial

section

attribute [local instance] Classical.propDecidable

private theorem map_ofFn_eq {R : Type u} {S : Type v} [CommSemiring R]
    [CommSemiring S] [DecidableEq R] [DecidableEq S] (φ : R →+* S) (n : ℕ) (a : Fin n → R) :
    (ofFn n a).map φ = ofFn n (fun i ↦ φ (a i)) := by
  ext k
  by_cases hk : k < n
  · simp [hk]
  · simp [ofFn_coeff_eq_zero_of_ge, Nat.le_of_not_gt hk]

private theorem degree_mul_lt_sum {S : Type v} [CommSemiring S]
    {p q : S[X]} {n m : ℕ} (hp : p.degree ≤ (n : WithBot ℕ))
    (hq : q.degree < (m : WithBot ℕ)) : (p * q).degree < (n + m : ℕ) := by
  by_cases hp₀ : p = 0
  · simp [hp₀]
  exact (degree_mul_le p q).trans_lt
    (WithBot.add_lt_add_of_le_of_lt (by simpa using hp₀) hp hq)


/-- The polynomial with bounded coefficient-linear forms associated to a finite family. -/
private noncomputable def coefficientLinearPolynomial {R : Type u} [CommRing R]
    {ι : Type w} [Fintype ι] (n : ℕ) (a : ι → R[X]) : (MvPolynomial ι R)[X] :=
  ofFn n (fun i ↦ ∑ j, MvPolynomial.C ((a j).coeff i) * MvPolynomial.X j)


private theorem coefficientLinearPolynomial_degree {R : Type u} [CommRing R]
    {ι : Type w} [Fintype ι] (n : ℕ) (a : ι → R[X]) :
    (coefficientLinearPolynomial n a).degree < (n : WithBot ℕ) :=
  ofFn_degree_lt (fun i ↦ ∑ j, MvPolynomial.C ((a j).coeff i) * MvPolynomial.X j)

private theorem eval₂_coefficientLinearPolynomial_zero {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {ι : Type w} [Fintype ι]
    (φ : R →+* S) (n : ℕ) (a : ι → R[X]) :
    (coefficientLinearPolynomial n a).map (MvPolynomial.eval₂Hom φ 0) = 0 := by
  classical
  ext k
  by_cases hk : k < n
  · simp [coefficientLinearPolynomial, map_ofFn_eq, hk]
  · simp [coefficientLinearPolynomial, map_ofFn_eq,
      ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)]

private theorem eval₂_coefficientLinearPolynomial {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {ι : Type w} [Fintype ι]
    (φ : R →+* S) (y : ι → S) (n : ℕ) (a : ι → R[X])
    (ha : ∀ j, (a j).degree < (n : WithBot ℕ)) :
    (coefficientLinearPolynomial n a).map (MvPolynomial.eval₂Hom φ y) =
      ∑ j, y j • (a j).map φ := by
  classical
  ext k
  by_cases hk : k < n
  · simp [coefficientLinearPolynomial, map_ofFn_eq, hk, mul_comm]
  · have haz (j : ι) : (a j).coeff k = 0 :=
      coeff_eq_zero_of_degree_lt ((ha j).trans_le
        (WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hk)))
    simp [coefficientLinearPolynomial, map_ofFn_eq,
      ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk), haz]

/-- Universal corrections obtained from the stock adjugate on the monomial basis.
The bounds are fixed, including when coefficients are subsequently mapped. -/
private noncomputable def adjugateCorrections {R : Type u} [CommRing R]
    (n m : ℕ) (g₀ h₀ : R[X]) :
    (MvPolynomial (Fin n ⊕ Fin m) R)[X] × (MvPolynomial (Fin n ⊕ Fin m) R)[X] :=
  let t := fun j : Fin n ⊕ Fin m ↦
    adjSylvester (m := n) (n := m) g₀ h₀
      (degreeLT.basis R (n + m) (finSumFinEquiv j))
  (coefficientLinearPolynomial n (fun j ↦ (t j).1.val),
    coefficientLinearPolynomial m (fun j ↦ (t j).2.val))


private theorem adjugateCorrections_degree {R : Type u} [CommRing R]
    (n m : ℕ) (g₀ h₀ : R[X]) :
    (adjugateCorrections n m g₀ h₀).1.degree < (n : WithBot ℕ) ∧
      (adjugateCorrections n m g₀ h₀).2.degree < (m : WithBot ℕ) := by
  dsimp only [adjugateCorrections]
  exact ⟨coefficientLinearPolynomial_degree n _, coefficientLinearPolynomial_degree m _⟩

private theorem eval_adjugateCorrections {R : Type u} [CommRing R]
    (n m : ℕ) (g₀ h₀ : R[X]) (y : (Fin n ⊕ Fin m) → R) :
    let Y : degreeLT R (n + m) :=
      ⟨ofFn (n + m) (fun i ↦ y (finSumFinEquiv.symm i)),
        mem_degreeLT.mpr (ofFn_degree_lt _)⟩
    let t := adjSylvester (m := n) (n := m) g₀ h₀ Y
    ((adjugateCorrections n m g₀ h₀).1.map (MvPolynomial.eval₂Hom (RingHom.id R) y),
      (adjugateCorrections n m g₀ h₀).2.map (MvPolynomial.eval₂Hom (RingHom.id R) y)) =
        (t.1.val, t.2.val) := by
  classical
  let e : (Fin n ⊕ Fin m) ≃ Fin (n + m) := finSumFinEquiv
  let Y : degreeLT R (n + m) :=
    ⟨ofFn (n + m) (fun i ↦ y (e.symm i)), mem_degreeLT.mpr (ofFn_degree_lt _)⟩
  have hY : (∑ j, y j • degreeLT.basis R (n + m) (e j)) = Y := by
    calc
      _ = ∑ i : Fin (n + m), y (e.symm i) • degreeLT.basis R (n + m) i := by
        simpa only [Equiv.symm_apply_apply] using
          e.sum_comp (fun i ↦ y (e.symm i) • degreeLT.basis R (n + m) i)
      _ = Y := by simpa [Y] using (degreeLT.basis R (n + m)).sum_repr Y
  have ht := congrArg (adjSylvester (m := n) (n := m) g₀ h₀) hY
  simp only [_root_.map_sum, _root_.map_smul] at ht
  dsimp only [adjugateCorrections]
  apply Prod.ext
  · rw [eval₂_coefficientLinearPolynomial _ _ _ _ (fun j ↦
        mem_degreeLT.mp (adjSylvester (m := n) (n := m) g₀ h₀
          (degreeLT.basis R (n + m) (e j))).1.property)]
    let π : degreeLT R n × degreeLT R m →ₗ[R] R[X] :=
      (degreeLT R n).subtype.comp (LinearMap.fst R _ _)
    have hπ := congrArg π ht
    simp only [_root_.map_sum, _root_.map_smul] at hπ
    change (∑ j, y j • (adjSylvester (m := n) (n := m) g₀ h₀
      (degreeLT.basis R (n + m) (e j))).1.val) =
        (adjSylvester (m := n) (n := m) g₀ h₀ Y).1.val at hπ
    simpa only [Polynomial.map_id] using hπ
  · rw [eval₂_coefficientLinearPolynomial _ _ _ _ (fun j ↦
        mem_degreeLT.mp (adjSylvester (m := n) (n := m) g₀ h₀
          (degreeLT.basis R (n + m) (e j))).2.property)]
    let π : degreeLT R n × degreeLT R m →ₗ[R] R[X] :=
      (degreeLT R m).subtype.comp (LinearMap.snd R _ _)
    have hπ := congrArg π ht
    simp only [_root_.map_sum, _root_.map_smul] at hπ
    change (∑ j, y j • (adjSylvester (m := n) (n := m) g₀ h₀
      (degreeLT.basis R (n + m) (e j))).2.val) =
        (adjSylvester (m := n) (n := m) g₀ h₀ Y).2.val at hπ
    simpa only [Polynomial.map_id] using hπ

private theorem eval_adjugateCorrections_linear {R : Type u} [CommRing R]
    (n m : ℕ) (g₀ h₀ : R[X]) (hg : g₀.natDegree ≤ n) (hh : h₀.natDegree ≤ m)
    (y : (Fin n ⊕ Fin m) → R) :
    g₀ * (adjugateCorrections n m g₀ h₀).2.map
        (MvPolynomial.eval₂Hom (RingHom.id R) y) +
      h₀ * (adjugateCorrections n m g₀ h₀).1.map
        (MvPolynomial.eval₂Hom (RingHom.id R) y) =
      C (resultant g₀ h₀ n m) *
        ofFn (n + m) (fun i ↦ y (finSumFinEquiv.symm i)) := by
  let Y : degreeLT R (n + m) :=
    ⟨ofFn (n + m) (fun i ↦ y (finSumFinEquiv.symm i)),
      mem_degreeLT.mpr (ofFn_degree_lt _)⟩
  have ht := eval_adjugateCorrections n m g₀ h₀ y
  have hs := LinearMap.congr_fun (sylveserMap_comp_adjSylvester g₀ h₀ hg hh) Y
  have hp := congrArg (fun p : degreeLT R (n + m) ↦ p.val) hs
  change g₀ * (adjSylvester (m := n) (n := m) g₀ h₀ Y).2.val +
    h₀ * (adjSylvester (m := n) (n := m) g₀ h₀ Y).1.val =
      resultant g₀ h₀ n m • Y.val at hp
  have hU : (adjugateCorrections n m g₀ h₀).1.map
      (MvPolynomial.eval₂Hom (RingHom.id R) y) =
        (adjSylvester (m := n) (n := m) g₀ h₀ Y).1.val := congrArg Prod.fst ht
  have hV : (adjugateCorrections n m g₀ h₀).2.map
      (MvPolynomial.eval₂Hom (RingHom.id R) y) =
        (adjSylvester (m := n) (n := m) g₀ h₀ Y).2.val := congrArg Prod.snd ht
  rw [hU, hV]
  simpa only [smul_eq_C_mul] using hp

/-- The unit-linear residual: its quadratic term is the product of the universal
adjugate corrections, with no division by the resultant. -/
private noncomputable def adjugateUnitResidual {R : Type u} [CommRing R]
    (n m : ℕ) (g₀ h₀ E : R[X]) :
    (Fin n ⊕ Fin m) → MvPolynomial (Fin n ⊕ Fin m) R := fun r ↦
  MvPolynomial.X r +
    ((adjugateCorrections n m g₀ h₀).1 * (adjugateCorrections n m g₀ h₀).2).coeff
      (finSumFinEquiv r : ℕ) - MvPolynomial.C (E.coeff (finSumFinEquiv r : ℕ))

private theorem eval₂_adjugateUnitResidual {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (n m : ℕ) (g₀ h₀ E : R[X])
    (y : (Fin n ⊕ Fin m) → S) (r : Fin n ⊕ Fin m) :
    MvPolynomial.eval₂Hom φ y (adjugateUnitResidual n m g₀ h₀ E r) =
      y r + ((adjugateCorrections n m g₀ h₀).1.map (MvPolynomial.eval₂Hom φ y) *
        (adjugateCorrections n m g₀ h₀).2.map (MvPolynomial.eval₂Hom φ y)).coeff
          (finSumFinEquiv r : ℕ) - φ (E.coeff (finSumFinEquiv r : ℕ)) := by
  unfold adjugateUnitResidual
  rw [map_sub, map_add, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
    ← coeff_map, Polynomial.map_mul]

private theorem eval₂_adjugateCorrections_zero {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (n m : ℕ) (g₀ h₀ : R[X]) :
    ((adjugateCorrections n m g₀ h₀).1.map (MvPolynomial.eval₂Hom φ 0),
      (adjugateCorrections n m g₀ h₀).2.map (MvPolynomial.eval₂Hom φ 0)) = (0, 0) := by
  dsimp only [adjugateCorrections]
  rw [eval₂_coefficientLinearPolynomial_zero, eval₂_coefficientLinearPolynomial_zero]

private theorem eval₂_adjugateUnitResidual_zero {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (n m : ℕ) (g₀ h₀ E : R[X])
    (r : Fin n ⊕ Fin m) :
    MvPolynomial.eval₂Hom φ 0 (adjugateUnitResidual n m g₀ h₀ E r) =
      -φ (E.coeff (finSumFinEquiv r : ℕ)) := by
  have hU : (adjugateCorrections n m g₀ h₀).1.map (MvPolynomial.eval₂Hom φ 0) = 0 :=
    congrArg Prod.fst (eval₂_adjugateCorrections_zero φ n m g₀ h₀)
  have hV : (adjugateCorrections n m g₀ h₀).2.map (MvPolynomial.eval₂Hom φ 0) = 0 :=
    congrArg Prod.snd (eval₂_adjugateCorrections_zero φ n m g₀ h₀)
  rw [eval₂_adjugateUnitResidual, hU, hV]
  simp


private theorem eval_adjugateUnitResidual_zero_mem {R : Type u} [CommRing R]
    (I : Ideal R) (n m : ℕ) (g₀ h₀ E : R[X]) (hE : ∀ k, E.coeff k ∈ I)
    (r : Fin n ⊕ Fin m) :
    MvPolynomial.eval₂Hom (RingHom.id R) 0 (adjugateUnitResidual n m g₀ h₀ E r) ∈ I := by
  rw [eval₂_adjugateUnitResidual_zero, RingHom.id_apply]
  exact I.neg_mem (hE _)

private theorem pderiv_adjugateUnitResidual {R : Type u} [CommRing R]
    (n m : ℕ) (g₀ h₀ E : R[X]) (r i : Fin n ⊕ Fin m) :
    MvPolynomial.pderiv i (adjugateUnitResidual n m g₀ h₀ E r) =
      (if r = i then 1 else 0) + MvPolynomial.pderiv i
        (((adjugateCorrections n m g₀ h₀).1 * (adjugateCorrections n m g₀ h₀).2).coeff
          (finSumFinEquiv r : ℕ)) := by
  classical
  simp [adjugateUnitResidual, MvPolynomial.pderiv_X, Pi.single_apply]

private theorem eval₂_pderiv_coeff_mul_of_zero {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {ι : Type w} (φ : R →+* S)
    (p q : (MvPolynomial ι R)[X])
    (hp : p.map (MvPolynomial.eval₂Hom φ 0) = 0)
    (hq : q.map (MvPolynomial.eval₂Hom φ 0) = 0) (i : ι) (k : ℕ) :
    MvPolynomial.eval₂Hom φ 0 (MvPolynomial.pderiv i ((p * q).coeff k)) = 0 := by
  classical
  have hp' (j : ℕ) : MvPolynomial.eval₂Hom φ 0 (p.coeff j) = 0 := by
    simpa only [coeff_map, coeff_zero] using congrArg (fun t : S[X] ↦ t.coeff j) hp
  have hq' (j : ℕ) : MvPolynomial.eval₂Hom φ 0 (q.coeff j) = 0 := by
    simpa only [coeff_map, coeff_zero] using congrArg (fun t : S[X] ↦ t.coeff j) hq
  rw [coeff_mul, _root_.map_sum, _root_.map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hp', hq',
    zero_mul, mul_zero, add_zero]

private theorem eval₂_pderiv_adjugateUnitResidual_zero {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (n m : ℕ) (g₀ h₀ E : R[X]) :
    (fun r i : Fin n ⊕ Fin m ↦ MvPolynomial.eval₂Hom φ 0
      (MvPolynomial.pderiv i (adjugateUnitResidual n m g₀ h₀ E r))) =
        (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) S) := by
  classical
  funext r i
  rw [pderiv_adjugateUnitResidual, map_add,
    eval₂_pderiv_coeff_mul_of_zero φ _ _
      (congrArg Prod.fst (eval₂_adjugateCorrections_zero φ n m g₀ h₀))
      (congrArg Prod.snd (eval₂_adjugateCorrections_zero φ n m g₀ h₀))]
  by_cases h : r = i <;> simp [h, Matrix.one_apply]

private theorem coeff_eval_coefficientLinearPolynomial_mem {R : Type u} [CommRing R]
    {ι : Type w} [Fintype ι] (I : Ideal R) (n : ℕ) (a : ι → R[X])
    (y : ι → R) (hy : ∀ j, y j ∈ I) (k : ℕ) :
    ((coefficientLinearPolynomial n a).map (MvPolynomial.eval₂Hom (RingHom.id R) y)).coeff k
      ∈ I := by
  classical
  by_cases hk : k < n
  · simp only [coefficientLinearPolynomial, coeff_map, ofFn_coeff_eq_val_of_lt _ hk,
      map_sum, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply]
    exact I.sum_mem (fun j hj ↦ I.mul_mem_left _ (hy j))
  · simp [coefficientLinearPolynomial, map_ofFn_eq,
      ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)]

private theorem eq_zero_of_C_mul_eq_zero_of_regular {R : Type u} [CommRing R]
    {d : R} (hd : d ∈ nonZeroDivisors R) {p : R[X]} (hp : C d * p = 0) : p = 0 := by
  ext k
  apply mem_nonZeroDivisors_iff_left.mp hd
  simpa only [coeff_C_mul, coeff_zero] using congrArg (fun q : R[X] ↦ q.coeff k) hp

private theorem coeff_mul_mem_ideal_mul {R : Type u} [CommRing R]
    (I J : Ideal R) {p q : R[X]} (hp : ∀ k, p.coeff k ∈ I)
    (hq : ∀ k, q.coeff k ∈ J) (k : ℕ) : (p * q).coeff k ∈ I * J := by
  classical
  rw [coeff_mul]
  exact (I * J).sum_mem fun a ha ↦ Ideal.mul_mem_mul (hp a.1) (hq a.2)

private theorem coeff_adjSylvester_mem {R : Type u} [CommRing R]
    (K : Ideal R) (n m : ℕ) (g₀ h₀ : R[X]) (P : degreeLT R (n + m))
    (hP : ∀ k, P.val.coeff k ∈ K) (k : ℕ) :
    ((adjSylvester (m := n) (n := m) g₀ h₀ P).1.val).coeff k ∈ K ∧
      ((adjSylvester (m := n) (n := m) g₀ h₀ P).2.val).coeff k ∈ K := by
  classical
  let y : (Fin n ⊕ Fin m) → R := fun r ↦ P.val.coeff (finSumFinEquiv r)
  have hY : (⟨ofFn (n + m) (fun i ↦ y (finSumFinEquiv.symm i)),
      mem_degreeLT.mpr (ofFn_degree_lt _)⟩ : degreeLT R (n + m)) = P := by
    apply Subtype.ext
    ext j
    by_cases hj : j < n + m
    · simp [y, hj]
    · rw [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hj)]
      exact (coeff_eq_zero_of_degree_lt ((mem_degreeLT.mp P.property).trans_le
        (WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hj)))).symm
  have ht := eval_adjugateCorrections n m g₀ h₀ y
  dsimp only at ht
  rw [hY] at ht
  have hU := coeff_eval_coefficientLinearPolynomial_mem K n
    (fun r ↦ (adjSylvester (m := n) (n := m) g₀ h₀
      (degreeLT.basis R (n + m) (finSumFinEquiv r))).1.val) y (fun r ↦ hP _) k
  have hV := coeff_eval_coefficientLinearPolynomial_mem K m
    (fun r ↦ (adjSylvester (m := n) (n := m) g₀ h₀
      (degreeLT.basis R (n + m) (finSumFinEquiv r))).2.val) y (fun r ↦ hP _) k
  change (((adjugateCorrections n m g₀ h₀).1.map
    (MvPolynomial.eval₂Hom (RingHom.id R) y)).coeff k) ∈ K at hU
  change (((adjugateCorrections n m g₀ h₀).2.map
    (MvPolynomial.eval₂Hom (RingHom.id R) y)).coeff k) ∈ K at hV
  have htU := congrArg Prod.fst ht
  have htV := congrArg Prod.snd ht
  dsimp only at htU htV
  rw [htU] at hU
  rw [htV] at hV
  exact ⟨hU, hV⟩

/-- Bounded pair differences vanish when their reference Sylvester image is
controlled by two crossed, possibly unbounded, corrections. -/
private theorem eq_zero_of_regular_resultant_relation
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) (n m : ℕ) (g₀ h₀ : R[X])
    (hg₀ : g₀.natDegree ≤ n) (hh₀ : h₀.natDegree ≤ m)
    (hd : resultant g₀ h₀ n m ∈ nonZeroDivisors R)
    (u v a b : R[X])
    (hu : u.degree < (n : WithBot ℕ)) (hv : v.degree < (m : WithBot ℕ))
    (ha : ∀ k, a.coeff k ∈ Ideal.span {resultant g₀ h₀ n m} * I)
    (hb : ∀ k, b.coeff k ∈ Ideal.span {resultant g₀ h₀ n m} * I)
    (hlinear : g₀ * v + h₀ * u + (a * v + b * u) = 0) : u = 0 ∧ v = 0 := by
  classical
  let d := resultant g₀ h₀ n m
  let D : degreeLT R n × degreeLT R m :=
    (⟨u, mem_degreeLT.mpr hu⟩, ⟨v, mem_degreeLT.mpr hv⟩)
  let S := sylvesterMap g₀ h₀ hg₀ hh₀ D
  let Q := a * v + b * u
  -- Only bounded pair-difference coefficients generate the finite ideal.
  let c : (Fin n ⊕ Fin m) → R := Sum.elim
    (fun i ↦ u.coeff i) (fun j ↦ v.coeff j)
  let J : Ideal R := Ideal.span (Set.range c)
  have huJ (k : ℕ) : u.coeff k ∈ J := by
    by_cases hk : k < n
    · exact Ideal.subset_span ⟨Sum.inl ⟨k, hk⟩, rfl⟩
    · rw [coeff_eq_zero_of_degree_lt (hu.trans_le
        (WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hk)))]
      exact J.zero_mem
  have hvJ (k : ℕ) : v.coeff k ∈ J := by
    by_cases hk : k < m
    · exact Ideal.subset_span ⟨Sum.inr ⟨k, hk⟩, rfl⟩
    · rw [coeff_eq_zero_of_degree_lt (hv.trans_le
        (WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hk)))]
      exact J.zero_mem
  have hQIJ (k : ℕ) : Q.coeff k ∈ Ideal.span {d} * (I * J) := by
    have hmem : Q.coeff k ∈ (Ideal.span {d} * I) * J := by
      dsimp only [Q]
      rw [coeff_add]
      exact ((Ideal.span {d} * I) * J).add_mem
        (coeff_mul_mem_ideal_mul (Ideal.span {d} * I) J ha hvJ k)
        (coeff_mul_mem_ideal_mul (Ideal.span {d} * I) J hb huJ k)
    simpa only [mul_assoc] using hmem
  have hSQ : S.val = -Q := by
    apply eq_neg_of_add_eq_zero_left
    change g₀ * v + h₀ * u + (a * v + b * u) = 0
    exact hlinear
  have hScoeff (k : ℕ) : S.val.coeff k ∈ Ideal.span {d} * (I * J) := by
    rw [hSQ, coeff_neg]
    exact (Ideal.span {d} * (I * J)).neg_mem (hQIJ k)
  -- Extract from the bounded reference output, not from the unbounded error Q.
  obtain ⟨q, hq, hqIJ, hSq⟩ := exists_mul_of_coeff_mem_span_singleton_mul
    (I * J) d (mem_degreeLT.mp S.property) hScoeff
  let P : degreeLT R (n + m) := ⟨q, mem_degreeLT.mpr hq⟩
  let A := adjSylvester (m := n) (n := m) g₀ h₀
  have hSP : sylvesterMap g₀ h₀ hg₀ hh₀ D = d • P := by
    apply Subtype.ext
    change S.val = d • q
    simpa only [smul_eq_C_mul] using hSq
  have hAS : A (sylvesterMap g₀ h₀ hg₀ hh₀ D) = d • D :=
    LinearMap.congr_fun (adjSylvester_comp_sylveserMap g₀ h₀ hg₀ hh₀) D
  have hAdj := congrArg A hSP
  rw [map_smul, hAS] at hAdj
  have hdzU := congrArg (fun t : degreeLT R n × degreeLT R m ↦ t.1.val) hAdj
  have hdzV := congrArg (fun t : degreeLT R n × degreeLT R m ↦ t.2.val) hAdj
  change d • u = d • (A P).1.val at hdzU
  change d • v = d • (A P).2.val at hdzV
  -- The single regular-cancellation stage: d times each coordinate difference is zero.
  have hzU : u = (A P).1.val := by
    apply sub_eq_zero.mp
    apply eq_zero_of_C_mul_eq_zero_of_regular hd
    rw [mul_sub]
    exact sub_eq_zero.mpr (by simpa only [smul_eq_C_mul] using hdzU)
  have hzV : v = (A P).2.val := by
    apply sub_eq_zero.mp
    apply eq_zero_of_C_mul_eq_zero_of_regular hd
    rw [mul_sub]
    exact sub_eq_zero.mpr (by simpa only [smul_eq_C_mul] using hdzV)
  have huIJ (k : ℕ) : u.coeff k ∈ I * J := by
    rw [hzU]
    exact (coeff_adjSylvester_mem (I * J) n m g₀ h₀ P hqIJ k).1
  have hvIJ (k : ℕ) : v.coeff k ∈ I * J := by
    rw [hzV]
    exact (coeff_adjSylvester_mem (I * J) n m g₀ h₀ P hqIJ k).2
  have hJfg : J.FG := by
    refine ⟨Finset.univ.image c, ?_⟩
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rfl
  have hJle : J ≤ I • J := by
    rw [Ideal.smul_eq_mul]
    apply Ideal.span_le.mpr
    rintro x ⟨r, rfl⟩
    cases r with
    | inl i => exact huIJ i
    | inr j => exact hvIJ j
  have hJzero : J = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I J hJfg hJle hI
  constructor
  · ext k
    simpa only [hJzero, Ideal.mem_bot, coeff_zero] using huJ k
  · ext k
    simpa only [hJzero, Ideal.mem_bot, coeff_zero] using hvJ k

/-- A zero of the unit residual in the ideal yields the required factorization.
The expansion multiplies the residual by the resultant squared; it never cancels it. -/
private theorem factorization_of_adjugateUnitResidual {R : Type u} [CommRing R]
    (I : Ideal R) (n m : ℕ) (f g₀ h₀ E : R[X])
    (hg : g₀.natDegree ≤ n) (hh : h₀.natDegree ≤ m)
    (hE : E.degree < (n + m : ℕ))
    (herror : f - g₀ * h₀ = C (resultant g₀ h₀ n m ^ 2) * E)
    (y : (Fin n ⊕ Fin m) → R) (hy : ∀ r, y r ∈ I)
    (hQ : ∀ r, MvPolynomial.eval₂Hom (RingHom.id R) y
      (adjugateUnitResidual n m g₀ h₀ E r) = 0) :
    ∃ g h : R[X], f = g * h ∧
      (g - g₀).degree < (n : WithBot ℕ) ∧ (h - h₀).degree < (m : WithBot ℕ) ∧
      ∀ k : ℕ, (g - g₀).coeff k ∈ Ideal.span {resultant g₀ h₀ n m} * I ∧
        (h - h₀).coeff k ∈ Ideal.span {resultant g₀ h₀ n m} * I := by
  classical
  let d := resultant g₀ h₀ n m
  let a := (adjugateCorrections n m g₀ h₀).1.map (MvPolynomial.eval₂Hom (RingHom.id R) y)
  let b := (adjugateCorrections n m g₀ h₀).2.map (MvPolynomial.eval₂Hom (RingHom.id R) y)
  let Y := ofFn (n + m) (fun i ↦ y (finSumFinEquiv.symm i))
  have ha : a.degree < (n : WithBot ℕ) :=
    degree_map_le.trans_lt (adjugateCorrections_degree n m g₀ h₀).1
  have hb : b.degree < (m : WithBot ℕ) :=
    degree_map_le.trans_lt (adjugateCorrections_degree n m g₀ h₀).2
  have hY : Y.degree < (n + m : ℕ) := ofFn_degree_lt _
  have hqdeg : (Y + a * b - E).degree < (n + m : ℕ) :=
    (degree_sub_le _ _).trans_lt (max_lt
      ((degree_add_le _ _).trans_lt (max_lt hY (degree_mul_lt_sum ha.le hb))) hE)
  have hqzero : Y + a * b - E = 0 := by
    ext k
    by_cases hk : k < n + m
    · have h := hQ (finSumFinEquiv.symm ⟨k, hk⟩)
      rw [eval₂_adjugateUnitResidual] at h
      simpa [Y, a, b, hk] using h
    · exact coeff_eq_zero_of_degree_lt (hqdeg.trans_le
        (WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hk)))
  have hlinear : g₀ * b + h₀ * a = C d * Y :=
    eval_adjugateCorrections_linear n m g₀ h₀ hg hh y
  have hexpand : (g₀ + C d * a) * (h₀ + C d * b) - f =
      C (d ^ 2) * (Y + a * b - E) := by
    calc
      _ = C d * (g₀ * b + h₀ * a) + C (d ^ 2) * (a * b) - (f - g₀ * h₀) := by
        simp only [map_pow]
        ring
      _ = _ := by rw [hlinear, herror]; simp only [map_pow]; ring
  refine ⟨g₀ + C d * a, h₀ + C d * b, ?_, ?_, ?_, ?_⟩
  · exact (sub_eq_zero.mp (hexpand.trans (by rw [hqzero, mul_zero]))).symm
  · simpa only [add_sub_cancel_left, C_mul'] using (degree_smul_le d a).trans_lt ha
  · simpa only [add_sub_cancel_left, C_mul'] using (degree_smul_le d b).trans_lt hb
  · intro k
    have haI : a.coeff k ∈ I :=
      coeff_eval_coefficientLinearPolynomial_mem I n _ y hy k
    have hbI : b.coeff k ∈ I :=
      coeff_eval_coefficientLinearPolynomial_mem I m _ y hy k
    simp only [add_sub_cancel_left, coeff_C_mul]
    exact ⟨Ideal.mem_span_singleton_mul.mpr ⟨_, haI, rfl⟩,
      Ideal.mem_span_singleton_mul.mpr ⟨_, hbI, rfl⟩⟩

end

/-- Two factorizations are equal if their pair differences have the prescribed
strict degree bounds and the two crossed reference corrections have coefficients
in the resultant times a Jacobson ideal. The reference corrections themselves may
have arbitrary degree. The resultant uses the fixed nominal bounds `n`, `m`. -/
theorem eq_factors_of_regular_resultant_of_degree_sub_lt
    {R : Type u} [CommRing R]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {n m : ℕ} {g₀ h₀ g h g₂ h₂ : Polynomial R}
    (hg₀ : g₀.natDegree ≤ n) (hh₀ : h₀.natDegree ≤ m)
    (hd : g₀.resultant h₀ n m ∈ nonZeroDivisors R)
    (hprod : g * h = g₂ * h₂)
    (hgg₂ : (g - g₂).degree < (n : WithBot ℕ))
    (hhh₂ : (h - h₂).degree < (m : WithBot ℕ))
    (hg : ∀ k : ℕ,
      (g - g₀).coeff k ∈ Ideal.span {g₀.resultant h₀ n m} * I)
    (hh₂ : ∀ k : ℕ,
      (h₂ - h₀).coeff k ∈ Ideal.span {g₀.resultant h₀ n m} * I) :
    g = g₂ ∧ h = h₂ := by
  have hlinear : g₀ * (h - h₂) + h₀ * (g - g₂) +
      ((g - g₀) * (h - h₂) + (h₂ - h₀) * (g - g₂)) = 0 := by
    calc
      _ = g * h - g₂ * h₂ := by ring
      _ = 0 := sub_eq_zero.mpr hprod
  obtain ⟨hu, hv⟩ := eq_zero_of_regular_resultant_relation I hI n m g₀ h₀
    hg₀ hh₀ hd (g - g₂) (h - h₂) (g - g₀) (h₂ - h₀) hgg₂ hhh₂ hg hh₂ hlinear
  exact ⟨sub_eq_zero.mp hu, sub_eq_zero.mp hv⟩

/-- Two factorizations in the same strict-degree correction neighborhood are equal
if its controlling resultant is a non-zero-divisor and its ideal is contained in
the Jacobson radical. The nominal bounds `n` and `m` may exceed the natural degrees
of the initial factors: the corrections fix coefficients at and above these bounds,
not necessarily their original leading coefficients. No Henselian hypothesis is needed. -/
theorem eq_factors_of_regular_resultant
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) {n m : ℕ} {g₀ h₀ g h g' h' : R[X]}
    (hg₀ : g₀.natDegree ≤ n) (hh₀ : h₀.natDegree ≤ m)
    (hd : resultant g₀ h₀ n m ∈ nonZeroDivisors R) (hprod : g * h = g' * h')
    (hg : (g - g₀).degree < (n : WithBot ℕ))
    (hh : (h - h₀).degree < (m : WithBot ℕ))
    (hg' : (g' - g₀).degree < (n : WithBot ℕ))
    (hh' : (h' - h₀).degree < (m : WithBot ℕ))
    (hcoeff : ∀ k : ℕ, (g - g₀).coeff k ∈ Ideal.span {resultant g₀ h₀ n m} * I ∧
      (h - h₀).coeff k ∈ Ideal.span {resultant g₀ h₀ n m} * I)
    (hcoeff' : ∀ k : ℕ, (g' - g₀).coeff k ∈ Ideal.span {resultant g₀ h₀ n m} * I ∧
      (h' - h₀).coeff k ∈ Ideal.span {resultant g₀ h₀ n m} * I) :
    g = g' ∧ h = h' := by
  apply eq_factors_of_regular_resultant_of_degree_sub_lt I hI hg₀ hh₀ hd hprod
  · have heq : g - g' = (g - g₀) - (g' - g₀) := by ring
    rw [heq]
    exact (degree_sub_le _ _).trans_lt (max_lt hg hg')
  · have heq : h - h' = (h - h₀) - (h' - h₀) := by ring
    rw [heq]
    exact (degree_sub_le _ _).trans_lt (max_lt hh hh')
  · exact fun k ↦ (hcoeff k).1
  · exact fun k ↦ (hcoeff' k).2

/-- Uniqueness in the resultant-controlled fixed-leading-coefficient neighborhood
at the natural degrees of the initial factors. -/
theorem eq_factors_of_regular_resultant_natDegree
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) {g₀ h₀ g h g' h' : R[X]}
    (hd : resultant g₀ h₀ g₀.natDegree h₀.natDegree ∈ nonZeroDivisors R)
    (hprod : g * h = g' * h')
    (hg : (g - g₀).degree < (g₀.natDegree : WithBot ℕ))
    (hh : (h - h₀).degree < (h₀.natDegree : WithBot ℕ))
    (hg' : (g' - g₀).degree < (g₀.natDegree : WithBot ℕ))
    (hh' : (h' - h₀).degree < (h₀.natDegree : WithBot ℕ))
    (hcoeff : ∀ k : ℕ,
      (g - g₀).coeff k ∈ Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree} * I ∧
        (h - h₀).coeff k ∈ Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree} * I)
    (hcoeff' : ∀ k : ℕ,
      (g' - g₀).coeff k ∈ Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree} * I ∧
        (h' - h₀).coeff k ∈ Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree} * I) :
    g = g' ∧ h = h' :=
  eq_factors_of_regular_resultant I hI le_rfl le_rfl hd hprod hg hh hg' hh' hcoeff hcoeff'

/-- A resultant-squared error over a Henselian pair admits a factorization with
strictly bounded corrections in the resultant times the ideal. The resultant
uses the prescribed bounds `n`, `m`, which need only bound the initial natural
degrees. Coefficients at and above those bounds are preserved; lower leading
coefficients and natural degrees need not be preserved for loose bounds.

This generalizes the complete discrete valuation criterion of Fesenko–Vostokov,
Chapter II, §1, Proposition (1.1), as explained in the module documentation.
No regularity, monicity, or positivity of the bounds is required. -/
theorem exists_factorization_of_resultant_sq_of_natDegree_le
    {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I]
    {n m : ℕ} {f g₀ h₀ : R[X]}
    (hg₀ : g₀.natDegree ≤ n) (hh₀ : h₀.natDegree ≤ m)
    (hdegree : (f - g₀ * h₀).degree <
      (n + m : WithBot ℕ))
    (herror : ∀ i : ℕ, (f - g₀ * h₀).coeff i ∈
      Ideal.span {resultant g₀ h₀ n m ^ 2} * I) :
    ∃ g h : R[X], f = g * h ∧
      (g - g₀).degree < (n : WithBot ℕ) ∧
      (h - h₀).degree < (m : WithBot ℕ) ∧
      ∀ i : ℕ,
        (g - g₀).coeff i ∈
            Ideal.span {resultant g₀ h₀ n m} * I ∧
          (h - h₀).coeff i ∈
            Ideal.span {resultant g₀ h₀ n m} * I := by
  classical
  let d := resultant g₀ h₀ n m
  obtain ⟨E, hE, hEI, hEq⟩ := exists_mul_of_coeff_mem_span_singleton_mul
    (N := n + m) I (d ^ 2) hdegree herror
  let Q := adjugateUnitResidual n m g₀ h₀ E
  have hzero : ∀ r : Fin n ⊕ Fin m, MvPolynomial.eval 0 (Q r) ∈ I :=
    eval_adjugateUnitResidual_zero_mem I n m g₀ h₀ E hEI
  have hj : (fun r i : Fin n ⊕ Fin m ↦
      MvPolynomial.eval 0 (MvPolynomial.pderiv i (Q r))) =
        (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) R) :=
    eval₂_pderiv_adjugateUnitResidual_zero (RingHom.id R) n m g₀ h₀ E
  have hdet : IsUnit (Matrix.det (fun r i : Fin n ⊕ Fin m ↦
      MvPolynomial.eval 0 (MvPolynomial.pderiv i (Q r)))) := by
    rw [hj, Matrix.det_one]
    exact isUnit_one
  obtain ⟨y, ⟨hyQ, hyI⟩, _⟩ :=
    HenselianRing.existsUnique_root_of_isUnit_det_jacobian Q 0 hzero hdet
  have hyI' : ∀ r, y r ∈ I := by
    simpa only [Pi.zero_apply, sub_zero] using hyI
  exact factorization_of_adjugateUnitResidual I n m f g₀ h₀ E
    hg₀ hh₀ hE hEq y hyI' hyQ

/-- A factorization whose error lies in the resultant squared times a Henselian
ideal lifts to an exact factorization, with strict-degree corrections in the
resultant times that ideal.

This generalizes the complete discrete valuation criterion of Fesenko–Vostokov,
Chapter II, §1, Proposition (1.1), as explained in the module documentation.
Neither initial factor is required to be monic. There is no cancellation,
nonvanishing, locality, completeness, or nontriviality hypothesis. The error's
degree bound expresses agreement at the sum of the initial factor natural degrees,
not an equality of actual target degrees over rings with zero divisors. Both
individual factor leading coefficients are preserved; no uniqueness of the
corrected factors is asserted. -/
theorem exists_factorization_of_resultant_sq
    {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I]
    {f g₀ h₀ : R[X]}
    (hdegree : (f - g₀ * h₀).degree <
      (g₀.natDegree + h₀.natDegree : WithBot ℕ))
    (herror : ∀ i : ℕ, (f - g₀ * h₀).coeff i ∈
      Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree ^ 2} * I) :
    ∃ g h : R[X], f = g * h ∧
      (g - g₀).degree < (g₀.natDegree : WithBot ℕ) ∧
      (h - h₀).degree < (h₀.natDegree : WithBot ℕ) ∧
      ∀ i : ℕ,
        (g - g₀).coeff i ∈
            Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree} * I ∧
          (h - h₀).coeff i ∈
            Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree} * I := by
  exact exists_factorization_of_resultant_sq_of_natDegree_le I le_rfl le_rfl hdegree herror

/-- A regular fixed-index resultant makes Henselian factor lifting unique among
pairs whose corrections have strict prescribed degree bounds and coefficients in
the resultant times the ideal. Uniqueness concerns polynomial pairs, not the
coefficient witnesses used to construct them. Loose bounds preserve coefficients
at and above the bounds, not necessarily the initial leading coefficients. -/
theorem existsUnique_factorization_of_resultant_sq_of_natDegree_le
    {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I]
    {n m : ℕ} {f g₀ h₀ : R[X]}
    (hg₀ : g₀.natDegree ≤ n) (hh₀ : h₀.natDegree ≤ m)
    (hd : resultant g₀ h₀ n m ∈ nonZeroDivisors R)
    (hdegree : (f - g₀ * h₀).degree <
      (n + m : WithBot ℕ))
    (herror : ∀ k : ℕ, (f - g₀ * h₀).coeff k ∈
      Ideal.span {resultant g₀ h₀ n m ^ 2} * I) :
    ∃! p : R[X] × R[X], f = p.1 * p.2 ∧
      (p.1 - g₀).degree < (n : WithBot ℕ) ∧
      (p.2 - h₀).degree < (m : WithBot ℕ) ∧
      ∀ k : ℕ,
        (p.1 - g₀).coeff k ∈
            Ideal.span {resultant g₀ h₀ n m} * I ∧
          (p.2 - h₀).coeff k ∈
            Ideal.span {resultant g₀ h₀ n m} * I := by
  obtain ⟨g, h, hprod, hg, hh, hcoeff⟩ := exists_factorization_of_resultant_sq_of_natDegree_le
    I hg₀ hh₀ hdegree herror
  refine ⟨(g, h), ⟨hprod, hg, hh, hcoeff⟩, ?_⟩
  rintro ⟨g', h'⟩ ⟨hprod', hg', hh', hcoeff'⟩
  obtain ⟨heg, heh⟩ := eq_factors_of_regular_resultant I HenselianRing.jac hg₀ hh₀ hd
    (hprod'.symm.trans hprod) hg' hh' hg hh hcoeff' hcoeff
  exact Prod.ext heg heh

/-- Ideal-power precision for resultant-controlled factorization over a Henselian pair.
If the original-degree resultant generates `M ^ t`, an error in `M ^ (2 * s + 1)`
with `t ≤ s` admits corrections in `M ^ (s + 1)`, without changing the strict
correction-degree bounds.

This is the ideal-power form of the construction of Fesenko and Vostokov,
*Local Fields and Their Extensions*, Chapter II, §1, Proposition (1.1), obtained
from `exists_factorization_of_resultant_sq` at the subideal `M ^ (s + 1 - t)`.
No regularity of the resultant is required. -/
theorem exists_factorization_of_resultant_span_eq_pow
    {R : Type u} [CommRing R] (M : Ideal R) [HenselianRing R M]
    {f g₀ h₀ : R[X]} {s t : ℕ}
    (hdegree : (f - g₀ * h₀).degree <
      (g₀.natDegree + h₀.natDegree : WithBot ℕ))
    (hresultant : Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree} = M ^ t)
    (ht : t ≤ s)
    (herror : ∀ i : ℕ, (f - g₀ * h₀).coeff i ∈ M ^ (2 * s + 1)) :
    ∃ g h : R[X], f = g * h ∧
      (g - g₀).degree < (g₀.natDegree : WithBot ℕ) ∧
      (h - h₀).degree < (h₀.natDegree : WithBot ℕ) ∧
      ∀ i : ℕ, (g - g₀).coeff i ∈ M ^ (s + 1) ∧
        (h - h₀).coeff i ∈ M ^ (s + 1) := by
  let e := s + 1 - t
  have he : 0 < e := by dsimp [e]; omega
  let : HenselianRing R (M ^ e) :=
    HenselianRing.of_le (Ideal.pow_le_self (Nat.ne_of_gt he))
  have hte : t + e = s + 1 := by dsimp [e]; omega
  have htte : t * 2 + e = s + t + 1 := by dsimp [e]; omega
  have hdCorr : Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree} * M ^ e =
      M ^ (s + 1) := by
    rw [hresultant, ← pow_add, hte]
  have hdSq : Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree ^ 2} * M ^ e =
      M ^ (s + t + 1) := by
    rw [← Ideal.span_singleton_pow _ 2, hresultant, ← pow_mul, ← pow_add, htte]
  have herror' : ∀ i : ℕ, (f - g₀ * h₀).coeff i ∈
      Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree ^ 2} * M ^ e := by
    intro i
    rw [hdSq]
    exact Ideal.pow_le_pow_right (by omega : s + t + 1 ≤ 2 * s + 1) (herror i)
  obtain ⟨g, h, hfact, hg, hh, hcorr⟩ :=
    exists_factorization_of_resultant_sq (M ^ e) hdegree herror'
  refine ⟨g, h, hfact, hg, hh, fun i ↦ ?_⟩
  simpa only [hdCorr] using hcorr i

/-- A resultant-squared error over a Henselian pair has a unique corrected pair
in the resultant-controlled fixed-leading-coefficient neighborhood when the
resultant is a non-zero-divisor. Uniqueness is among pairs of polynomials, not
among coefficient witnesses used to construct them. -/
theorem existsUnique_factorization_of_resultant_sq
    {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I]
    {f g₀ h₀ : R[X]}
    (hd : resultant g₀ h₀ g₀.natDegree h₀.natDegree ∈ nonZeroDivisors R)
    (hdegree : (f - g₀ * h₀).degree <
      (g₀.natDegree + h₀.natDegree : WithBot ℕ))
    (herror : ∀ k : ℕ, (f - g₀ * h₀).coeff k ∈
      Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree ^ 2} * I) :
    ∃! p : R[X] × R[X], f = p.1 * p.2 ∧
      (p.1 - g₀).degree < (g₀.natDegree : WithBot ℕ) ∧
      (p.2 - h₀).degree < (h₀.natDegree : WithBot ℕ) ∧
      ∀ k : ℕ,
        (p.1 - g₀).coeff k ∈
            Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree} * I ∧
          (p.2 - h₀).coeff k ∈
            Ideal.span {resultant g₀ h₀ g₀.natDegree h₀.natDegree} * I := by
  exact existsUnique_factorization_of_resultant_sq_of_natDegree_le
    I le_rfl le_rfl hd hdegree herror

/-- A coefficient map carries a resultant-squared factorization problem to any
Henselian target pair containing the image of the source ideal. The prescribed
bounds and the image of the fixed-index source resultant are retained even when
initial degrees drop. The source pair need not be Henselian, and neither
injectivity nor regularity of either resultant is required. -/
theorem exists_factorization_of_resultant_sq_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (J : Ideal S) [HenselianRing S J]
    (hIJ : Ideal.map φ I ≤ J) {n m : ℕ} {f g₀ h₀ : R[X]}
    (hg₀ : g₀.natDegree ≤ n) (hh₀ : h₀.natDegree ≤ m)
    (hdegree : (f - g₀ * h₀).degree < (n + m : WithBot ℕ))
    (herror : ∀ k : ℕ, (f - g₀ * h₀).coeff k ∈
      Ideal.span {resultant g₀ h₀ n m ^ 2} * I) :
    ∃ G H : S[X], f.map φ = G * H ∧
      (G - g₀.map φ).degree < (n : WithBot ℕ) ∧
      (H - h₀.map φ).degree < (m : WithBot ℕ) ∧
      ∀ k : ℕ,
        (G - g₀.map φ).coeff k ∈ Ideal.span {φ (resultant g₀ h₀ n m)} * J ∧
        (H - h₀.map φ).coeff k ∈ Ideal.span {φ (resultant g₀ h₀ n m)} * J := by
  have hmap : f.map φ - g₀.map φ * h₀.map φ = (f - g₀ * h₀).map φ := by
    simp only [Polynomial.map_sub, Polynomial.map_mul]
  have hdegree' : (f.map φ - g₀.map φ * h₀.map φ).degree <
      (n + m : WithBot ℕ) := by
    rw [hmap]
    exact degree_map_le.trans_lt hdegree
  have hideal : Ideal.map φ (Ideal.span {resultant g₀ h₀ n m ^ 2} * I) ≤
      Ideal.span {φ (resultant g₀ h₀ n m) ^ 2} * J := by
    rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_pow]
    exact Ideal.mul_mono_right hIJ
  have herror' : ∀ k : ℕ, (f.map φ - g₀.map φ * h₀.map φ).coeff k ∈
      Ideal.span {resultant (g₀.map φ) (h₀.map φ) n m ^ 2} * J := by
    intro k
    rw [hmap, coeff_map, resultant_map_map]
    exact hideal (Ideal.mem_map_of_mem φ (herror k))
  simpa only [resultant_map_map] using
    exists_factorization_of_resultant_sq_of_natDegree_le J
      (natDegree_map_le.trans hg₀) (natDegree_map_le.trans hh₀) hdegree' herror'


end Polynomial

/-- A square-resultant error admits a unique ordered factorization over a Henselian target
among pairs whose corrections satisfy the stated strict-degree bounds and whose correction
coefficients lie in `Ideal.span {φ (g₀.resultant h₀ n m)} * J`, provided the mapped resultant
is a non-zero-divisor. The supplied bounds and resultant indices are retained even when the
coefficient map lowers degrees. -/
theorem Polynomial.existsUnique_factorization_of_resultant_sq_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (J : Ideal S) [HenselianRing S J]
    (hIJ : Ideal.map φ I ≤ J) {n m : ℕ} {f g₀ h₀ : Polynomial R}
    (hg₀ : g₀.natDegree ≤ n) (hh₀ : h₀.natDegree ≤ m)
    (hd : φ (g₀.resultant h₀ n m) ∈ nonZeroDivisors S)
    (hdegree : (f - g₀ * h₀).degree <
      (n : WithBot ℕ) + (m : WithBot ℕ))
    (herror : ∀ k : ℕ, (f - g₀ * h₀).coeff k ∈
      Ideal.span {(g₀.resultant h₀ n m) ^ 2} * I) :
    ∃! p : Polynomial S × Polynomial S,
      f.map φ = p.1 * p.2 ∧
      (p.1 - g₀.map φ).degree < (n : WithBot ℕ) ∧
      (p.2 - h₀.map φ).degree < (m : WithBot ℕ) ∧
      ∀ k : ℕ,
        (p.1 - g₀.map φ).coeff k ∈
          Ideal.span {φ (g₀.resultant h₀ n m)} * J ∧
        (p.2 - h₀.map φ).coeff k ∈
          Ideal.span {φ (g₀.resultant h₀ n m)} * J := by
  obtain ⟨G, H, hprod, hG, hH, hcoeff⟩ :=
    Polynomial.exists_factorization_of_resultant_sq_map φ I J hIJ hg₀ hh₀ hdegree herror
  refine ⟨(G, H), ⟨hprod, hG, hH, hcoeff⟩, ?_⟩
  rintro ⟨G', H'⟩ ⟨hprod', hG', hH', hcoeff'⟩
  have hresultant :
      (g₀.map φ).resultant (h₀.map φ) n m = φ (g₀.resultant h₀ n m) :=
    Polynomial.resultant_map_map g₀ h₀ n m φ
  have hd' : (g₀.map φ).resultant (h₀.map φ) n m ∈ nonZeroDivisors S := by
    simpa only [hresultant] using hd
  obtain ⟨hG_eq, hH_eq⟩ :=
    Polynomial.eq_factors_of_regular_resultant J
      (HenselianRing.jac (R := S) (I := J))
      ((Polynomial.natDegree_map_le (f := φ) (p := g₀)).trans hg₀)
      ((Polynomial.natDegree_map_le (f := φ) (p := h₀)).trans hh₀)
      hd' (hprod'.symm.trans hprod) hG' hH' hG hH
      (by simpa only [hresultant] using hcoeff')
      (by simpa only [hresultant] using hcoeff)
  exact Prod.ext hG_eq hH_eq
