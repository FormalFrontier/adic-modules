/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import AdicModules.LinearAlgebra.Matrix.DeterminantPerturbation
public import AdicModules.MvPolynomial.Evaluation
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Jacobian perturbations on determinant-ideal neighborhoods

For a polynomial map over a commutative semiring, evaluate its partial derivatives through a
coefficient homomorphism into a commutative ring. Rows of the resulting matrix correspond to
outputs and columns to variables. If the coordinates of two evaluation points differ by an
element of the determinant ideal times a Jacobson ideal, the two Jacobian determinants are
associated and their linear maps have equal kernels and ranges.

The coefficient semiring and target ring have independent universes, and the evaluation points need
not lie in the image of the coefficient homomorphism. No regularity of the determinant is
required. The index type may be empty.

On the same neighborhoods, equality of evaluation vectors is equivalent to vanishing of the
Jacobian at the center on the difference of the points. Consequently, injectivity is equivalent
to triviality of its kernel on vectors with coordinates in the neighborhood ideal.
Regularity of the determinant suffices for injectivity, so any supplied solution for a prescribed
target vector in such a neighborhood is unique there.

The proofs combine Mathlib's `MvPolynomial.eval₂Hom_congr` and `MvPolynomial.map_eval₂Hom`
with the determinant-perturbation results in
`AdicModules.LinearAlgebra.Matrix.DeterminantPerturbation`. The fiber and injectivity results
also use the evaluation-difference theorem in `AdicModules.MvPolynomial.Evaluation`.
The regular-determinant corollaries use Mathlib's matrix zero-kernel theorem.
-/

@[expose] public section

noncomputable section

universe u v w

namespace MvPolynomial

/-- Evaluating a polynomial at points congruent modulo an ideal gives congruent values.
The proof reduces to `eval₂Hom_congr` by evaluating in the quotient ring. -/
theorem eval₂Hom_sub_mem_of_forall_sub_mem
    {C : Type u} {R : Type v} {σ : Type w} [CommSemiring C] [CommRing R]
    (φ : C →+* R) (a b : σ → R) (K : Ideal R)
    (hba : ∀ i, b i - a i ∈ K) (P : MvPolynomial σ C) :
    eval₂Hom φ b P - eval₂Hom φ a P ∈ K := by
  have hpoints :
      (fun i => Ideal.Quotient.mk K (b i)) =
        (fun i => Ideal.Quotient.mk K (a i)) :=
    funext fun i => Ideal.Quotient.eq.mpr (hba i)
  apply (Ideal.Quotient.eq).mp
  rw [map_eval₂Hom, map_eval₂Hom]
  exact eval₂Hom_congr rfl hpoints rfl

/-- At the zero ideal, evaluation congruence recovers `eval₂Hom_congr` with the
coefficient homomorphism and polynomial fixed, for commutative ring targets. -/
private theorem eval₂Hom_eq_of_forall_sub_mem_bot
    {C : Type u} {R : Type v} {σ : Type w} [CommSemiring C] [CommRing R]
    (φ : C →+* R) (a b : σ → R)
    (hba : ∀ i, b i - a i ∈ (⊥ : Ideal R)) (P : MvPolynomial σ C) :
    eval₂Hom φ b P = eval₂Hom φ a P := by
  simpa [sub_eq_zero] using eval₂Hom_sub_mem_of_forall_sub_mem φ a b (⊥ : Ideal R) hba P

/-- A determinant-scaled Jacobson neighborhood preserves the associated class of the
Jacobian determinant, by `Matrix.associated_det_of_sub_mem_span_mul`. -/
theorem associated_det_jacobian_of_sub_mem_span_mul
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R] [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a b : σ → R) (I : Ideal R)
    (hI : I ≤ (⊥ : Ideal R).jacobson)
    (hba : ∀ i, b i - a i ∈
      Ideal.span {Matrix.det (Matrix.of (fun r s => eval₂Hom φ a (pderiv s (F r))))} * I) :
    Associated
      (Matrix.det (Matrix.of (fun r s => eval₂Hom φ b (pderiv s (F r)))))
      (Matrix.det (Matrix.of (fun r s => eval₂Hom φ a (pderiv s (F r))))) := by
  exact Matrix.associated_det_of_sub_mem_span_mul
    (Matrix.of (fun r s => eval₂Hom φ b (pderiv s (F r))))
    (Matrix.of (fun r s => eval₂Hom φ a (pderiv s (F r)))) I hI
    (fun r s => by
      simpa only [Matrix.of_apply] using
        eval₂Hom_sub_mem_of_forall_sub_mem φ a b _ hba (pderiv s (F r)))

/-- A determinant-scaled Jacobson neighborhood preserves the kernel of the Jacobian's
linear map, by `Matrix.ker_mulVecLin_eq_of_sub_mem_span_mul`. -/
theorem ker_jacobian_mulVecLin_eq_of_sub_mem_span_mul
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R] [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a b : σ → R) (I : Ideal R)
    (hI : I ≤ (⊥ : Ideal R).jacobson)
    (hba : ∀ i, b i - a i ∈
      Ideal.span {Matrix.det (Matrix.of (fun r s => eval₂Hom φ a (pderiv s (F r))))} * I) :
    LinearMap.ker
        (Matrix.mulVecLin (Matrix.of (fun r s => eval₂Hom φ b (pderiv s (F r))))) =
      LinearMap.ker
        (Matrix.mulVecLin (Matrix.of (fun r s => eval₂Hom φ a (pderiv s (F r))))) := by
  exact Matrix.ker_mulVecLin_eq_of_sub_mem_span_mul
    (Matrix.of (fun r s => eval₂Hom φ a (pderiv s (F r))))
    (Matrix.of (fun r s => eval₂Hom φ b (pderiv s (F r)))) I hI
    (fun r s => by
      simpa only [Matrix.of_apply] using
        eval₂Hom_sub_mem_of_forall_sub_mem φ a b _ hba (pderiv s (F r)))

/-- A determinant-scaled Jacobson neighborhood preserves the range of the Jacobian's
linear map, by `Matrix.range_mulVecLin_eq_of_sub_mem_span_mul`. -/
theorem range_jacobian_mulVecLin_eq_of_sub_mem_span_mul
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R] [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a b : σ → R) (I : Ideal R)
    (hI : I ≤ (⊥ : Ideal R).jacobson)
    (hba : ∀ i, b i - a i ∈
      Ideal.span {Matrix.det (Matrix.of (fun r s => eval₂Hom φ a (pderiv s (F r))))} * I) :
    LinearMap.range
        (Matrix.mulVecLin (Matrix.of (fun r s => eval₂Hom φ b (pderiv s (F r))))) =
      LinearMap.range
        (Matrix.mulVecLin (Matrix.of (fun r s => eval₂Hom φ a (pderiv s (F r))))) := by
  exact Matrix.range_mulVecLin_eq_of_sub_mem_span_mul
    (Matrix.of (fun r s => eval₂Hom φ a (pderiv s (F r))))
    (Matrix.of (fun r s => eval₂Hom φ b (pderiv s (F r)))) I hI
    (fun r s => by
      simpa only [Matrix.of_apply] using
        eval₂Hom_sub_mem_of_forall_sub_mem φ a b _ hba (pderiv s (F r)))

/-- On a determinant-scaled Jacobson neighborhood, two points have the same evaluation vector
exactly when the Jacobian matrix at the center kills their difference. This combines
`exists_eval₂_sub_eq_mulVec_of_sub_mem_span_mul` with
`Matrix.ker_mulVecLin_eq_of_sub_mem_span_mul`. -/
theorem eval₂_eq_iff_mulVec_sub_eq_zero
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R] [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) (I : Ideal R)
    (hI : I ≤ (⊥ : Ideal R).jacobson) :
    let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
    let d : R := A.det
    ∀ b c : σ → R,
      (∀ i, b i - a i ∈ Ideal.span {d} * I) →
      (∀ i, c i - a i ∈ Ideal.span {d} * I) →
      ((fun i => (F i).eval₂ φ b) = (fun i => (F i).eval₂ φ c) ↔
        A.mulVec (fun i => b i - c i) = 0) := by
  dsimp only
  intro b c hb hc
  let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
  obtain ⟨E, hE, hsec⟩ :=
    exists_eval₂_sub_eq_mulVec_of_sub_mem_span_mul φ F a b c A.det I hb hc
  let Q : Matrix σ σ R := A + A.det • E
  have hQA : ∀ i j, Q i j - A i j ∈ Ideal.span {A.det} * I := by
    intro i j
    change A i j + A.det * E i j - A i j ∈ _
    simpa only [add_sub_cancel_left] using
      Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton A.det)) (hE i j)
  have hker := Matrix.ker_mulVecLin_eq_of_sub_mem_span_mul A Q I hI hQA
  have hzero : Q.mulVec (fun i => b i - c i) = 0 ↔
      A.mulVec (fun i => b i - c i) = 0 := by
    simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using
      (SetLike.ext_iff.mp hker (fun i => b i - c i))
  calc
    (fun i => (F i).eval₂ φ b) = (fun i => (F i).eval₂ φ c) ↔
        (fun i => (F i).eval₂ φ b - (F i).eval₂ φ c) = 0 := sub_eq_zero.symm
    _ ↔ Q.mulVec (fun i => b i - c i) = 0 := by rw [hsec]
    _ ↔ A.mulVec (fun i => b i - c i) = 0 := hzero

/-- Translation by a point in a prescribed polynomial fiber bijects the kernel of the
Jacobian at the center, restricted to the determinant-scaled neighborhood ideal, with the
entire fiber in that neighborhood. No regularity of the determinant is required. -/
theorem bijOn_add_mulVec_eq_zero_eval₂
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R] [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) (I : Ideal R)
    (t : σ → R) (hI : I ≤ (⊥ : Ideal R).jacobson) :
    let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
    let d : R := A.det
    let J : Ideal R := Ideal.span {d} * I
    ∀ b : σ → R,
      (∀ i, b i - a i ∈ J) →
      (fun i => (F i).eval₂ φ b) = t →
      Set.BijOn (fun z : σ → R => b + z)
        {z | (∀ i, z i ∈ J) ∧ A.mulVec z = 0}
        {c | (∀ i, c i - a i ∈ J) ∧ (fun i => (F i).eval₂ φ c) = t} := by
  let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
  let J : Ideal R := Ideal.span {A.det} * I
  change ∀ b : σ → R, (∀ i, b i - a i ∈ J) →
    (fun i => (F i).eval₂ φ b) = t →
    Set.BijOn (fun z : σ → R => b + z)
      {z | (∀ i, z i ∈ J) ∧ A.mulVec z = 0}
      {c | (∀ i, c i - a i ∈ J) ∧ (fun i => (F i).eval₂ φ c) = t}
  intro b hb ht
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hbz : ∀ i, (b + z) i - a i ∈ J := by
      intro i
      change b i + z i - a i ∈ J
      rw [add_sub_right_comm]
      exact J.add_mem (hb i) (hz.1 i)
    refine ⟨hbz, ?_⟩
    have heval : (fun i => (F i).eval₂ φ (b + z)) = (fun i => (F i).eval₂ φ b) := by
      apply (eval₂_eq_iff_mulVec_sub_eq_zero φ F a I hI (b + z) b hbz hb).mpr
      simpa only [Pi.add_apply, add_sub_cancel_left] using hz.2
    exact heval.trans ht
  · intro z _ z' _ hzz
    exact add_left_cancel hzz
  · intro c hc
    refine ⟨c - b, ⟨?_, ?_⟩, ?_⟩
    · intro i
      have hi := J.sub_mem (hc.1 i) (hb i)
      rwa [sub_sub_eq_add_sub, sub_add_cancel] at hi
    · exact (eval₂_eq_iff_mulVec_sub_eq_zero φ F a I hI c b hc.1 hb).mp
        (hc.2.trans ht.symm)
    · exact (add_comm b (c - b)).trans (sub_add_cancel c b)

/-- A polynomial map is injective on a determinant-scaled Jacobson neighborhood exactly
when the Jacobian at the center has trivial kernel on vectors with coordinates in that
neighborhood ideal. No regularity assumption on its determinant is needed. -/
theorem injOn_eval₂_iff_mulVec_eq_zero
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R] [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) (I : Ideal R)
    (hI : I ≤ (⊥ : Ideal R).jacobson) :
    let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
    let d : R := A.det
    let J : Ideal R := Ideal.span {d} * I
    Set.InjOn (fun b i => (F i).eval₂ φ b) {b | ∀ i, b i - a i ∈ J} ↔
      ∀ z : σ → R, (∀ i, z i ∈ J) → A.mulVec z = 0 → z = 0 := by
  let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
  let J : Ideal R := Ideal.span {A.det} * I
  change Set.InjOn (fun b i => (F i).eval₂ φ b) {b | ∀ i, b i - a i ∈ J} ↔
    ∀ z : σ → R, (∀ i, z i ∈ J) → A.mulVec z = 0 → z = 0
  constructor
  · intro hinj z hz hAz
    have hb : ∀ i, (a + z) i - a i ∈ J := by
      intro i
      simpa only [Pi.add_apply, add_sub_cancel_left] using hz i
    have ha : ∀ i, a i - a i ∈ J := by
      intro i
      simpa only [sub_self] using J.zero_mem
    have heval : (fun i => (F i).eval₂ φ (a + z)) = (fun i => (F i).eval₂ φ a) := by
      apply (eval₂_eq_iff_mulVec_sub_eq_zero φ F a I hI (a + z) a hb ha).mpr
      simpa only [Pi.add_apply, add_sub_cancel_left] using hAz
    have hpoints : a + z = a := hinj hb ha heval
    simpa only [add_sub_cancel_left, sub_self] using
      congrArg (fun b : σ → R => b - a) hpoints
  · intro hker b hb c hc heval
    have hsub : ∀ i, b i - c i ∈ J := by
      intro i
      have hi := J.sub_mem (hb i) (hc i)
      rwa [sub_sub_eq_add_sub, sub_add_cancel] at hi
    have hAz : A.mulVec (fun i => b i - c i) = 0 :=
      (eval₂_eq_iff_mulVec_sub_eq_zero φ F a I hI b c hb hc).mp heval
    exact sub_eq_zero.mp (hker _ hsub hAz)

/-- A prescribed fiber in a determinant-scaled Jacobson neighborhood consists of exactly
one point if and only if it is nonempty and the Jacobian at the center has trivial kernel
on vectors with coordinates in the neighborhood ideal. No regularity of the determinant
is required. -/
theorem existsUnique_eval₂_eq_iff_exists_and_mulVec_eq_zero
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R] [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) (I : Ideal R)
    (t : σ → R) (hI : I ≤ (⊥ : Ideal R).jacobson) :
    let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
    let d : R := A.det
    let J : Ideal R := Ideal.span {d} * I
    (∃! b : σ → R, (∀ i, b i - a i ∈ J) ∧ (fun i => (F i).eval₂ φ b) = t) ↔
      (∃ b : σ → R, (∀ i, b i - a i ∈ J) ∧ (fun i => (F i).eval₂ φ b) = t) ∧
        ∀ z : σ → R, (∀ i, z i ∈ J) → A.mulVec z = 0 → z = 0 := by
  let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
  let J : Ideal R := Ideal.span {A.det} * I
  change (∃! b : σ → R, (∀ i, b i - a i ∈ J) ∧
      (fun i => (F i).eval₂ φ b) = t) ↔
    (∃ b : σ → R, (∀ i, b i - a i ∈ J) ∧ (fun i => (F i).eval₂ φ b) = t) ∧
      ∀ z : σ → R, (∀ i, z i ∈ J) → A.mulVec z = 0 → z = 0
  constructor
  · rintro ⟨b, hb, huniq⟩
    refine ⟨⟨b, hb⟩, ?_⟩
    intro z hz hAz
    have hbij := bijOn_add_mulVec_eq_zero_eval₂ φ F a I t hI b hb.1 hb.2
    have hpoints : b + z = b := huniq (b + z) (hbij.mapsTo ⟨hz, hAz⟩)
    simpa only [add_sub_cancel_left, sub_self] using
      congrArg (fun c : σ → R => c - b) hpoints
  · rintro ⟨⟨b, hb⟩, hker⟩
    refine ⟨b, hb, ?_⟩
    intro c hc
    exact (injOn_eval₂_iff_mulVec_eq_zero φ F a I hI).mpr hker
      hc.1 hb.1 (hc.2.trans hb.2.symm)

/-- Regularity of the evaluated Jacobian determinant at the center makes a polynomial map
injective on the corresponding determinant-scaled Jacobson neighborhood. -/
theorem injOn_eval₂_of_isRegular_det
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R] [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) (I : Ideal R)
    (hI : I ≤ (⊥ : Ideal R).jacobson) :
    let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
    let d : R := A.det
    let J : Ideal R := Ideal.span {d} * I
    IsRegular d →
      Set.InjOn (fun b i => (F i).eval₂ φ b) {b | ∀ i, b i - a i ∈ J} := by
  dsimp only
  intro hdet
  apply (injOn_eval₂_iff_mulVec_eq_zero φ F a I hI).mpr
  intro z _ hAz
  exact Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero
    hdet.mem_nonZeroDivisors hAz

/-- An existing solution in a determinant-scaled Jacobson neighborhood is the unique solution
there for its prescribed target vector if the evaluated Jacobian determinant at the center is
regular. The solution is supplied by the existence hypothesis. -/
theorem existsUnique_eval₂_eq_of_exists_of_isRegular_det
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R] [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) (I : Ideal R)
    (t : σ → R) (hI : I ≤ (⊥ : Ideal R).jacobson) :
    let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
    let d : R := A.det
    let J : Ideal R := Ideal.span {d} * I
    IsRegular d →
      (∃ b : σ → R, (∀ i, b i - a i ∈ J) ∧ (fun i => (F i).eval₂ φ b) = t) →
      ∃! b : σ → R, (∀ i, b i - a i ∈ J) ∧ (fun i => (F i).eval₂ φ b) = t := by
  dsimp only
  intro hdet hex
  apply (existsUnique_eval₂_eq_iff_exists_and_mulVec_eq_zero φ F a I t hI).mpr
  refine ⟨hex, ?_⟩
  intro z _ hAz
  exact Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero
    hdet.mem_nonZeroDivisors hAz

/-- Evaluation on a determinant-ideal neighborhood filtered by an arbitrary set of linearized
values is injective exactly when the filtered source is empty or the Jacobian has no nonzero
kernel vector with coordinates in the neighborhood ideal. The filter concerns `A.mulVec (b - a)`,
not the nonlinear evaluation displacement, and need not contain zero or be closed under addition.
Only the Jacobson inclusion is required; no Henselian or determinant-regularity assumption is used.
-/
theorem injOn_eval₂_det_neighborhood_inter_preimage_iff
    {C : Type*} {R : Type*} {σ : Type*}
    [CommSemiring C] [CommRing R] [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) (I : Ideal R)
    (hI : I ≤ (⊥ : Ideal R).jacobson) (S : Set (σ → R)) :
    let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
    let d : R := A.det
    let J : Ideal R := Ideal.span {d} * I
    Set.InjOn (fun b i => (F i).eval₂ φ b)
        {b | (∀ i, b i - a i ∈ J) ∧ A.mulVec (b - a) ∈ S} ↔
      {b | (∀ i, b i - a i ∈ J) ∧ A.mulVec (b - a) ∈ S} = ∅ ∨
        ∀ δ : σ → R, (∀ i, δ i ∈ J) → A.mulVec δ = 0 → δ = 0 := by
  classical
  let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
  let d : R := A.det
  let J : Ideal R := Ideal.span {d} * I
  let B : Set (σ → R) := {b | (∀ i, b i - a i ∈ J) ∧ A.mulVec (b - a) ∈ S}
  change Set.InjOn (fun b i => (F i).eval₂ φ b) B ↔
    B = ∅ ∨ ∀ δ : σ → R, (∀ i, δ i ∈ J) → A.mulVec δ = 0 → δ = 0
  constructor
  · intro hinj
    by_cases hB : B = ∅
    · exact Or.inl hB
    · right
      obtain ⟨b, hb⟩ : B.Nonempty := Set.nonempty_iff_ne_empty.mpr hB
      intro δ hδ hker
      have hshift : b + δ - a = (b - a) + δ := by
        simpa only [sub_eq_add_neg] using (add_right_comm b δ (-a))
      have hbδbox : ∀ i, (b + δ) i - a i ∈ J := by
        intro i
        change (b + δ - a) i ∈ J
        rw [congrFun hshift i]
        exact J.add_mem (hb.1 i) (hδ i)
      have hbδ : b + δ ∈ B := by
        refine ⟨hbδbox, ?_⟩
        rw [hshift, Matrix.mulVec_add, hker, add_zero]
        exact hb.2
      have hdiff : (fun i => (b + δ) i - b i) = δ := by
        change b + δ - b = δ
        simpa only [sub_eq_add_neg, add_neg_cancel, zero_add] using
          (add_right_comm b δ (-b))
      have heval : (fun i => (F i).eval₂ φ (b + δ)) =
          (fun i => (F i).eval₂ φ b) := by
        apply (eval₂_eq_iff_mulVec_sub_eq_zero φ F a I hI
          (b + δ) b hbδbox hb.1).mpr
        change A.mulVec (fun i => (b + δ) i - b i) = 0
        rw [hdiff]
        exact hker
      have hpoint : b + δ = b := hinj hbδ hb heval
      exact add_left_cancel (hpoint.trans (add_zero b).symm)
  · rintro (hB | hker)
    · rw [hB]
      exact Set.injOn_empty _
    · have hwhole : Set.InjOn (fun b i => (F i).eval₂ φ b)
          {b | ∀ i, b i - a i ∈ J} :=
        (injOn_eval₂_iff_mulVec_eq_zero φ F a I hI).mpr hker
      exact Set.InjOn.mono (fun b hb => hb.1) hwhole

/-- If a linear-target filter contains zero, the center belongs to the filtered determinant
neighborhood, so injectivity is equivalent to the small-kernel condition without an empty-source
alternative. In particular this applies to every submodule of the target, with no lower bound
on that submodule and no Henselian assumption. -/
theorem injOn_eval₂_det_neighborhood_inter_preimage_iff_of_zero_mem
    {C : Type*} {R : Type*} {σ : Type*}
    [CommSemiring C] [CommRing R] [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) (I : Ideal R)
    (hI : I ≤ (⊥ : Ideal R).jacobson) (S : Set (σ → R)) (hS : (0 : σ → R) ∈ S) :
    let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
    let d : R := A.det
    let J : Ideal R := Ideal.span {d} * I
    Set.InjOn (fun b i => (F i).eval₂ φ b)
        {b | (∀ i, b i - a i ∈ J) ∧ A.mulVec (b - a) ∈ S} ↔
      ∀ δ : σ → R, (∀ i, δ i ∈ J) → A.mulVec δ = 0 → δ = 0 := by
  classical
  let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
  let d : R := A.det
  let J : Ideal R := Ideal.span {d} * I
  let B : Set (σ → R) := {b | (∀ i, b i - a i ∈ J) ∧ A.mulVec (b - a) ∈ S}
  change Set.InjOn (fun b i => (F i).eval₂ φ b) B ↔
    ∀ δ : σ → R, (∀ i, δ i ∈ J) → A.mulVec δ = 0 → δ = 0
  have ha : a ∈ B := by
    refine ⟨?_, ?_⟩
    · intro i
      simpa only [sub_self] using J.zero_mem
    · simpa only [sub_self, Matrix.mulVec_zero] using hS
  have h := injOn_eval₂_det_neighborhood_inter_preimage_iff φ F a I hI S
  change Set.InjOn (fun b i => (F i).eval₂ φ b) B ↔
    B = ∅ ∨ ∀ δ : σ → R, (∀ i, δ i ∈ J) → A.mulVec δ = 0 → δ = 0 at h
  constructor
  · intro hinj
    rcases h.mp hinj with hempty | hker
    · exact False.elim
        (Eq.mp (congrArg (fun T : Set (σ → R) => a ∈ T) hempty) ha)
    · exact hker
  · intro hker
    exact h.mpr (Or.inr hker)

open scoped Classical in
/-- Two points in the determinant-scaled ideal neighborhood of a center have equal polynomial
values if their difference lies in the kernel of the Jacobian at the center. The ideal is arbitrary;
no Jacobson-smallness assumption is needed. -/
theorem eval₂_eq_of_mulVec_sub_eq_zero
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R] [Fintype σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) (I : Ideal R) :
    let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
    let d : R := A.det
    ∀ b c : σ → R,
      (∀ i, b i - a i ∈ Ideal.span {d} * I) →
      (∀ i, c i - a i ∈ Ideal.span {d} * I) →
      A.mulVec (fun i => b i - c i) = 0 →
      (fun i => (F i).eval₂ φ b) = (fun i => (F i).eval₂ φ c) := by
  dsimp only
  intro b c hb hc hbc
  let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
  let κ : σ → R := fun i => b i - c i
  change A.mulVec κ = 0 at hbc
  obtain ⟨E, _, hE⟩ :=
    exists_eval₂_sub_eq_mulVec_of_sub_mem_span_mul φ F a b c A.det I hb hc
  change (fun j => (F j).eval₂ φ b - (F j).eval₂ φ c) =
    (A + A.det • E).mulVec κ at hE
  have hdet : A.det • κ = 0 := by
    calc
      A.det • κ = (A.adjugate * A).mulVec κ := by
        rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = A.adjugate.mulVec (A.mulVec κ) := (Matrix.mulVec_mulVec κ A.adjugate A).symm
      _ = 0 := by rw [hbc, Matrix.mulVec_zero]
  have hsec : (A + A.det • E).mulVec κ = 0 := by
    calc
      (A + A.det • E).mulVec κ = A.mulVec κ + E.mulVec (A.det • κ) := by
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul]
      _ = 0 := by rw [hbc, hdet, Matrix.mulVec_zero, add_zero]
  funext j
  exact sub_eq_zero.mp (congrFun (hE.trans hsec) j)

open scoped Classical in
/-- Polynomial evaluation differences on a determinant-ideal box lie in the Jacobian image of
that same box. The ideal-preserving witness combines
`exists_eval₂_sub_eq_mulVec_of_sub_mem_span_mul` with Mathlib's adjugate identity
`Matrix.mul_adjugate`. -/
theorem exists_eval₂_sub_eq_jacobian_mulVec_of_sub_mem_span_det_mul
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R] [Fintype σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) (I : Ideal R) :
    let A : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
    let d : R := A.det
    let J : Ideal R := Ideal.span {d} * I
    ∀ b : σ → R,
      (∀ i, b i - a i ∈ J) →
      ∃ η : σ → R,
        (∀ i, η i ∈ J) ∧
        (fun i => (F i).eval₂ φ b - (F i).eval₂ φ a) = A.mulVec η := by
  intro A d J b hb
  have ha : ∀ i, a i - a i ∈ J := by
    intro i
    simpa only [sub_self] using J.zero_mem
  obtain ⟨Q, _, hQ⟩ :=
    exists_eval₂_sub_eq_mulVec_of_sub_mem_span_mul φ F a b a d I hb ha
  let κ : σ → R := fun i => b i - a i
  have mulVec_mem (M : Matrix σ σ R) (x : σ → R)
      (hx : ∀ i, x i ∈ J) : ∀ i, M.mulVec x i ∈ J := by
    intro i
    change (∑ j, M i j * x j) ∈ J
    exact Submodule.sum_mem J (fun j _ => J.mul_mem_left (M i j) (hx j))
  refine ⟨κ + A.adjugate.mulVec (Q.mulVec κ), ?_, ?_⟩
  · intro i
    exact J.add_mem (hb i)
      (mulVec_mem A.adjugate (Q.mulVec κ) (mulVec_mem Q κ hb) i)
  · calc
      (fun i => (F i).eval₂ φ b - (F i).eval₂ φ a) =
          (A + d • Q).mulVec κ := hQ
      _ = A.mulVec (κ + A.adjugate.mulVec (Q.mulVec κ)) := by
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add,
          Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
          Matrix.one_mulVec]

end MvPolynomial
