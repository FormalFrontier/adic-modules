/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import AdicModules.MvPolynomial.JacobianPerturbation
public import AdicModules.RingTheory.Ideal.Localization

/-!
# Jacobian injectivity under one-add regularity

Evaluation is injective on the box `(Ideal.span {d}) * I` when the evaluated Jacobian
determinant `d` and every `1 + x` with `x ∈ I` are regular.
The coefficient semiring is independent of the target ring.

The proof localizes the target at one plus the ideal, applies the Jacobson-ideal theorem,
and descends through the injective localization map.

## References

* `MvPolynomial.injOn_eval₂_of_isRegular_det` for the Jacobson-ideal case.
* Mathlib’s localization and ideal APIs.
-/

@[expose] public section

universe u v w

namespace MvPolynomial

/-- Injectivity on the Jacobian-scaled ideal box when every element of one plus the ideal
is regular. -/
theorem injOn_eval₂_of_isRegular_det_of_isRegular_one_add
    {C : Type u} {R : Type v} {σ : Type w}
    [CommSemiring C] [CommRing R] [Fintype σ] [DecidableEq σ]
    (φ : C →+* R) (F : σ → MvPolynomial σ C) (a : σ → R) (I : Ideal R)
    (hI : ∀ x : R, x ∈ I → IsRegular (1 + x)) :
    let M : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
    let d : R := M.det
    let J : Ideal R := Ideal.span {d} * I
    IsRegular d →
      Set.InjOn (fun b i => (F i).eval₂ φ b) {b | ∀ i, b i - a i ∈ J} := by
  classical
  let M : Matrix σ σ R := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φ a)
  let d : R := M.det
  let J : Ideal R := Ideal.span {d} * I
  change IsRegular d →
    Set.InjOn (fun b i => (F i).eval₂ φ b) {b | ∀ i, b i - a i ∈ J}
  intro hd
  let T : Submonoid R := (⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)
  let A := Localization T
  let f : R →+* A := algebraMap R A
  have hT (s : T) : IsRegular (s : R) := by
    have hs : Ideal.Quotient.mk I (s : R) = 1 := s.property
    have hsI : (s : R) - 1 ∈ I :=
      Ideal.Quotient.eq.mp (by simpa only [map_one] using hs)
    simpa only [add_comm (1 : R) ((s : R) - 1), sub_add_cancel] using
      hI ((s : R) - 1) hsI
  have hf : Function.Injective f :=
    (IsLocalization.injective_iff_isRegular (S := A) T).mpr hT
  have hreg : IsRegular (f d) :=
    isRegular_iff_mem_nonZeroDivisors.mpr
      ((IsLocalization.nonZeroDivisors_le_comap T A)
        (isRegular_iff_mem_nonZeroDivisors.mp hd))
  have hJac : Ideal.map f I ≤ (⊥ : Ideal A).jacobson :=
    Ideal.map_le_jacobson_of_isLocalization (A := A) I
  let φA : C →+* A := f.comp φ
  let aA : σ → A := fun i => f (a i)
  let IA : Ideal A := Ideal.map f I
  let MA : Matrix σ σ A := Matrix.of (fun i j => (pderiv j (F i)).eval₂ φA aA)
  let dA : A := MA.det
  let JA : Ideal A := Ideal.span {dA} * IA
  have hEval (b : σ → R) (P : MvPolynomial σ C) :
      P.eval₂ φA (fun i => f (b i)) = f (P.eval₂ φ b) := by
    exact (MvPolynomial.eval₂_comp_left f φ b P).symm
  have hM : MA = f.mapMatrix M := by
    funext i j
    exact hEval a (pderiv j (F i))
  have hdA : dA = f d := by
    change MA.det = f M.det
    rw [hM]
    exact (RingHom.map_det f M).symm
  have hregA : IsRegular dA := by
    rw [hdA]
    exact hreg
  have h_image : I ≤ Ideal.comap f IA :=
    Ideal.map_le_iff_le_comap.mp le_rfl
  have hbox (b : σ → R) (hb : ∀ i, b i - a i ∈ J) :
      ∀ i, f (b i) - aA i ∈ JA := by
    intro i
    obtain ⟨z, hz, heq⟩ := Ideal.mem_span_singleton_mul.mp (hb i)
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨f z, h_image hz, ?_⟩
    change dA * f z = f (b i) - f (a i)
    rw [hdA, ← map_mul, heq, map_sub]
  have hJP := MvPolynomial.injOn_eval₂_of_isRegular_det φA F aA IA hJac hregA
  intro b hb c hc hbc
  have hbcA :
      (fun i => (F i).eval₂ φA (fun j => f (b j))) =
      (fun i => (F i).eval₂ φA (fun j => f (c j))) := by
    funext i
    simpa only [hEval] using congrArg f (congrFun hbc i)
  have hpoints : (fun i => f (b i)) = (fun i => f (c i)) :=
    hJP (hbox b hb) (hbox c hc) hbcA
  funext i
  exact hf (congrFun hpoints i)

end MvPolynomial
