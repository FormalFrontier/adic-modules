/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.Idempotents

import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Ring.ULift
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.Ring

/-!
# Henselian pairs and finite-algebra idempotents

The finite-algebra criterion relates Henselianity of a commutative ring and an ideal to
unique lifting of idempotents through the quotient by the extended ideal in every given
module-finite commutative algebra. The lift is an element of the original algebra, with
its prescribed image under the quotient map.

The component calculations, due to Formal Frontier Agents, use a unit-valued linear
functional to detect a kernel and descend polynomial roots to the coefficient ring.

## References

- The Stacks project authors, *The Stacks project*, Lemma 15.11.6 (3),
  [Tag 09XI](https://stacks.math.columbia.edu/tag/09XI).
-/

public section

universe u v

namespace HenselianRing

/-- A linear functional whose value on the image of `1` is a unit detects the kernel. -/
private theorem injective_of_unit_linear_image
    {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
    (α : R →ₗ[R] E) (σ : E →ₗ[R] R) (hc : IsUnit (σ (α 1))) :
    Function.Injective α := by
  intro x y hxy
  have hz : α (x - y) = 0 := by
    rw [α.map_sub, hxy, sub_self]
  have hmul : σ (α 1) * (x - y) = 0 := by
    calc
      σ (α 1) * (x - y) = σ ((x - y) • α 1) := by
        rw [σ.map_smul, smul_eq_mul, mul_comm]
      _ = σ (α (x - y)) := by
        rw [← α.map_smul, smul_eq_mul, mul_one]
      _ = 0 := by rw [hz, σ.map_zero]
  have hzero : x - y = 0 := hc.mul_right_inj.mp (by
    simpa only [mul_zero] using hmul)
  exact sub_eq_zero.mp hzero

/-- A split surjection with kernel in an ideal of unit perturbations is injective. -/
private theorem injective_of_split_of_kernel_mem
    {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
    (I : Ideal R) (α : R →ₗ[R] E) (σ : E →ₗ[R] R)
    (hsplit : ∀ y, α (σ y) = y)
    (hker : ∀ r, α r = 0 → r ∈ I)
    (hunit : ∀ r ∈ I, IsUnit (1 - r)) : Function.Injective α := by
  have hmem : 1 - σ (α 1) ∈ I := hker _ (by
    rw [α.map_sub, hsplit, sub_self])
  have hc : IsUnit (σ (α 1)) := by
    simpa only [sub_sub_cancel] using hunit _ hmem
  exact injective_of_unit_linear_image α σ hc

/-- Equality after multiplication by one element is preserved by powers. -/
private theorem pow_mul_eq_of_mul_eq
    {B : Type v} [CommSemiring B] {x y e : B} (h : x * e = y * e) (n : ℕ) :
    x ^ n * e = y ^ n * e := by
  induction n with
  | zero => simp only [pow_zero, one_mul]
  | succ n ih =>
      calc
        x ^ (n + 1) * e = x ^ n * (x * e) := by rw [pow_succ, mul_assoc]
        _ = x ^ n * (y * e) := by rw [h]
        _ = y * (x ^ n * e) := mul_left_comm _ _ _
        _ = y * (y ^ n * e) := by rw [ih]
        _ = y ^ (n + 1) * e := by rw [pow_succ', mul_assoc]

/-- Polynomial evaluation agrees on a component where its two arguments agree. -/
private theorem eval_mul_eq_of_mul_eq
    {R : Type u} [CommSemiring R] {B : Type v} [CommSemiring B] [Algebra R B]
    (f : Polynomial R) {a : R} {t e : B}
    (h : algebraMap R B a * e = t * e) :
    algebraMap R B (f.eval a) * e = f.eval₂ (algebraMap R B) t * e := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add, map_add, Polynomial.eval₂_add, add_mul, hp, hq]
  | monomial n r =>
      simp only [Polynomial.eval_monomial, Polynomial.eval₂_monomial, map_mul, map_pow]
      simpa only [mul_assoc] using
        congrArg (fun z : B => algebraMap R B r * z) (pow_mul_eq_of_mul_eq h n)

/-- The residue of a scalar is detected by a component with residue identity. -/
private theorem quotient_eq_zero_of_component_eq_zero
    {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
    (I : Ideal R) (ρ : B →+* R ⧸ I) {e : B}
    (hρ : ∀ r, ρ (algebraMap R B r) = Ideal.Quotient.mk I r)
    (he : ρ e = 1) {r : R} (hr : algebraMap R B r * e = 0) :
    Ideal.Quotient.mk I r = 0 := by
  have h := congrArg ρ hr
  simpa only [map_mul, hρ, he, mul_one, map_zero] using h

/-- Equality on a component identifies residues in the original ideal quotient. -/
private theorem quotient_eq_of_component_eq
    {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
    (I : Ideal R) (ρ : B →+* R ⧸ I) {a a₀ : R} {t e : B}
    (hρ : ∀ r, ρ (algebraMap R B r) = Ideal.Quotient.mk I r)
    (he : ρ e = 1) (ht : ρ t = Ideal.Quotient.mk I a₀)
    (ha : algebraMap R B a * e = t * e) :
    Ideal.Quotient.mk I a = Ideal.Quotient.mk I a₀ := by
  have h := congrArg ρ ha
  simpa only [map_mul, hρ, he, ht, mul_one] using h

/-- A root on a faithful component descends to the coefficient ring. -/
private theorem eval_eq_zero_of_component
    {R : Type u} [CommSemiring R] {B : Type v} [CommSemiring B] [Algebra R B]
    (f : Polynomial R) {a : R} {t e : B}
    (hinj : Function.Injective (fun r : R => algebraMap R B r * e))
    (ht : f.eval₂ (algebraMap R B) t = 0)
    (ha : algebraMap R B a * e = t * e) : f.eval a = 0 := by
  apply hinj
  have hzero : algebraMap R B (f.eval a) * e = 0 := by
    rw [eval_mul_eq_of_mul_eq f ha, ht, zero_mul]
  simpa only [map_zero, zero_mul] using hzero

/-- Unique idempotent lifting descends along the canonical universe raise. -/
private theorem existsUnique_idempotent_of_maxUniverse
    {R : Type u} [CommRing R] (I : Ideal R)
    (h : ∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B]
      (e0 : B ⧸ I.map (algebraMap R B)), IsIdempotentElem e0 →
        ∃! e : B, IsIdempotentElem e ∧
          Ideal.Quotient.mk (I.map (algebraMap R B)) e = e0)
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A]
    (e0 : A ⧸ I.map (algebraMap R A)) (he0 : IsIdempotentElem e0) :
    ∃! e : A, IsIdempotentElem e ∧
      Ideal.Quotient.mk (I.map (algebraMap R A)) e = e0 := by
  let e : A ≃ₐ[R] ULift.{v} A := (ULift.algEquiv : ULift.{v} A ≃ₐ[R] A).symm
  letI finiteULift : Module.Finite R (ULift.{v} A) := Module.Finite.equiv e.toLinearEquiv
  let JA : Ideal A := I.map (algebraMap R A)
  let JU : Ideal (ULift.{v} A) := I.map (algebraMap R (ULift.{v} A))
  have hcomp : ((e : A ≃+* ULift.{v} A) : A →+* ULift.{v} A).comp
      (algebraMap R A) = algebraMap R (ULift.{v} A) := by
    apply RingHom.ext
    intro r
    exact e.commutes r
  have hJ : JU = JA.map ((e : A ≃+* ULift.{v} A) : A →+* ULift.{v} A) := by
    dsimp only [JA, JU]
    rw [Ideal.map_map, hcomp]
  let q : A ⧸ JA ≃+* (ULift.{v} A) ⧸ JU :=
    Ideal.quotientEquiv JA JU (e : A ≃+* ULift.{v} A) hJ
  have hraw (a : A) : q (Ideal.Quotient.mk JA a) = Ideal.Quotient.mk JU (e a) :=
    Ideal.quotientEquiv_mk JA JU (e : A ≃+* ULift.{v} A) hJ a
  obtain ⟨d, hd, huniq⟩ := h (ULift.{v} A) (q e0) (he0.map q)
  refine ⟨e.symm d, ⟨hd.1.map e.symm, ?_⟩, ?_⟩
  · apply q.injective
    calc
      q (Ideal.Quotient.mk JA (e.symm d)) =
          Ideal.Quotient.mk JU (e (e.symm d)) := hraw _
      _ = Ideal.Quotient.mk JU d :=
        congrArg (Ideal.Quotient.mk JU) (e.apply_symm_apply d)
      _ = q e0 := hd.2
  · intro c hc
    have hec : e c = d := huniq (e c) ⟨hc.1.map e, by
      rw [← hraw c]
      exact congrArg q hc.2⟩
    calc
      c = e.symm (e c) := (e.symm_apply_apply c).symm
      _ = e.symm d := congrArg e.symm hec

/-- The cyclic quotient test forces every ideal perturbation of one to be a unit. -/
private theorem isUnit_one_sub_mul_of_finite_idempotent_lifts
    {R : Type u} [CommRing R] (I : Ideal R)
    (h : ∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B]
      (e0 : B ⧸ I.map (algebraMap R B)), IsIdempotentElem e0 →
        ∃! e : B, IsIdempotentElem e ∧
          Ideal.Quotient.mk (I.map (algebraMap R B)) e = e0)
    {x : R} (hx : x ∈ I) (a : R) : IsUnit (1 - a * x) := by
  let K : Ideal R := Ideal.span ({1 - a * x} : Set R)
  letI finiteCyclic : Module.Finite R (R ⧸ K) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R K).toLinearMap (by
      intro z
      obtain ⟨r, hr⟩ := Ideal.Quotient.mkₐ_surjective R K z
      refine ⟨r, ?_⟩
      simpa only [AlgHom.toLinearMap_apply] using hr)
  let J : Ideal (R ⧸ K) := I.map (algebraMap R (R ⧸ K))
  have hs : Ideal.Quotient.mk K (1 - a * x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hone : (1 : R ⧸ K) =
      algebraMap R (R ⧸ K) a * algebraMap R (R ⧸ K) x := by
    have hmk : (1 : R ⧸ K) = Ideal.Quotient.mk K a * Ideal.Quotient.mk K x :=
      sub_eq_zero.mp (by simpa only [map_sub, map_one, map_mul] using hs)
    simpa only [Ideal.Quotient.algebraMap_eq] using hmk
  have hJtop : J = ⊤ := (Ideal.eq_top_iff_one J).mpr (by
    rw [hone]
    exact J.mul_mem_left _ (Ideal.mem_map_of_mem (algebraMap R (R ⧸ K)) hx))
  letI residueSubsingleton : Subsingleton ((R ⧸ K) ⧸ J) :=
    Ideal.Quotient.subsingleton_iff.mpr hJtop
  obtain ⟨d, _, huniq⟩ := existsUnique_idempotent_of_maxUniverse.{u, v} I h (R ⧸ K)
    (0 : (R ⧸ K) ⧸ J) (isIdempotentElem_iff.mpr (zero_mul _))
  have hz : (0 : R ⧸ K) = d := huniq 0
    ⟨isIdempotentElem_iff.mpr (zero_mul _), by simp only [map_zero]⟩
  have ho : (1 : R ⧸ K) = d := huniq 1
    ⟨IsIdempotentElem.one, Subsingleton.elim _ _⟩
  have h1K : (1 : R) ∈ K := Ideal.Quotient.eq_zero_iff_mem.mp (by
    simpa only [map_one] using ho.trans hz.symm)
  have hKtop : K = ⊤ := (Ideal.eq_top_iff_one K).mpr h1K
  exact Ideal.span_singleton_eq_top.mp hKtop

/-- Unique lifting in every finite algebra implies Jacobson containment in the base. -/
private theorem le_jacobson_of_finite_idempotent_lifts
    {R : Type u} [CommRing R] (I : Ideal R)
    (h : ∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B]
      (e0 : B ⧸ I.map (algebraMap R B)), IsIdempotentElem e0 →
        ∃! e : B, IsIdempotentElem e ∧
          Ideal.Quotient.mk (I.map (algebraMap R B)) e = e0) :
    I ≤ Ideal.jacobson (⊥ : Ideal R) := by
  intro x hx
  apply Ideal.mem_jacobson_bot.mpr
  intro y
  have hu := isUnit_one_sub_mul_of_finite_idempotent_lifts.{u, v} I h hx (-y)
  have hid : 1 - (-y) * x = x * y + 1 := by
    rw [neg_mul, sub_neg_eq_add, mul_comm y x, add_comm]
  simpa only [hid] using hu

/-- A quotient by an ideal in the Jacobson radical reflects units. -/
private theorem isUnit_of_quotient_isUnit_of_le_jacobson
    {R : Type u} [CommRing R] (I : Ideal R)
    (hJac : I ≤ Ideal.jacobson (⊥ : Ideal R)) {r : R}
    (hr : IsUnit (Ideal.Quotient.mk I r)) : IsUnit r := by
  letI : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I hJac
  exact (isUnit_map_iff (Ideal.Quotient.mk I) r).mp hr

/-- The finite-algebra lifting property makes the original ideal quotient reflect units. -/
private theorem isUnit_of_quotient_of_finite_idempotent_lifts
    {R : Type u} [CommRing R] (I : Ideal R)
    (h : ∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B]
      (e0 : B ⧸ I.map (algebraMap R B)), IsIdempotentElem e0 →
        ∃! e : B, IsIdempotentElem e ∧
          Ideal.Quotient.mk (I.map (algebraMap R B)) e = e0)
    {r : R} (hr : IsUnit (Ideal.Quotient.mk I r)) : IsUnit r := by
  exact isUnit_of_quotient_isUnit_of_le_jacobson I
    (le_jacobson_of_finite_idempotent_lifts.{u, v} I h) hr

/-- A unit derivative separates a linear polynomial from its monic-division cofactor. -/
private theorem isCoprime_X_sub_C_divByMonic_of_isUnit_eval_derivative
    {A : Type*} [CommRing A] (f : Polynomial A) (a : A)
    (hd : IsUnit (f.derivative.eval a)) :
    IsCoprime (Polynomial.X - Polynomial.C a)
      (f /ₘ (Polynomial.X - Polynomial.C a)) := by
  let g : Polynomial A := f /ₘ (Polynomial.X - Polynomial.C a)
  have hder : g.eval a = f.derivative.eval a := by
    have h := congrArg (fun p : Polynomial A => p.eval a)
      (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f a)
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero] using h
  have hgu : IsUnit (g.eval a) := by rw [hder]; exact hd
  obtain ⟨u, hu⟩ := hgu.exists_right_inv
  obtain ⟨h, hh⟩ := (Polynomial.X_sub_C_dvd_sub_C_eval :
    Polynomial.X - Polynomial.C a ∣ g - Polynomial.C (g.eval a))
  have hbez : -(Polynomial.C u * h) * (Polynomial.X - Polynomial.C a) +
      Polynomial.C u * g = 1 := by
    calc
      -(Polynomial.C u * h) * (Polynomial.X - Polynomial.C a) + Polynomial.C u * g =
          Polynomial.C u * (g - (Polynomial.X - Polynomial.C a) * h) := by ring
      _ = Polynomial.C u * Polynomial.C (g.eval a) := by rw [← hh, sub_sub_cancel]
      _ = 1 := by rw [← Polynomial.C_mul, mul_comm u, hu, Polynomial.C_1]
  apply (Ideal.isCoprime_span_singleton_iff (Polynomial.X - Polynomial.C a) g).mp
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨-(Polynomial.C u * h) * (Polynomial.X - Polynomial.C a), ?_,
    Polynomial.C u * g, ?_, hbez⟩
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

/-- The field specialization recovers the hypotheses and cofactor of
`Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero`. -/
private theorem isCoprime_X_sub_C_divByMonic_of_eval_derivative_ne_zero
    {K : Type*} [Field K] (f : Polynomial K) (a : K)
    (hf' : f.derivative.eval a ≠ 0) :
    IsCoprime (Polynomial.X - Polynomial.C a : Polynomial K)
      (f /ₘ (Polynomial.X - Polynomial.C a)) := by
  exact isCoprime_X_sub_C_divByMonic_of_isUnit_eval_derivative f a
    (isUnit_iff_ne_zero.mpr hf')

/-- A simple root separates its linear factor from the complementary factor. -/
private theorem exists_coprime_linear_factor
    {A : Type*} [CommRing A] (f : Polynomial A) (a : A)
    (ha : f.eval a = 0) (hd : IsUnit (f.derivative.eval a)) :
    ∃ g : Polynomial A, f = (Polynomial.X - Polynomial.C a) * g ∧
      IsCoprime (Ideal.span ({Polynomial.X - Polynomial.C a} : Set (Polynomial A)))
        (Ideal.span ({g} : Set (Polynomial A))) := by
  refine ⟨f /ₘ (Polynomial.X - Polynomial.C a), ?_, ?_⟩
  · exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
      (Polynomial.IsRoot.def.mpr ha)).symm
  · exact (Ideal.isCoprime_span_singleton_iff _ _).mpr
      (isCoprime_X_sub_C_divByMonic_of_isUnit_eval_derivative f a hd)

/-- The CRT component at a simple root has polynomial evaluation as its first coordinate. -/
private theorem exists_quotient_simple_root_equiv
    {A : Type*} [CommRing A] (f : Polynomial A) (a : A)
    (ha : f.eval a = 0) (hd : IsUnit (f.derivative.eval a)) :
    ∃ (g : Polynomial A)
      (θ : (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))) ≃+*
        A × (Polynomial A ⧸ Ideal.span ({g} : Set (Polynomial A)))),
      ∀ p : Polynomial A, (θ (Ideal.Quotient.mk _ p)).1 = p.eval a := by
  obtain ⟨g, hg, hcop⟩ := exists_coprime_linear_factor f a ha hd
  let P : Ideal (Polynomial A) :=
    Ideal.span ({Polynomial.X - Polynomial.C a} : Set (Polynomial A))
  let Q : Ideal (Polynomial A) := Ideal.span ({g} : Set (Polynomial A))
  have hideal : Ideal.span ({f} : Set (Polynomial A)) = P * Q := by
    rw [hg]
    exact (Ideal.span_singleton_mul_span_singleton _ _).symm
  let θ : (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))) ≃+*
      A × (Polynomial A ⧸ Q) :=
    (Ideal.quotEquivOfEq hideal).trans
      ((Ideal.quotientMulEquivQuotientProd P Q hcop).trans
        (RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv a).toRingEquiv
          (RingEquiv.refl _)))
  refine ⟨g, θ, ?_⟩
  intro p
  change ((RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv a).toRingEquiv
    (RingEquiv.refl _)) ((Ideal.quotientMulEquivQuotientProd P Q hcop)
      (Ideal.quotEquivOfEq hideal (Ideal.Quotient.mk _ p)))).1 = p.eval a
  rw [RingEquiv.coe_prodCongr]
  change Polynomial.quotientSpanXSubCAlgEquiv a
    ((Ideal.quotientMulEquivQuotientProd P Q hcop)
      (Ideal.quotEquivOfEq hideal (Ideal.Quotient.mk _ p))).1 = p.eval a
  rw [Ideal.quotEquivOfEq_mk, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.Quotient.factor_mk, Polynomial.quotientSpanXSubCAlgEquiv_mk]

/-- A lifted product component retains its scalar and root residue coordinates. -/
private theorem exists_idempotent_component_of_quotient_prod
    {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
    {S : Type*} [CommRing S] (I : Ideal R) (t : B) (a₀ : R)
    (θ : (B ⧸ I.map (algebraMap R B)) ≃+* (R ⧸ I) × S)
    (hscalar : ∀ r : R,
      (θ (Ideal.Quotient.mk _ (algebraMap R B r))).1 = Ideal.Quotient.mk I r)
    (ht : (θ (Ideal.Quotient.mk _ t)).1 = Ideal.Quotient.mk I a₀)
    (hlift : ∀ e0 : B ⧸ I.map (algebraMap R B), IsIdempotentElem e0 →
      ∃! e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = e0) :
    ∃ e : B, IsIdempotentElem e ∧
      (∀ b : B, e * b = b → ∃ r : R,
        b - algebraMap R B r * e ∈ I.map (algebraMap R B)) ∧
      (∀ r : R, algebraMap R B r * e ∈ I.map (algebraMap R B) ↔ r ∈ I) ∧
      e * (t - algebraMap R B a₀) ∈ I.map (algebraMap R B) := by
  let J : Ideal B := I.map (algebraMap R B)
  let q : B →+* B ⧸ J := Ideal.Quotient.mk J
  let ψ : B →+* (R ⧸ I) × S := θ.toRingHom.comp q
  let e0 : B ⧸ J := θ.symm (1, 0)
  have he0coord : θ e0 = (1, 0) := θ.apply_symm_apply _
  have he0 : IsIdempotentElem e0 := by
    change e0 * e0 = e0
    apply θ.injective
    rw [map_mul, he0coord]
    apply Prod.ext <;> simp
  obtain ⟨e, ⟨he, hqe⟩, _⟩ := hlift e0 he0
  have hψe : ψ e = (1, 0) := by
    change θ (q e) = (1, 0)
    rw [hqe]
    exact he0coord
  have hψscalar (r : R) : (ψ (algebraMap R B r)).1 = Ideal.Quotient.mk I r :=
    hscalar r
  have hψt : (ψ t).1 = Ideal.Quotient.mk I a₀ := ht
  have hmem (b : B) : b ∈ J ↔ ψ b = 0 := by
    constructor
    · intro hb
      change θ (q b) = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hb, map_zero]
    · intro hb
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply θ.injective
      simpa only [ψ, q, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, map_zero] using hb
  have hψre (r : R) : ψ (algebraMap R B r * e) = (Ideal.Quotient.mk I r, 0) := by
    rw [map_mul, hψe]
    apply Prod.ext
    · change (ψ (algebraMap R B r)).1 * 1 = Ideal.Quotient.mk I r
      simpa only [mul_one] using hψscalar r
    · change (ψ (algebraMap R B r)).2 * 0 = 0
      exact mul_zero _
  refine ⟨e, he, ?_, ?_, ?_⟩
  · intro b hb
    have hb2 : (ψ b).2 = 0 := by
      have h : (ψ e * ψ b).2 = (ψ b).2 := by
        simpa only [map_mul] using congrArg (fun z : B => (ψ z).2) hb
      rw [hψe] at h
      change 0 * (ψ b).2 = (ψ b).2 at h
      simpa only [zero_mul] using h.symm
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (I := I) (ψ b).1
    refine ⟨r, (hmem _).mpr ?_⟩
    rw [map_sub, hψre]
    exact sub_eq_zero.mpr (Prod.ext hr.symm hb2)
  · intro r
    rw [hmem, hψre]
    constructor
    · intro hr
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact congrArg Prod.fst hr
    · intro hr
      have hr0 : Ideal.Quotient.mk I r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
      apply Prod.ext
      · exact hr0
      · rfl
  · apply (hmem _).mpr
    rw [map_mul, map_sub, hψe]
    apply Prod.ext
    · change 1 * ((ψ t).1 - (ψ (algebraMap R B a₀)).1) = 0
      rw [hψt, hψscalar, sub_self, mul_zero]
    · change 0 * ((ψ t).2 - (ψ (algebraMap R B a₀)).2) = 0
      exact zero_mul _

/-- The simple-root CRT gives an original idempotent in the monic test algebra.

Monicity is only needed to obtain the finite-algebra lifting premise; the component
construction itself works for any polynomial with the stated simple residue root. -/
private theorem exists_idempotent_adjoinRoot_component
    {R : Type u} [CommRing R] (I : Ideal R) (f : Polynomial R) (a₀ : R)
    (ha : f.eval a₀ ∈ I)
    (hd : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀)))
    (hlift : ∀ e0 : AdjoinRoot f ⧸ I.map (algebraMap R (AdjoinRoot f)),
      IsIdempotentElem e0 → ∃! e : AdjoinRoot f,
        IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = e0) :
    ∃ e : AdjoinRoot f, IsIdempotentElem e ∧
      (∀ b : AdjoinRoot f, e * b = b → ∃ r : R,
        b - algebraMap R (AdjoinRoot f) r * e ∈ I.map (algebraMap R (AdjoinRoot f))) ∧
      (∀ r : R, algebraMap R (AdjoinRoot f) r * e ∈
        I.map (algebraMap R (AdjoinRoot f)) ↔ r ∈ I) ∧
      e * (AdjoinRoot.root f - algebraMap R (AdjoinRoot f) a₀) ∈
        I.map (algebraMap R (AdjoinRoot f)) := by
  let qI : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hbar : (f.map qI).eval (qI a₀) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hdbar : IsUnit ((f.map qI).derivative.eval (qI a₀)) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact hd
  obtain ⟨g, θ, hθ⟩ := exists_quotient_simple_root_equiv (f.map qI) (qI a₀) hbar hdbar
  have hJ : I.map (algebraMap R (AdjoinRoot f)) = I.map (AdjoinRoot.of f) := by
    rw [AdjoinRoot.algebraMap_eq]
  let δ : (AdjoinRoot f ⧸ I.map (algebraMap R (AdjoinRoot f))) ≃+*
      (Polynomial (R ⧸ I) ⧸ Ideal.span ({f.map qI} : Set (Polynomial (R ⧸ I)))) :=
    (Ideal.quotEquivOfEq hJ).trans (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I f)
  let Θ : (AdjoinRoot f ⧸ I.map (algebraMap R (AdjoinRoot f))) ≃+*
      (R ⧸ I) × (Polynomial (R ⧸ I) ⧸ Ideal.span ({g} : Set (Polynomial (R ⧸ I)))) :=
    δ.trans θ
  have hΘ (p : Polynomial R) :
      (Θ (Ideal.Quotient.mk _ (AdjoinRoot.mk f p))).1 = (p.map qI).eval (qI a₀) := by
    change (θ (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I f
      (Ideal.quotEquivOfEq hJ (Ideal.Quotient.mk _ (AdjoinRoot.mk f p))))).1 = _
    rw [Ideal.quotEquivOfEq_mk,
      AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of]
    exact hθ (p.map qI)
  have hconst (r : R) : AdjoinRoot.mk f (Polynomial.C r) =
      algebraMap R (AdjoinRoot f) r := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.mk_C (f := f) r
  apply exists_idempotent_component_of_quotient_prod
    (S := Polynomial (R ⧸ I) ⧸ Ideal.span ({g} : Set (Polynomial (R ⧸ I))))
    I (AdjoinRoot.root f) a₀ Θ
  · intro r
    simpa only [hconst, Polynomial.map_C, Polynomial.eval_C] using hΘ (Polynomial.C r)
  · simpa only [AdjoinRoot.mk_X, Polynomial.map_X, Polynomial.eval_X] using hΘ Polynomial.X
  · exact hlift

/-- The range of an idempotent endomorphism of a projective module is projective. -/
private theorem projective_range_of_idempotent
    {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M] [Module R M]
    [Module.Projective R M] (p : M →ₗ[R] M) (hp : IsIdempotentElem p) :
    Module.Projective R p.range := by
  refine Module.Projective.of_split p.range.subtype p.rangeRestrict ?_
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (LinearMap.IsIdempotentElem.mem_range_iff hp).mp x.property

/-- A map onto a finite projective module is bijective if it is onto modulo a Jacobson
ideal and its scalar kernel lies in that ideal. -/
private theorem bijective_of_surjective_mod_ideal_of_kernel_mem
    {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
    [Module.Finite R E] [Module.Projective R E]
    (I : Ideal R) (hJac : I ≤ (⊥ : Ideal R).jacobson) (α : R →ₗ[R] E)
    (hmod : Function.Surjective ((I • (⊤ : Submodule R E)).mkQ ∘ₗ α))
    (hker : ∀ r, α r = 0 → r ∈ I) : Function.Bijective α := by
  have hsurj : Function.Surjective α :=
    LinearMap.surjective_of_surjective_comp_mkQ α I hJac hmod
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective α
    (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨injective_of_split_of_kernel_mem I α σ ?_ hker ?_, hsurj⟩
  · intro y
    exact congrArg (fun f : E →ₗ[R] E => f y) hσ
  · intro r hr
    simpa only [mul_neg_one, neg_add_eq_sub] using
      (Ideal.mem_jacobson_bot.mp (hJac hr) (-1))

/-- On an idempotent component, the extended ideal is the scalar-ideal submodule. -/
private theorem mem_smul_top_range_lmul_iff
    {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
    (I : Ideal R) (e : B) (he : IsIdempotentElem e)
    (x : (Algebra.lmul R B e).range) :
    x ∈ I • (⊤ : Submodule R (Algebra.lmul R B e).range) ↔
      (x : B) ∈ I.map (algebraMap R B) := by
  let p : B →ₗ[R] B := Algebra.lmul R B e
  have hp : IsIdempotentElem p := he.map (Algebra.lmul R B)
  have hp_apply (b : B) : p b = e * b := by
    simp only [p, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  have hmap : (I • (⊤ : Submodule R B)).map p.rangeRestrict =
      I • (⊤ : Submodule R p.range) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr p.surjective_rangeRestrict]
  constructor
  · intro hx
    have hxmap : x ∈ (I • (⊤ : Submodule R B)).map p.rangeRestrict := by
      rw [hmap]
      exact hx
    obtain ⟨b, hb, hbx⟩ := Submodule.mem_map.mp hxmap
    have hbJ : b ∈ I.map (algebraMap R B) := by
      have hb' : b ∈ (I.map (algebraMap R B)).restrictScalars R := by
        rw [← Ideal.smul_top_eq_map]
        exact hb
      exact hb'
    have hbx' : e * b = (x : B) := by
      calc
        e * b = p b := (hp_apply b).symm
        _ = (x : B) := congrArg (fun y : p.range => (y : B)) hbx
    rw [← hbx']
    exact (I.map (algebraMap R B)).mul_mem_left e hbJ
  · intro hx
    have hxB : (x : B) ∈ I • (⊤ : Submodule R B) := by
      have hx' : (x : B) ∈ (I.map (algebraMap R B)).restrictScalars R := hx
      rwa [← Ideal.smul_top_eq_map] at hx'
    have hxmap : x ∈ (I • (⊤ : Submodule R B)).map p.rangeRestrict := by
      refine Submodule.mem_map.mpr ⟨(x : B), hxB, ?_⟩
      apply Subtype.ext
      exact (LinearMap.IsIdempotentElem.mem_range_iff hp).mp x.property
    rwa [hmap] at hxmap

/-- A monic root component with its scalar and root residue coordinates gives a root in
its original coefficient ring. -/
private theorem exists_root_of_idempotent_adjoinRoot_component
    {R : Type u} [CommRing R] (I : Ideal R) (hJac : I ≤ (⊥ : Ideal R).jacobson)
    (f : Polynomial R) (hf : f.Monic) (a₀ : R)
    (e : AdjoinRoot f) (he : IsIdempotentElem e)
    (hres : ∀ b : AdjoinRoot f, e * b = b →
      ∃ r : R, b - algebraMap R (AdjoinRoot f) r * e ∈
        I.map (algebraMap R (AdjoinRoot f)))
    (hscalar : ∀ r : R, algebraMap R (AdjoinRoot f) r * e ∈
      I.map (algebraMap R (AdjoinRoot f)) ↔ r ∈ I)
    (hroot : e * (AdjoinRoot.root f - algebraMap R (AdjoinRoot f) a₀) ∈
      I.map (algebraMap R (AdjoinRoot f))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  let B := AdjoinRoot f
  let p : B →ₗ[R] B := Algebra.lmul R B e
  let E := p.range
  have hp : IsIdempotentElem p := he.map (Algebra.lmul R B)
  have hp_apply (b : B) : p b = e * b := by
    simp only [p, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  letI : Module.Finite R B := hf.finite_adjoinRoot
  letI : Module.Projective R B :=
    Module.Projective.of_basis (AdjoinRoot.powerBasis' hf).basis
  letI : Module.Finite R E := Module.Finite.range p
  letI : Module.Projective R E := projective_range_of_idempotent p hp
  have hfix (x : E) : e * (x : B) = (x : B) := by
    rw [← hp_apply]
    exact (LinearMap.IsIdempotentElem.mem_range_iff hp).mp x.property
  have heE : e ∈ E := by
    refine ⟨1, ?_⟩
    rw [hp_apply, mul_one]
  let ε : E := ⟨e, heE⟩
  let α : R →ₗ[R] E := LinearMap.toSpanSingleton R E ε
  have hα1 : α 1 = ε := LinearMap.toSpanSingleton_apply_one R E ε
  have hα (r : R) : (α r : B) = algebraMap R B r * e := by
    calc
      (α r : B) = (α (r • (1 : R)) : B) := by rw [smul_eq_mul, mul_one]
      _ = ((r • α 1 : E) : B) := by rw [α.map_smul]
      _ = r • e := by rw [Submodule.coe_smul, hα1]
      _ = algebraMap R B r * e := Algebra.smul_def r e
  have hmod : Function.Surjective ((I • (⊤ : Submodule R E)).mkQ ∘ₗ α) := by
    intro z
    obtain ⟨x, hx⟩ := (I • (⊤ : Submodule R E)).mkQ_surjective z
    obtain ⟨r, hr⟩ := hres (x : B) (hfix x)
    have hdiff : x - α r ∈ I • (⊤ : Submodule R E) := by
      apply (mem_smul_top_range_lmul_iff I e he (x - α r)).mpr
      simpa only [Submodule.coe_sub, hα] using hr
    have heq : (I • (⊤ : Submodule R E)).mkQ x =
        (I • (⊤ : Submodule R E)).mkQ (α r) := by
      simpa only [Submodule.mkQ_apply] using
        (Submodule.Quotient.eq (I • (⊤ : Submodule R E))).mpr hdiff
    refine ⟨r, ?_⟩
    exact heq.symm.trans hx
  have hker : ∀ r, α r = 0 → r ∈ I := by
    intro r hr
    apply (hscalar r).mp
    have hrB : algebraMap R B r * e = 0 := by
      calc
        algebraMap R B r * e = (α r : B) := (hα r).symm
        _ = 0 := congrArg (fun x : E => (x : B)) hr
    rw [hrB]
    exact (I.map (algebraMap R B)).zero_mem
  have hbij : Function.Bijective α :=
    bijective_of_surjective_mod_ideal_of_kernel_mem I hJac α hmod hker
  obtain ⟨a, ha⟩ := hbij.2 (p.rangeRestrict (AdjoinRoot.root f))
  have hae : algebraMap R B a * e = AdjoinRoot.root f * e := by
    calc
      algebraMap R B a * e = (α a : B) := (hα a).symm
      _ = p (AdjoinRoot.root f) := congrArg (fun x : E => (x : B)) ha
      _ = e * AdjoinRoot.root f := hp_apply _
      _ = AdjoinRoot.root f * e := mul_comm _ _
  have hinj : Function.Injective (fun r : R => algebraMap R B r * e) := by
    intro r s hrs
    apply hbij.1
    apply Subtype.ext
    exact (hα r).trans (hrs.trans (hα s).symm)
  have ht : f.eval₂ (algebraMap R B) (AdjoinRoot.root f) = 0 := by
    exact (AdjoinRoot.aeval_eq (f := f) f).trans (AdjoinRoot.mk_self (f := f))
  refine ⟨a, Polynomial.IsRoot.def.mpr (eval_eq_zero_of_component f hinj ht hae), ?_⟩
  apply (hscalar (a - a₀)).mp
  have hcongr : algebraMap R B (a - a₀) * e =
      e * (AdjoinRoot.root f - algebraMap R B a₀) := by
    calc
      algebraMap R B (a - a₀) * e =
          algebraMap R B a * e - algebraMap R B a₀ * e := by rw [map_sub, sub_mul]
      _ = AdjoinRoot.root f * e - algebraMap R B a₀ * e := by rw [hae]
      _ = e * (AdjoinRoot.root f - algebraMap R B a₀) := by
        rw [mul_sub, mul_comm e (AdjoinRoot.root f), mul_comm e (algebraMap R B a₀)]
  rw [hcongr]
  exact hroot

/-- A pair is Henselian if and only if idempotents lift uniquely through the extended-ideal
quotient in every module-finite commutative algebra in a universe containing the base.

This is the idempotent criterion of The Stacks project, Lemma 15.11.6 (3),
[Tag 09XI](https://stacks.math.columbia.edu/tag/09XI). -/
theorem iff_existsUnique_isIdempotentElem_map
    {R : Type u} [CommRing R] (I : Ideal R) :
    HenselianRing R I ↔
      ∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B]
        (e0 : B ⧸ I.map (algebraMap R B)), IsIdempotentElem e0 →
          ∃! e : B, IsIdempotentElem e ∧
            Ideal.Quotient.mk (I.map (algebraMap R B)) e = e0 := by
  constructor
  · intro hR B _ _ _ e0 he0
    letI : HenselianRing R I := hR
    exact existsUnique_isIdempotentElem_map I he0
  · intro h
    have hJac : I ≤ Ideal.jacobson (⊥ : Ideal R) :=
      le_jacobson_of_finite_idempotent_lifts.{u, v} I h
    refine { jac := hJac, is_henselian := ?_ }
    intro f hf a₀ ha hd
    letI : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
    obtain ⟨e, he, hres, hscalar, hroot⟩ :=
      exists_idempotent_adjoinRoot_component I f a₀ ha hd
        (existsUnique_idempotent_of_maxUniverse.{u, v} I h (AdjoinRoot f))
    exact exists_root_of_idempotent_adjoinRoot_component I hJac
      f hf a₀ e he hres hscalar hroot

end HenselianRing
