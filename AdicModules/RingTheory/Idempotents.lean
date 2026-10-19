/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Polynomial.RootUniqueness
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import AdicModules.Polynomial.Coprime
import AdicModules.Polynomial.Hensel
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
import Mathlib.Tactic.Ring

/-!
# Idempotents in Henselian pairs

Idempotents lift uniquely from the quotient by a Henselian-pair ideal. More generally,
for a module-finite commutative algebra over the base ring, idempotents lift uniquely
from the quotient by the extension of that ideal. The lifted idempotent belongs to
the given algebra, and its image is specified by equality in the quotient.

The finite-algebra argument uses Mathlib's finite-module Cayley–Hamilton theorem,
monic factor lifting, and a polynomial Bézout identity evaluated in the given algebra.
Regular multiplication, distinguished-polynomial reduction and polynomial evaluation
use Mathlib's interfaces. Uniqueness follows from the simple-root uniqueness criterion.

## References

* The Stacks project authors, *The Stacks project*,
  [Lemma 15.11.6(3)](https://stacks.math.columbia.edu/tag/09XI).
* Hideyuki Matsumura, *Commutative Ring Theory*, Theorem 2.1 (Cayley–Hamilton).
-/

@[expose] public section

universe u v

namespace HenselianRing

/-- An idempotent in the quotient by a Henselian-pair ideal lifts to a unique
idempotent in the original ring.

This is the base-ring case of
[The Stacks Project, Lemma 15.11.6(3)](https://stacks.math.columbia.edu/tag/09XI). -/
theorem existsUnique_isIdempotentElem {R : Type u} [CommRing R]
    (I : Ideal R) [HenselianRing R I] {e0 : R ⧸ I}
    (he0 : IsIdempotentElem e0) :
    ∃! e : R, IsIdempotentElem e ∧ Ideal.Quotient.mk I e = e0 := by
  let p : Polynomial R := Polynomial.X * (Polynomial.X - 1)
  have hp : p.Monic := by
    simpa only [p, Polynomial.C_0, Polynomial.C_1, sub_zero] using
      (Polynomial.monic_X_sub_C (0 : R)).mul (Polynomial.monic_X_sub_C (1 : R))
  have heval (a : R) : p.eval a = a * (a - 1) := by
    simp only [p, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_one]
  have hroot (a : R) : p.IsRoot a ↔ IsIdempotentElem a := by
    rw [Polynomial.IsRoot.def, heval, mul_sub, mul_one, sub_eq_zero,
      isIdempotentElem_iff]
  have hderiv (a : R) : p.derivative.eval a = 2 * a - 1 := by
    simp only [p, Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_one, sub_zero, one_mul, mul_one,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
      sub_add_eq_add_sub, two_mul]
  have hunit (a : R) (ha : IsIdempotentElem (Ideal.Quotient.mk I a)) :
      IsUnit (Ideal.Quotient.mk I (p.derivative.eval a)) := by
    rw [hderiv, two_mul, map_sub, map_add, map_one]
    -- The derivative is its own inverse at an idempotent, even in characteristic two.
    apply IsUnit.of_mul_eq_one
      (Ideal.Quotient.mk I a + Ideal.Quotient.mk I a - 1)
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one,
      isIdempotentElem_iff.mp ha, add_sub_cancel_right, sub_sub_cancel]
  obtain ⟨a0, ha0⟩ := Ideal.Quotient.mk_surjective (I := I) e0
  have h0 : p.eval a0 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [heval, map_mul, map_sub, map_one, ha0, mul_sub, mul_one,
      isIdempotentElem_iff.mp he0, sub_self]
  have h1 : IsUnit (Ideal.Quotient.mk I (p.derivative.eval a0)) := by
    apply hunit
    simpa only [ha0] using he0
  obtain ⟨e, he, hae⟩ := HenselianRing.is_henselian (R := R) (I := I) p hp a0 h0 h1
  have heq : Ideal.Quotient.mk I e = e0 :=
    ((Ideal.Quotient.mk_eq_mk_iff_sub_mem e a0).mpr hae).trans ha0
  letI : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I (HenselianRing.jac (R := R) (I := I))
  refine ⟨e, ⟨(hroot e).mp he, heq⟩, ?_⟩
  intro b hb
  exact Polynomial.IsRoot.eq_of_map_eq ((hroot b).mpr hb.1) he
    (Ideal.Quotient.mk I) (hb.2.trans heq.symm)
    (hunit b (hb.1.map (Ideal.Quotient.mk I)))

private theorem exists_monic_map_eq_pow_aeval_eq_zero
    {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    [Algebra R B] [Module.Finite R B] (I : Ideal R)
    {c : B} (hc : c ∈ I.map (algebraMap R B)) :
    ∃ P : Polynomial R, P.Monic ∧
      P.map (Ideal.Quotient.mk I) = Polynomial.X ^ P.natDegree ∧
      Polynomial.aeval c P = 0 := by
  have hrange : LinearMap.range (Algebra.lmul R B c) ≤ I • (⊤ : Submodule R B) := by
    rw [Ideal.smul_top_eq_map]
    rintro x ⟨y, rfl⟩
    apply (Submodule.restrictScalars_mem R _ _).mpr
    simpa only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mul_comm] using
      (I.map (algebraMap R B)).mul_mem_left y hc
  obtain ⟨P, hP, _, hcoeff, hann⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      R (Algebra.lmul R B c) I hrange
  have hdist : P.IsDistinguishedAt I := by
    refine { monic := hP, mem := ?_ }
    intro k hk
    exact Ideal.pow_le_self (Nat.ne_of_gt (Nat.sub_pos_of_lt hk)) (hcoeff k)
  refine ⟨P, hP, hdist.map_eq_X_pow, ?_⟩
  apply Algebra.lmul_injective (R := R) (A := B)
  rw [map_zero, ← Polynomial.aeval_algHom_apply]
  exact hann

private theorem map_le_jacobson_of_isIntegral
    {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    (φ : R →+* B) (hφ : φ.IsIntegral) (I : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥) :
    I.map φ ≤ Ideal.jacobson ⊥ := by
  apply Ideal.map_le_iff_le_comap.mpr
  rw [Ideal.comap_jacobson]
  refine le_sInf ?_
  rintro K ⟨m, ⟨_, hm⟩, rfl⟩
  let : m.IsMaximal := hm
  let : (m.comap φ).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal φ hφ m
  calc
    I ≤ Ideal.jacobson ⊥ := hI
    _ ≤ (m.comap φ).jacobson := Ideal.jacobson_mono bot_le
    _ = m.comap φ := Ideal.jacobson_eq_self_of_isMaximal

private theorem map_le_jacobson_of_le_jacobson
    {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    [Algebra R B] [Module.Finite R B] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥) :
    I.map (algebraMap R B) ≤ Ideal.jacobson ⊥ := by
  exact map_le_jacobson_of_isIntegral (algebraMap R B)
    (RingHom.Finite.to_isIntegral
      ((RingHom.finite_algebraMap (A := R) (B := B)).mpr inferInstance)) I hI

private theorem eq_of_isIdempotentElem_quotient_eq
    {S : Type u} [CommRing S] (J : Ideal S)
    (hJ : J ≤ Ideal.jacobson ⊥) {e f : S}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : Ideal.Quotient.mk J e = Ideal.Quotient.mk J f) : e = f := by
  let p : Polynomial S := Polynomial.X * (Polynomial.X - 1)
  have hroot (a : S) : p.IsRoot a ↔ IsIdempotentElem a := by
    rw [Polynomial.IsRoot.def]
    simp only [p, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      mul_sub, mul_one, sub_eq_zero, isIdempotentElem_iff]
  have hderiv (a : S) : p.derivative.eval a = 2 * a - 1 := by
    simp only [p, Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_one, sub_zero, one_mul, mul_one,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
      sub_add_eq_add_sub, two_mul]
  have hunit : IsUnit (Ideal.Quotient.mk J (p.derivative.eval e)) := by
    rw [hderiv, two_mul, map_sub, map_add, map_one]
    -- The derivative is its own inverse at an idempotent, also in characteristic two.
    apply IsUnit.of_mul_eq_one
      (Ideal.Quotient.mk J e + Ideal.Quotient.mk J e - 1)
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one,
      isIdempotentElem_iff.mp (he.map (Ideal.Quotient.mk J)),
      add_sub_cancel_right, sub_sub_cancel]
  let : IsLocalHom (Ideal.Quotient.mk J) := isLocalHom_of_le_jacobson_bot J hJ
  exact Polynomial.IsRoot.eq_of_map_eq ((hroot e).mpr he) ((hroot f).mpr hf)
    (Ideal.Quotient.mk J) hef hunit

/-- In a module-finite commutative algebra over a Henselian pair, each idempotent
modulo the extended ideal lifts to a unique idempotent in the given algebra.

This is the idempotent-lifting property of Henselian pairs; see
[The Stacks Project, Lemma 15.11.6(3)](https://stacks.math.columbia.edu/tag/09XI). -/
theorem existsUnique_isIdempotentElem_map {R : Type u} {B : Type v}
    [CommRing R] [CommRing B] (I : Ideal R) [HenselianRing R I]
    [Algebra R B] [Module.Finite R B]
    {e0 : B ⧸ I.map (algebraMap R B)} (he0 : IsIdempotentElem e0) :
    ∃! e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk (I.map (algebraMap R B)) e = e0 := by
  classical
  rcases subsingleton_or_nontrivial B with hB | hB
  · let : Subsingleton B := hB
    refine ⟨0, ⟨?_, Subsingleton.elim _ _⟩, ?_⟩
    · exact isIdempotentElem_iff.mpr (zero_mul 0)
    · intro f _
      exact Subsingleton.elim _ _
  let : Nontrivial B := hB
  have : Nontrivial R := ⟨⟨0, 1, fun h =>
    (zero_ne_one : (0 : B) ≠ 1) (by
      simpa only [map_zero, map_one] using congrArg (algebraMap R B) h)⟩⟩
  let α : R →+* B := algebraMap R B
  let J : Ideal B := I.map α
  let qJ : B →+* B ⧸ J := Ideal.Quotient.mk J
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (I := J) e0
  let c : B := b ^ 2 - b
  have hc : c ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk J (b ^ 2 - b) = 0
    rw [map_sub, map_pow, hb, pow_two, he0.eq, sub_self]
  obtain ⟨P, hP, hPmap, hPc⟩ :=
    exists_monic_map_eq_pow_aeval_eq_zero I hc
  have hn : P.natDegree ≠ 0 := by
    intro hdeg
    have hPone : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP hdeg
    rw [hPone, map_one] at hPc
    exact one_ne_zero hPc
  let p : Polynomial R := Polynomial.X * (Polynomial.X - 1)
  have hp : p.Monic := by
    simpa only [p, Polynomial.C_0, Polynomial.C_1, sub_zero] using
      (Polynomial.monic_X_sub_C (0 : R)).mul (Polynomial.monic_X_sub_C (1 : R))
  have hpn : p.natDegree ≠ 0 := by
    intro hdeg
    have hpone : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hp hdeg
    have h := congrArg (Polynomial.eval (0 : R)) hpone
    simp [p] at h
  let F : Polynomial R := P.comp p
  have hF : F.Monic := hP.comp hp hpn
  have hX : (Polynomial.X : Polynomial (R ⧸ I)).Monic := by
    simpa only [Polynomial.C_0, sub_zero] using
      Polynomial.monic_X_sub_C (0 : R ⧸ I)
  have hX1 : (Polynomial.X - 1 : Polynomial (R ⧸ I)).Monic := by
    simpa only [Polynomial.C_1] using Polynomial.monic_X_sub_C (1 : R ⧸ I)
  have hcopX : IsCoprime (Polynomial.X : Polynomial (R ⧸ I))
      (Polynomial.X - 1) := by
    refine ⟨1, -1, ?_⟩
    ring
  have hcop0 : IsCoprime (Polynomial.X ^ P.natDegree : Polynomial (R ⧸ I))
      ((Polynomial.X - 1) ^ P.natDegree) := hcopX.pow
  have hFmap : F.map (Ideal.Quotient.mk I) =
      Polynomial.X ^ P.natDegree * (Polynomial.X - 1) ^ P.natDegree := by
    simp only [F, Polynomial.map_comp, hPmap, Polynomial.X_pow_comp, p,
      Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one,
      mul_pow]
  obtain ⟨G, H, hG, _hH, hfac, hGmap, hHmap⟩ :=
    HenselianRing.exists_monic_factorization I hF (hX.pow P.natDegree)
      (hX1.pow P.natDegree) hcop0 hFmap
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I (HenselianRing.jac (R := R) (I := I))
  have hcop : IsCoprime G H :=
    (Polynomial.Monic.isCoprime_map_iff (Ideal.Quotient.mk I) hG).mp (by
      simpa only [hGmap, hHmap] using hcop0)
  obtain ⟨U, V, hUV⟩ := hcop
  let η : Polynomial R →ₐ[R] B := Polynomial.aeval b
  let g : B := η G
  let h : B := η H
  let u : B := η U
  let v : B := η V
  have hpb : Polynomial.aeval b p = c := by
    simp only [p, c, map_mul, map_sub, Polynomial.aeval_X,
      mul_sub, mul_one, pow_two]
  have hFzero : η F = 0 := by
    change Polynomial.aeval b (P.comp p) = 0
    rw [Polynomial.aeval_comp, hpb]
    exact hPc
  have hgh : g * h = 0 := by
    calc
      g * h = η (G * H) := (map_mul η G H).symm
      _ = η F := congrArg η hfac.symm
      _ = 0 := hFzero
  have hbez : u * g + v * h = 1 := by
    change η U * η G + η V * η H = 1
    rw [← map_mul, ← map_mul, ← map_add, hUV, map_one]
  let e : B := u * g
  have he : IsIdempotentElem e := by
    apply isIdempotentElem_iff.mpr
    change (u * g) * (u * g) = u * g
    calc
      (u * g) * (u * g) =
          (u * g) * (u * g + v * h) - (u * v) * (g * h) := by ring
      _ = u * g := by rw [hbez, hgh, mul_one, mul_zero, sub_zero]
  have hkill (a : R) (ha : a ∈ I) : (qJ.comp α) a = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_map_of_mem α ha
  let δ : R ⧸ I →+* B ⧸ J := Ideal.Quotient.lift I (qJ.comp α) hkill
  have hδ : δ.comp (Ideal.Quotient.mk I) = qJ.comp α :=
    Ideal.Quotient.lift_comp_mk I (qJ.comp α) hkill
  have htransport (Q : Polynomial R) :
      qJ (η Q) = (Q.map (Ideal.Quotient.mk I)).eval₂ δ e0 := by
    calc
      qJ (η Q) = Q.eval₂ (qJ.comp α) (qJ b) := by
        change qJ (Polynomial.aeval b Q) = _
        rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
      _ = Q.eval₂ (δ.comp (Ideal.Quotient.mk I)) e0 := by rw [hδ, hb]
      _ = (Q.map (Ideal.Quotient.mk I)).eval₂ δ e0 :=
        (Polynomial.eval₂_map (Ideal.Quotient.mk I) δ e0).symm
  have hgbar : qJ g = e0 := by
    calc
      qJ g = (G.map (Ideal.Quotient.mk I)).eval₂ δ e0 := htransport G
      _ = e0 ^ P.natDegree := by
        rw [hGmap]
        simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
      _ = e0 := he0.pow_eq hn
  have hhbar : qJ h = (e0 - 1) ^ P.natDegree := by
    change qJ (η H) = _
    rw [htransport H, hHmap]
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_one]
  have he0h : e0 * qJ h = 0 := by
    rw [hhbar]
    calc
      e0 * (e0 - 1) ^ P.natDegree =
          e0 ^ P.natDegree * (e0 - 1) ^ P.natDegree :=
        congrArg (fun z => z * (e0 - 1) ^ P.natDegree) (he0.pow_eq hn).symm
      _ = (e0 * (e0 - 1)) ^ P.natDegree := (mul_pow _ _ _).symm
      _ = 0 := by rw [mul_sub, mul_one, he0.eq, sub_self, zero_pow hn]
  have hbezbar : qJ u * e0 + qJ v * qJ h = 1 := by
    have hq := congrArg qJ hbez
    simpa only [map_add, map_mul, map_one, hgbar] using hq
  have hemap : qJ e = e0 := by
    calc
      qJ e = qJ u * e0 := by
        change qJ (u * g) = _
        rw [map_mul, hgbar]
      _ = (qJ u * e0) * e0 := by rw [mul_assoc, he0.eq]
      _ = (qJ u * e0 + qJ v * qJ h) * e0 - qJ v * (e0 * qJ h) := by ring
      _ = e0 := by rw [hbezbar, he0h, one_mul, mul_zero, sub_zero]
  refine ⟨e, ⟨he, hemap⟩, ?_⟩
  intro f hf
  exact eq_of_isIdempotentElem_quotient_eq J
    (map_le_jacobson_of_le_jacobson I (HenselianRing.jac (R := R) (I := I)))
    hf.1 he (hf.2.trans hemap.symm)

end HenselianRing
