/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianCriterion
import AdicModules.RingTheory.HenselianTransport

import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.Tactic.Ring

/-!
# Lifting points of étale algebras over Henselian pairs

A specified point of an étale algebra over the quotient of a Henselian pair
has a unique lift to the base ring, with its given algebra structure.

## References

The existence assertion is the implication (1) ⇒ (2) in
[Stacks Project, Lemma 15.11.6, tag 09XI](https://stacks.math.columbia.edu/tag/09XI).
Item (2) asserts existence, not uniqueness. The unique-lift formulation
additionally uses rigidity of étale sections congruent modulo an ideal
contained in the Jacobson radical: their equalizer is open and contains
`Spec (R ⧸ I)`, hence every closed point of `Spec R` and therefore all of
`Spec R`. This is a derivation of uniqueness, not a uniqueness assertion
in item (2) of that lemma.

## Degenerate cases

No locality or nontriviality assumption is imposed: zero algebras and the zero base ring
are allowed. A Henselian pair with the unit ideal has zero base ring, since its ideal
lies in the Jacobson radical.
-/

@[expose] public section

universe u v w

section

namespace HenselianEtaleAugmentation

variable {T : Type u} {S : Type v} [CommRing T] [CommRing S] [Algebra T S]

/-- The localized infinitesimal uniqueness argument does not require finiteness. -/
private theorem augmentation_ker_eq_sq (p : S →ₐ[T] T) (g : S) (hg : p g = 1)
    [Algebra.FormallyUnramified T (Localization.Away g)] :
    RingHom.ker p.toRingHom = (RingHom.ker p.toRingHom) ^ 2 := by
  let K : Ideal S := RingHom.ker p.toRingHom
  let Q := S ⧸ K ^ 2
  let q : S →ₐ[T] Q := Ideal.Quotient.mkₐ T (K ^ 2)
  let s : S →ₐ[T] Q := (Algebra.ofId T Q).comp p
  let J : Ideal Q := K.map q.toRingHom
  change K = K ^ 2
  have hJ : J ^ 2 = ⊥ := by
    change (K.map (Ideal.Quotient.mk (K ^ 2))) ^ 2 = ⊥
    rw [← Ideal.map_pow, Ideal.map_mk_eq_bot_of_le le_rfl]
  have hcong (x : S) : q x - s x ∈ J := by
    have hx : x - algebraMap T S (p x) ∈ K := by
      change p (x - algebraMap T S (p x)) = 0
      simp
    change q x - algebraMap T Q (p x) ∈ J
    have hmap : q (x - algebraMap T S (p x)) ∈ J :=
      Ideal.mem_map_of_mem q.toRingHom hx
    simpa only [map_sub, q.commutes] using hmap
  have hsg : s g = 1 := by
    change algebraMap T Q (p g) = 1
    rw [hg, map_one]
  have hqg1 : q g - 1 ∈ J := by
    simpa only [hsg] using hcong g
  have hnil : (q g - 1) ^ 2 = 0 := by
    have hm : (q g - 1) ^ 2 ∈ J ^ 2 := by
      simpa only [pow_two] using Ideal.mul_mem_mul hqg1 hqg1
    have hm0 : (q g - 1) ^ 2 ∈ (⊥ : Ideal Q) := by
      simpa only [hJ] using hm
    exact Ideal.mem_bot.mp hm0
  have hunit : q g * (2 - q g) = 1 := by
    calc
      q g * (2 - q g) = 1 - (q g - 1) ^ 2 := by ring
      _ = 1 := by rw [hnil, sub_zero]
  have hqg : IsUnit (q g) := by
    exact ⟨⟨q g, 2 - q g, hunit, by simpa only [mul_comm] using hunit⟩, rfl⟩
  have hsg_unit : IsUnit (s g) := by
    rw [hsg]
    exact isUnit_one
  let L := Localization.Away g
  let q' : L →ₐ[T] Q := IsLocalization.Away.liftAlgHom g hqg
  let s' : L →ₐ[T] Q := IsLocalization.Away.liftAlgHom g hsg_unit
  have hq' (x : S) : q' (algebraMap S L x) = q x :=
    IsLocalization.Away.lift_eq g hqg x
  have hs' (x : S) : s' (algebraMap S L x) = s x :=
    IsLocalization.Away.lift_eq g hsg_unit x
  have hred : (Ideal.Quotient.mkₐ T J).comp q' =
      (Ideal.Quotient.mkₐ T J).comp s' := by
    apply IsLocalization.algHom_ext (Submonoid.powers g)
    apply AlgHom.ext
    intro x
    change Ideal.Quotient.mk J (q' (algebraMap S L x)) =
      Ideal.Quotient.mk J (s' (algebraMap S L x))
    rw [hq', hs']
    exact Ideal.Quotient.eq.mpr (hcong x)
  have hext : q' = s' :=
    Algebra.FormallyUnramified.comp_injective (R := T) (A := L) J hJ hred
  have hqs (x : S) : q x = s x := by
    calc
      q x = q' (algebraMap S L x) := (hq' x).symm
      _ = s' (algebraMap S L x) :=
        congrArg (fun f : L →ₐ[T] Q => f (algebraMap S L x)) hext
      _ = s x := hs' x
  apply le_antisymm
  · intro x hx
    have hpx : p x = 0 := hx
    have hqx : q x = 0 := by
      rw [hqs]
      change algebraMap T Q (p x) = 0
      rw [hpx, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hqx
  · simpa only [pow_two] using (Ideal.mul_le_left : K * K ≤ K)

/-- Finite generation comes from the image of the actual split projection. -/
private theorem augmentation_ker_fg [Module.Finite T S] (p : S →ₐ[T] T) :
    (RingHom.ker p.toRingHom).FG := by
  let K : Ideal S := RingHom.ker p.toRingHom
  let π : S →ₗ[T] S :=
    LinearMap.id - (Algebra.linearMap T S).comp p.toLinearMap
  have hπ (x : S) : π x = x - algebraMap T S (p x) := rfl
  have hrange : π.range = K.restrictScalars T := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      change p (π y) = 0
      rw [hπ]
      simp
    · intro hx
      have hpx : p x = 0 := hx
      refine ⟨x, ?_⟩
      rw [hπ, hpx, map_zero, sub_zero]
  have hfg : (K.restrictScalars T).FG := by
    rw [← hrange]
    exact Submodule.fg_range π
  exact Submodule.FG.of_restrictScalars T hfg

/-- Principality is subsequent to, and separate from, the kernel-square identity. -/
private theorem exists_idempotent_span_augmentation_ker [Module.Finite T S]
    (p : S →ₐ[T] T) (g : S) (hg : p g = 1)
    [Algebra.FormallyUnramified T (Localization.Away g)] :
    ∃ e : S, IsIdempotentElem e ∧ Ideal.span {e} = RingHom.ker p.toRingHom := by
  let K : Ideal S := RingHom.ker p.toRingHom
  have hfg : K.FG := augmentation_ker_fg p
  have hsq : K = K ^ 2 := augmentation_ker_eq_sq p g hg
  have hid : IsIdempotentElem K := by
    change K * K = K
    simpa only [pow_two] using hsq.symm
  obtain ⟨e, he, hspan⟩ := (Ideal.isIdempotentElem_iff_of_fg K hfg).mp hid
  exact ⟨e, he, hspan.symm⟩

end HenselianEtaleAugmentation

end

section

namespace AdicModules

open scoped BigOperators


variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

private theorem envelope_fg_sup (D E : Subalgebra R A)
    (hD : D.toSubmodule.FG) (hE : E.toSubmodule.FG) :
    (D ⊔ E).toSubmodule.FG := by
  have hmul : (D ⊔ E).toSubmodule = D.toSubmodule * E.toSubmodule := by
    simpa only [Algebra.adjoin_union, Algebra.adjoin_eq] using
      (Algebra.adjoin_union_coe_submodule
        (R := R) (s := (D : Set A)) (t := (E : Set A)))
  rw [hmul]
  exact hD.mul hE

private theorem envelope_fg_finset_sup {ι : Type w}
    (s : Finset ι) (D : ι → Subalgebra R A)
    (hD : ∀ i ∈ s, (D i).toSubmodule.FG) :
    (s.sup D).toSubmodule.FG := by
  classical
  revert hD
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using (Subalgebra.fg_bot_toSubmodule (R := R) (A := A))
  | @insert i s hi ih =>
    intro hD
    rw [Finset.sup_insert]
    exact envelope_fg_sup _ _ (hD i (by simp))
      (ih (fun j hj => hD j (by simp [hj])))

/-- Glue into the range of the actual localization map, not an abstract copy. -/
private theorem envelope_awayMap_bijective {ι : Type w} [Fintype ι]
    (D : Subalgebra R A) (f : ι → D) (r : ι → R) (g : D)
    (hg : g = ∑ i, algebraMap R D (r i) * f i)
    (hclear : ∀ i a, ∃ n : ℕ, D.val (f i) ^ n * a ∈ D) :
    Function.Bijective (Localization.awayMap D.val.toRingHom g) := by
  classical
  let B := Localization.Away g
  let C := Localization.Away (D.val g)
  let h : B →ₐ[R] C := Localization.awayMapₐ D.val g
  have hmap (d : D) : h (algebraMap D B d) = algebraMap A C (D.val d) := by
    change IsLocalization.Away.map B C D.val.toRingHom g
      (algebraMap D B d) = algebraMap A C (D.val d)
    rw [IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  let u : B := IsLocalization.Away.invSelf g
  let v : C := h u
  have hv : algebraMap A C (D.val g) * v = 1 := by
    simpa only [map_mul, map_one, hmap] using
      congrArg h (IsLocalization.Away.mul_invSelf (S := B) g)
  have hv_mem : v ∈ h.range := ⟨u, rfl⟩
  have hs (i : ι) : algebraMap A C (D.val (f i)) ∈ h.range :=
    ⟨algebraMap D B (f i), hmap (f i)⟩
  have hl (i : ι) : algebraMap R C (r i) * v ∈ h.range := by
    refine ⟨algebraMap R B (r i) * u, ?_⟩
    exact (map_mul h _ _).trans
      (congrArg (fun x : C => x * v) (h.commutes (r i)))
  have hgB : algebraMap D B g =
      ∑ i, algebraMap R B (r i) * algebraMap D B (f i) := by
    simpa only [map_sum, map_mul, ← IsScalarTower.algebraMap_apply R D B] using
      congrArg (algebraMap D B) hg
  have hgC : algebraMap A C (D.val g) =
      ∑ i, algebraMap R C (r i) * algebraMap A C (D.val (f i)) := by
    simpa only [map_sum, map_mul, hmap, AlgHom.commutes] using congrArg h hgB
  have hsum : (∑ i, (algebraMap R C (r i) * v) *
      algebraMap A C (D.val (f i))) = 1 := by
    calc
      _ = (∑ i, algebraMap R C (r i) *
          algebraMap A C (D.val (f i))) * v := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_right_comm _ _ _
      _ = algebraMap A C (D.val g) * v := by rw [hgC]
      _ = 1 := hv
  have hnum (a : A) : algebraMap A C a ∈ h.range := by
    apply h.range.mem_of_finsetSum_eq_one_of_pow_smul_mem Finset.univ
      (fun i => algebraMap A C (D.val (f i)))
      (fun i => algebraMap R C (r i) * v) hsum hs hl
    intro i
    obtain ⟨n, hn⟩ := hclear i a
    refine ⟨n, ?_⟩
    change algebraMap A C (D.val (f i)) ^ n * algebraMap A C a ∈ h.range
    refine ⟨algebraMap D B ⟨D.val (f i) ^ n * a, hn⟩, ?_⟩
    change h (algebraMap D B ⟨D.val (f i) ^ n * a, hn⟩) = _
    rw [hmap]
    change algebraMap A C (D.val (f i) ^ n * a) = _
    rw [map_mul, map_pow]
  have hsurj : Function.Surjective h := by
    intro x
    obtain ⟨⟨a, m⟩, heq⟩ :=
      IsLocalization.surj (Submonoid.powers (D.val g)) x
    obtain ⟨n, hn⟩ := m.property
    have heq' : x * algebraMap A C (D.val g) ^ n = algebraMap A C a := by
      simpa only [← hn, map_pow] using heq
    have hpow : algebraMap A C (D.val g) ^ n * v ^ n = 1 := by
      rw [← mul_pow, hv, one_pow]
    have hx : x = algebraMap A C a * v ^ n := by
      calc
        x = x * (algebraMap A C (D.val g) ^ n * v ^ n) := by rw [hpow, mul_one]
        _ = (x * algebraMap A C (D.val g) ^ n) * v ^ n := (mul_assoc _ _ _).symm
        _ = algebraMap A C a * v ^ n := by rw [heq']
    have hx_mem : x ∈ h.range := by
      rw [hx]
      exact h.range.mul_mem (hnum a) (h.range.pow_mem hv_mem n)
    exact hx_mem
  change Function.Bijective h
  exact ⟨IsLocalization.Away.mapₐ_injective_of_injective g
    Subtype.val_injective, hsurj⟩

/-- An envelope for the whole specified quotient point; all scalar actions are
canonical, and the localization morphism is the map induced by inclusion. -/
private theorem exists_finite_envelope [Algebra.Etale R A]
    (I : Ideal R) (φ : A →ₐ[R] R ⧸ I) :
    ∃ D : Subalgebra R A, Module.Finite R D ∧ ∃ g : D,
      φ (D.val g) = 1 ∧
      Function.Bijective (Localization.awayMap D.val.toRingHom g) := by
  classical
  have hlocal (q : PrimeSpectrum (R ⧸ I)) :
      ∃ D : Subalgebra R A, D.toSubmodule.FG ∧ ∃ f : D,
        φ (D.val f) ∉ q.asIdeal ∧
        Function.Bijective (Localization.awayMap D.val.toRingHom f) := by
    let p : Ideal A := q.asIdeal.comap φ.toRingHom
    have : p.IsPrime := by dsimp [p]; infer_instance
    obtain ⟨D, hD, f, hf, hb⟩ :=
      Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
        (R := R) p
    exact ⟨D, hD, f, hf, hb⟩
  choose D hD f hf hb using hlocal
  let z : PrimeSpectrum (R ⧸ I) → R ⧸ I := fun q => φ ((D q).val (f q))
  have hz : Ideal.span (Set.range z) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let q : PrimeSpectrum (R ⧸ I) := ⟨m, hm.isPrime⟩
    exact hf q (hle (Ideal.subset_span ⟨q, rfl⟩))
  have hone : (1 : R ⧸ I) ∈ Submodule.span (R ⧸ I) (Set.range z) := by
    change (1 : R ⧸ I) ∈ Ideal.span (Set.range z)
    rw [hz]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hone
  let J := ↥c.support
  let r : J → R := fun j =>
    Classical.choose (Ideal.Quotient.mk_surjective (c j.1))
  have hr (j : J) : Ideal.Quotient.mk I (r j) = c j.1 :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective (c j.1))
  have hc' : (∑ j : J, c j.1 * z j.1) = 1 := by
    calc
      _ = ∑ q ∈ c.support, c q * z q := Finset.sum_coe_sort _ _
      _ = 1 := by simpa only [Finsupp.sum, smul_eq_mul] using hc
  let E : Subalgebra R A := Finset.univ.sup (fun j : J => D j.1)
  have hle (j : J) : D j.1 ≤ E :=
    Finset.le_sup (s := Finset.univ) (f := fun j : J => D j.1) (Finset.mem_univ j)
  have hE : E.toSubmodule.FG :=
    envelope_fg_finset_sup Finset.univ (fun j : J => D j.1)
      (fun j _ => hD j.1)
  let t : J → E := fun j => ⟨(D j.1).val (f j.1), hle j (f j.1).property⟩
  let g : E := ∑ j, algebraMap R E (r j) * t j
  refine ⟨E, ⟨(Submodule.fg_top _).mpr hE⟩, g, ?_, ?_⟩
  · have hφ (j : J) :
        φ (E.val (algebraMap R E (r j) * t j)) = c j.1 * z j.1 := by
      simp only [map_mul, AlgHom.commutes]
      change Ideal.Quotient.mk I (r j) * z j.1 = c j.1 * z j.1
      rw [hr]
    calc
      φ (E.val g) = ∑ j : J, φ (E.val (algebraMap R E (r j) * t j)) := by
        simp only [g, map_sum]
      _ = ∑ j : J, c j.1 * z j.1 := Finset.sum_congr rfl (fun j _ => hφ j)
      _ = 1 := hc'
  · apply envelope_awayMap_bijective E t r g rfl
    intro j a
    obtain ⟨b, n, hn⟩ :=
      (Localization.awayMap_surjective_iff.mp (hb j.1).surjective) a
    refine ⟨n, ?_⟩
    change (D j.1).val (f j.1) ^ n * a ∈ E
    change (D j.1).val b = (D j.1).val (f j.1) ^ n * a at hn
    rw [← hn]
    exact hle j b.property

end AdicModules

end

section

namespace AdicModules

private theorem algebraMap_bijective_of_finite_flat_quotient
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Flat R B]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    (h : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R B))
        (algebraMap R B) Ideal.le_comap_map)) :
    Function.Bijective (algebraMap R B) := by
  have hsurj : Function.Surjective (algebraMap R B) := by
    apply LinearMap.surjective_of_surjective_comp_mkQ
      (Algebra.ofId R B).toLinearMap I hI
    intro bbar
    obtain ⟨b, rfl⟩ := (I • (⊤ : Submodule R B)).mkQ_surjective bbar
    obtain ⟨rbar, hr⟩ := h.2 (Ideal.Quotient.mk (I.map (algebraMap R B)) b)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective rbar
    refine ⟨r, ?_⟩
    change (Submodule.Quotient.mk (algebraMap R B r) :
      B ⧸ (I • (⊤ : Submodule R B))) = Submodule.Quotient.mk b
    apply (Submodule.Quotient.eq _).2
    rw [Ideal.smul_top_eq_map]
    change algebraMap R B r - b ∈ I.map (algebraMap R B)
    exact Ideal.Quotient.eq.mp (by
      simpa only [Ideal.quotientMap_mk] using hr)
  have hker : RingHom.ker (algebraMap R B) ≤ I := by
    intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply h.1
    simp only [Ideal.quotientMap_mk, RingHom.mem_ker.mp hr, map_zero]
  let : Module.FaithfullyFlat R B := {
    toFlat := inferInstance
    submodule_ne_top := by
      intro m hm htop
      have hJac : (⊥ : Ideal R).jacobson ≤ m := sInf_le ⟨bot_le, hm⟩
      have hker_m : RingHom.ker (algebraMap R B) ≤ m :=
        hker.trans (hI.trans hJac)
      have hone : (1 : B) ∈ m.map (algebraMap R B) := by
        have hmem : (1 : B) ∈ m • (⊤ : Submodule R B) := by
          rw [htop]
          trivial
        rw [Ideal.smul_top_eq_map] at hmem
        exact hmem
      obtain ⟨r, hr, hfr⟩ :=
        (Ideal.mem_map_iff_of_surjective (algebraMap R B) hsurj).1 hone
      have hrsub : r - 1 ∈ m := hker_m (RingHom.mem_ker.mpr (by
        rw [map_sub, hfr, map_one, sub_self]))
      apply hm.ne_top
      apply (Ideal.eq_top_iff_one m).2
      simpa only [sub_sub_cancel] using m.sub_mem hr hrsub }
  exact ⟨FaithfulSMul.algebraMap_injective R B, hsurj⟩

end AdicModules

end

section

namespace Algebra.Unramified

private theorem comp_injective_of_le_jacobson_bot
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Unramified R A]
    (I : Ideal B) (hI : I ≤ Ideal.jacobson ⊥) :
    Function.Injective ((Ideal.Quotient.mkₐ R I).comp :
      (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) := by
  classical
  intro f g h
  have hfg : (⊤ : Subalgebra R A).FG := Algebra.FiniteType.out
  obtain ⟨s, hsfin, hs⟩ := Subalgebra.fg_def.mp hfg
  -- The finite difference ideal depends only on algebra generators, not a module basis.
  let D : Ideal B := Ideal.span ((fun a : A => f a - g a) '' s)
  have hDfg : (D : Submodule B B).FG :=
    Submodule.fg_span (hsfin.image _)
  have hDI : D ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, _, rfl⟩
    exact Ideal.Quotient.eq.mp (DFunLike.congr_fun h a)
  have hmodD : (Ideal.Quotient.mkₐ R D).comp f =
      (Ideal.Quotient.mkₐ R D).comp g := by
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro a ha
    change Ideal.Quotient.mk D (f a) = Ideal.Quotient.mk D (g a)
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span ⟨a, ha, rfl⟩)
  have hd (a : A) : f a - g a ∈ D :=
    Ideal.Quotient.eq.mp (DFunLike.congr_fun hmodD a)
  -- Pass to B/D², where the image of D is square-zero.
  let q : B →ₐ[R] B ⧸ (D ^ 2) := Ideal.Quotient.mkₐ R (D ^ 2)
  let J : Ideal (B ⧸ (D ^ 2)) := D.map (Ideal.Quotient.mk (D ^ 2))
  have hJ : J ^ 2 = ⊥ := by
    change (D.map (Ideal.Quotient.mk (D ^ 2))) ^ 2 = ⊥
    rw [← Ideal.map_pow]
    exact Ideal.map_mk_eq_bot_of_le le_rfl
  have hq : q.comp f = q.comp g := by
    apply Algebra.FormallyUnramified.comp_injective J hJ
    apply AlgHom.ext
    intro a
    change Ideal.Quotient.mk J (q (f a)) = Ideal.Quotient.mk J (q (g a))
    apply Ideal.Quotient.eq.mpr
    have ha := Ideal.mem_map_of_mem (Ideal.Quotient.mk (D ^ 2)) (hd a)
    simpa only [q, J, Ideal.Quotient.mkₐ_eq_mk, map_sub] using ha
  have hDsq : D ≤ D ^ 2 := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, _, rfl⟩
    exact Ideal.Quotient.eq.mp (DFunLike.congr_fun hq a)
  -- Jacobson Nakayama applies to D as a finitely generated B-submodule of B.
  have hDzero : D = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot D D hDfg
    · simpa only [Ideal.smul_eq_mul, pow_two] using hDsq
    · exact hDI.trans hI
  apply AlgHom.ext
  intro a
  apply sub_eq_zero.mp
  simpa only [hDzero, Submodule.mem_bot] using hd a

end Algebra.Unramified

end

section

namespace HenselianEtaleQuotient

section Quotient

variable {R : Type u} {D : Type v} [CommRing R] [CommRing D] [Algebra R D]

/-- The specified quotient action agrees with the original R-action. -/
private theorem quotient_scalar_tower (I : Ideal R) :
    let : Algebra (R ⧸ I) (D ⧸ I.map (algebraMap R D)) :=
      Ideal.Quotient.algebraQuotientOfLEComap
        (Ideal.le_comap_map : I ≤ (I.map (algebraMap R D)).comap (algebraMap R D))
    IsScalarTower R (R ⧸ I) (D ⧸ I.map (algebraMap R D)) := by
  let : Algebra (R ⧸ I) (D ⧸ I.map (algebraMap R D)) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.le_comap_map : I ≤ (I.map (algebraMap R D)).comap (algebraMap R D))
  exact IsScalarTower.of_algebraMap_eq'
    (Ideal.quotientMap_comp_mk
      (Ideal.le_comap_map : I ≤ (I.map (algebraMap R D)).comap (algebraMap R D))).symm

/-- Descend the given map, and check its quotient-base algebra property. -/
private theorem exists_quotient_augmentation (I : Ideal R) (φ : D →ₐ[R] R ⧸ I) :
    let : Algebra (R ⧸ I) (D ⧸ I.map (algebraMap R D)) :=
      Ideal.Quotient.algebraQuotientOfLEComap
        (Ideal.le_comap_map : I ≤ (I.map (algebraMap R D)).comap (algebraMap R D))
    ∃ p : (D ⧸ I.map (algebraMap R D)) →ₐ[R ⧸ I] R ⧸ I,
      ∀ d : D, p (Ideal.Quotient.mk (I.map (algebraMap R D)) d) = φ d := by
  let T := R ⧸ I
  let J := I.map (algebraMap R D)
  let S := D ⧸ J
  let : Algebra T S := Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.le_comap_map : I ≤ J.comap (algebraMap R D))
  have hkill : ∀ d : D, d ∈ J → φ d = 0 := by
    have hle : J ≤ RingHom.ker φ.toRingHom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      change φ (algebraMap R D r) = 0
      rw [φ.commutes]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
    exact fun d hd => hle hd
  let f : S →+* T := Ideal.Quotient.lift J φ.toRingHom hkill
  let p : S →ₐ[T] T :=
    { toRingHom := f
      commutes' := by
        rintro ⟨r⟩
        have hcoeff : algebraMap T S (Ideal.Quotient.mk I r) =
            Ideal.Quotient.mk J (algebraMap R D r) := Ideal.quotientMap_mk
        change f (algebraMap T S (Ideal.Quotient.mk I r)) = _
        rw [hcoeff]
        change φ (algebraMap R D r) = algebraMap T T (Ideal.Quotient.mk I r)
        simp }
  refine ⟨p, ?_⟩
  intro d
  rfl

/-- Finiteness uses the finite quotient and the actual R/T/S tower. -/
private theorem quotient_finite (I : Ideal R) [Module.Finite R D] :
    let : Algebra (R ⧸ I) (D ⧸ I.map (algebraMap R D)) :=
      Ideal.Quotient.algebraQuotientOfLEComap
        (Ideal.le_comap_map : I ≤ (I.map (algebraMap R D)).comap (algebraMap R D))
    Module.Finite (R ⧸ I) (D ⧸ I.map (algebraMap R D)) := by
  let T := R ⧸ I
  let J := I.map (algebraMap R D)
  let S := D ⧸ J
  let : Algebra T S := Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.le_comap_map : I ≤ J.comap (algebraMap R D))
  have : IsScalarTower R T S := quotient_scalar_tower (D := D) I
  let q : D →ₐ[R] S := Ideal.Quotient.mkₐ R J
  have : Module.Finite R S :=
    Module.Finite.of_surjective q.toLinearMap (Ideal.Quotient.mkₐ_surjective R J)
  exact Module.Finite.of_restrictScalars_finite R T S

end Quotient

section Localization

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Descend formal unramifiedness along the canonical quotient-away map. -/
private theorem quotient_away_formallyUnramified [Algebra.Etale R A]
    (I : Ideal R) (D : Subalgebra R A) (g : D)
    (hbij : Function.Bijective (Localization.awayMap D.val.toRingHom g)) :
    let T := R ⧸ I
    let J := I.map (algebraMap R D)
    let S := D ⧸ J
    let : Algebra T S := Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.le_comap_map : I ≤ J.comap (algebraMap R D))
    let U := Localization.Away (Ideal.Quotient.mk J g)
    let : Algebra T U := ((algebraMap S U).comp (algebraMap T S)).toAlgebra
    Algebra.FormallyUnramified T U := by
  let T := R ⧸ I
  let J := I.map (algebraMap R D)
  let S := D ⧸ J
  let : Algebra T S := Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.le_comap_map : I ≤ J.comap (algebraMap R D))
  have : IsScalarTower R T S := quotient_scalar_tower (D := D) I
  let U := Localization.Away (Ideal.Quotient.mk J g)
  have : IsScalarTower T S U := inferInstance
  have hcoeff (r : R) : algebraMap T S (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk J (algebraMap R D r) := Ideal.quotientMap_mk
  have hcoeffU (r : R) : algebraMap T U (Ideal.Quotient.mk I r) =
      algebraMap R U r := by
    change algebraMap S U (algebraMap T S (Ideal.Quotient.mk I r)) = _
    rw [hcoeff]
    exact (IsScalarTower.algebraMap_apply R S U r).symm
  have : IsScalarTower R T U := inferInstance
  let e : Localization.Away g ≃ₐ[R] Localization.Away (D.val g) :=
    AlgEquiv.ofBijective (Localization.awayMapₐ D.val g) hbij
  have : Algebra.Etale R (Localization.Away (D.val g)) := inferInstance
  have : Algebra.FormallyUnramified R (Localization.Away (D.val g)) := inferInstance
  have : Algebra.FormallyUnramified R (Localization.Away g) :=
    Algebra.FormallyUnramified.of_equiv e.symm
  let q : D →ₐ[R] S := Ideal.Quotient.mkₐ R J
  have : IsLocalization.Away (q g) U := by
    change IsLocalization.Away (Ideal.Quotient.mk J g) U
    infer_instance
  let F : Localization.Away g →ₐ[R] U := Localization.awayMapₐ q g
  have hF : Function.Surjective F :=
    IsLocalization.Away.mapₐ_surjective_of_surjective
      (Aₚ := Localization.Away g) (Bₚ := U) (f := q) g
      (Ideal.Quotient.mkₐ_surjective R J)
  have : Algebra.FormallyUnramified R U :=
    Algebra.FormallyUnramified.of_surjective F hF
  have hU : Algebra.FormallyUnramified T U :=
    Algebra.FormallyUnramified.of_restrictScalars R T U
  have hα : (inferInstance : Algebra T U) =
      ((algebraMap S U).comp (algebraMap T S)).toAlgebra := by
    apply Algebra.algebra_ext
    intro t
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective t
    change algebraMap T U (Ideal.Quotient.mk I r) =
      algebraMap S U (algebraMap T S (Ideal.Quotient.mk I r))
    rw [hcoeffU, hcoeff]
    exact IsScalarTower.algebraMap_apply R S U r
  change @Algebra.FormallyUnramified T U _ _
    ((algebraMap S U).comp (algebraMap T S)).toAlgebra
  exact (congrArg (fun α : Algebra T U =>
    @Algebra.FormallyUnramified T U _ _ α) hα).mp hU

end Localization

end HenselianEtaleQuotient

end

section

namespace AdicModules

private theorem exists_selectedComponent_algEquiv
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (D : Subalgebra R A) (g e : D)
    (hbij : Function.Bijective (Localization.awayMap D.val.toRingHom g))
    (he : IsIdempotentElem e) (hdiv : g ∣ e) :
    ∃ δ : (D ⧸ Ideal.span {1 - e}) ≃ₐ[R] Localization.Away (D.val e),
      ∀ d : D, δ (Ideal.Quotient.mk (Ideal.span {1 - e}) d) =
        algebraMap A (Localization.Away (D.val e)) (D.val d) := by
  let : IsLocalization.Away e (D ⧸ Ideal.span {1 - e}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  let sourceEquiv : (D ⧸ Ideal.span {1 - e}) ≃ₐ[D] Localization.Away e :=
    IsLocalization.algEquiv (Submonoid.powers e) _ _
  let f : Localization.Away e →ₐ[R] Localization.Away (D.val e) :=
    IsLocalization.Away.mapₐ _ _ D.val e
  have hf : Function.Bijective f :=
    Localization.awayMap_bijective_of_dvd D.val.toRingHom hdiv hbij
  refine ⟨(sourceEquiv.restrictScalars R).trans (AlgEquiv.ofBijective f hf), ?_⟩
  intro d
  change IsLocalization.Away.map (Localization.Away e)
    (Localization.Away (D.val e)) D.val.toRingHom e
    (sourceEquiv (algebraMap D (D ⧸ Ideal.span {1 - e}) d)) = _
  rw [sourceEquiv.commutes]
  dsimp only [IsLocalization.Away.map]
  rw [IsLocalization.map_eq]
  rfl

private theorem selectedComponent_etale
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] (D : Subalgebra R A) (g e : D)
    (hbij : Function.Bijective (Localization.awayMap D.val.toRingHom g))
    (he : IsIdempotentElem e) (hdiv : g ∣ e) :
    Algebra.Etale R (D ⧸ Ideal.span {1 - e}) := by
  obtain ⟨δ, _⟩ := exists_selectedComponent_algEquiv D g e hbij he hdiv
  exact Algebra.Etale.of_equiv δ.symm

private theorem selectedComponent_flat
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] (D : Subalgebra R A) (g e : D)
    (hbij : Function.Bijective (Localization.awayMap D.val.toRingHom g))
    (he : IsIdempotentElem e) (hdiv : g ∣ e) :
    Module.Flat R (D ⧸ Ideal.span {1 - e}) := by
  let : Algebra.Etale R (D ⧸ Ideal.span {1 - e}) :=
    selectedComponent_etale D g e hbij he hdiv
  infer_instance

end AdicModules

end

namespace HenselianRing

/-- A specified quotient point of an étale algebra over a Henselian pair lifts
uniquely through the canonical quotient map.

For existence, see the implication (1) ⇒ (2) of
[Stacks Project, Lemma 15.11.6, tag 09XI](https://stacks.math.columbia.edu/tag/09XI).
The unique-lift formulation additionally uses rigidity of étale sections
congruent modulo an ideal contained in the Jacobson radical; uniqueness
is not asserted in item (2) of that reference. -/
theorem existsUnique_algHom_lift_of_etale
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {I : Ideal R} [HenselianRing R I] [Algebra.Etale R A]
    (φ : A →ₐ[R] (R ⧸ I)) :
    ∃! ψ : A →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp ψ = φ := by
  classical
  obtain ⟨D, hD, g, hg, hbij⟩ := AdicModules.exists_finite_envelope I φ
  let : Module.Finite R D := hD
  let T := R ⧸ I
  let J : Ideal D := I.map (algebraMap R D)
  let S := D ⧸ J
  let : Algebra T S := Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.le_comap_map : I ≤ J.comap (algebraMap R D))
  have : IsScalarTower R T S := HenselianEtaleQuotient.quotient_scalar_tower I
  let pD : D →ₐ[R] T := φ.comp D.val
  obtain ⟨p, hp⟩ := HenselianEtaleQuotient.exists_quotient_augmentation I pD
  have : Module.Finite T S := HenselianEtaleQuotient.quotient_finite I
  let g₀ : S := Ideal.Quotient.mk J g
  let U := Localization.Away g₀
  have hα : ((algebraMap S U).comp (algebraMap T S)).toAlgebra =
      (inferInstance : Algebra T U) :=
    Algebra.algebra_ext _ _ (fun _ => rfl)
  have hU : @Algebra.FormallyUnramified T U _ _
      ((algebraMap S U).comp (algebraMap T S)).toAlgebra :=
    HenselianEtaleQuotient.quotient_away_formallyUnramified I D g hbij
  have : Algebra.FormallyUnramified T U :=
    (congrArg (fun α : Algebra T U =>
      @Algebra.FormallyUnramified T U _ _ α) hα).mp hU
  have hpg : p g₀ = 1 := (hp g).trans hg
  obtain ⟨k, hk, hkspan⟩ :=
    HenselianEtaleAugmentation.exists_idempotent_span_augmentation_ker p g₀ hpg
  have hpk : p k = 0 := by
    have hkK : k ∈ RingHom.ker p.toRingHom := by
      rw [← hkspan]
      exact Ideal.mem_span_singleton_self k
    exact hkK
  have : HenselianRing D J := HenselianRing.map_of_isIntegral I
    (algebraMap R D) (algebraMap_isIntegral_iff.mpr inferInstance)
  obtain ⟨e, ⟨he, he₀⟩, _⟩ :=
    HenselianRing.existsUnique_isIdempotentElem J hk.one_sub
  have hpe : pD e = 1 := by
    rw [← hp e, he₀, map_sub, map_one, hpk, sub_zero]
  let H : Ideal D := Ideal.span {1 - e}
  let B := D ⧸ H
  let q : D →ₐ[R] B := Ideal.Quotient.mkₐ R H
  have hqe : q e = 1 := by
    have hzero : q (1 - e) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (1 - e))
    have hzero' : 1 - q e = 0 := by
      simpa only [map_sub, map_one] using hzero
    exact (sub_eq_zero.mp hzero').symm
  have hH : H ≤ RingHom.ker pD.toRingHom := by
    apply Ideal.span_le.mpr
    intro d hd
    obtain rfl := Set.mem_singleton_iff.mp hd
    change pD (1 - e) = 0
    rw [map_sub, map_one, hpe, sub_self]
  let β : B →ₐ[R] T := Ideal.Quotient.liftₐ H pD (fun d hd => hH hd)
  have hβq (d : D) : β (q d) = pD d := rfl
  have : Module.Finite R B :=
    Module.Finite.of_surjective q.toLinearMap (Ideal.Quotient.mkₐ_surjective R H)
  let JB : Ideal B := I.map (algebraMap R B)
  have hJmap : J.map q.toRingHom = JB := by
    change (I.map (algebraMap R D)).map q.toRingHom = I.map (algebraMap R B)
    rw [Ideal.map_map]
    congr 1
  have hJB : JB ≤ RingHom.ker β.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change β (algebraMap R B r) = 0
    rw [β.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  -- The chosen augmentation, not an arbitrary residue isomorphism, determines this kernel.
  have hkerβ : RingHom.ker β.toRingHom = JB := by
    apply le_antisymm
    · intro b hb
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mkₐ_surjective R H b
      have hpd : p (Ideal.Quotient.mk J d) = 0 := by
        rw [hp]
        exact (hβq d).symm.trans hb
      have hdK : Ideal.Quotient.mk J d ∈ Ideal.span {k} := by
        rw [hkspan]
        exact hpd
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hdK
      obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective s
      have hdJ : d - t * (1 - e) ∈ J := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, map_mul, map_sub, map_one, he₀, sub_sub_cancel, ht, hs, sub_self]
      have hmem : q (d - t * (1 - e)) ∈ JB := by
        rw [← hJmap]
        exact Ideal.mem_map_of_mem q.toRingHom hdJ
      simpa only [map_sub, map_mul, map_one, hqe, sub_self, mul_zero, sub_zero] using hmem
    · exact hJB
  -- This is literally the quotient of the coefficient map R → B.
  let u : T →+* B ⧸ JB := Ideal.quotientMap JB (algebraMap R B) Ideal.le_comap_map
  let β₀ : B ⧸ JB →+* T := Ideal.Quotient.lift JB β.toRingHom (fun b hb => hJB hb)
  have hβ₀inj : Function.Injective β₀ :=
    (Ideal.injective_lift_iff (fun b hb => hJB hb)).mpr hkerβ
  have hβ₀u (t : T) : β₀ (u t) = t := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective t
    change β (algebraMap R B r) = Ideal.Quotient.mk I r
    exact β.commutes r
  have hcoef : Function.Bijective u := by
    constructor
    · intro x y hxy
      calc
        x = β₀ (u x) := (hβ₀u x).symm
        _ = β₀ (u y) := congrArg β₀ hxy
        _ = y := hβ₀u y
    · intro z
      exact ⟨β₀ z, hβ₀inj (hβ₀u (β₀ z))⟩
  have : HenselianRing B JB := HenselianRing.map_of_isIntegral I
    (algebraMap R B) (algebraMap_isIntegral_iff.mpr inferInstance)
  have hβg : β (q g) = 1 := (hβq g).trans hg
  have hgJB : q g - 1 ∈ JB := by
    rw [← hkerβ]
    change β (q g - 1) = 0
    rw [map_sub, map_one, hβg, sub_self]
  have hgunit : IsUnit (q g) := Ideal.isUnit_of_sub_one_mem_jacobson_bot (q g)
    ((HenselianRing.jac (R := B) (I := JB)) hgJB)
  let : IsLocalization.Away e B :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  obtain ⟨n, hn⟩ := (IsLocalization.Away.algebraMap_isUnit_iff (S := B) e).mp hgunit
  have hdiv : g ∣ e := by
    have hn' : g ∣ e ^ (n + 1) := by
      rw [pow_succ]
      exact dvd_mul_of_dvd_left hn e
    simpa only [he.pow_succ_eq n] using hn'
  obtain ⟨δ, hδ⟩ := AdicModules.exists_selectedComponent_algEquiv D g e hbij he hdiv
  have : Module.Flat R B := AdicModules.selectedComponent_flat D g e hbij he hdiv
  have hRB : Function.Bijective (algebraMap R B) :=
    AdicModules.algebraMap_bijective_of_finite_flat_quotient I
      (HenselianRing.jac (R := R) (I := I)) hcoef
  let E : R ≃ₐ[R] B := AlgEquiv.ofBijective (Algebra.ofId R B) hRB
  let Ae := Localization.Away (D.val e)
  let η : A →ₐ[R] Ae := IsScalarTower.toAlgHom R A Ae
  let θ : A →ₐ[R] B := δ.symm.toAlgHom.comp η
  have hφeunit : IsUnit (φ (D.val e)) := by
    change IsUnit (pD e)
    rw [hpe]
    exact isUnit_one
  let φe : Ae →ₐ[R] T := IsLocalization.Away.liftAlgHom (D.val e) hφeunit
  have hφeη (a : A) : φe (η a) = φ a :=
    IsLocalization.Away.lift_eq (D.val e) hφeunit a
  have hφeδ : φe.comp δ.toAlgHom = β := by
    apply AlgHom.ext
    intro b
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective b
    change φe (δ (Ideal.Quotient.mk H d)) = β (q d)
    rw [hδ d, hβq]
    exact IsLocalization.Away.lift_eq (D.val e) hφeunit (D.val d)
  have hβθ : β.comp θ = φ := by
    apply AlgHom.ext
    intro a
    change β (δ.symm (η a)) = φ a
    calc
      β (δ.symm (η a)) = φe (δ (δ.symm (η a))) :=
        (DFunLike.congr_fun hφeδ (δ.symm (η a))).symm
      _ = φ a := by rw [δ.apply_symm_apply]; exact hφeη a
  let ψ : A →ₐ[R] R := E.symm.toAlgHom.comp θ
  have hψ : (Ideal.Quotient.mkₐ R I).comp ψ = φ := by
    apply AlgHom.ext
    intro a
    calc
      Ideal.Quotient.mk I (ψ a) = β (E (ψ a)) := (β.commutes (ψ a)).symm
      _ = β (θ a) := by
        change β (E (E.symm (θ a))) = β (θ a)
        rw [E.apply_symm_apply]
      _ = φ a := DFunLike.congr_fun hβθ a
  refine ⟨ψ, hψ, ?_⟩
  intro χ hχ
  exact Algebra.Unramified.comp_injective_of_le_jacobson_bot I
    (HenselianRing.jac (R := R) (I := I)) (hχ.trans hψ.symm)

end HenselianRing
