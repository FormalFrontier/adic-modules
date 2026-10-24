/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.HenselianCriterion
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.Algebra.GroupWithZero.Basic

/-!
# Henselian pairs under integral and surjective homomorphisms

An integral homomorphism of commutative rings sends a Henselian pair to the pair
formed by extending the ideal. In particular, this holds for surjective homomorphisms.
If every element of a surjection's kernel is nilpotent, the source pair is Henselian
if and only if its image pair is Henselian. Extension along an integral faithfully flat
homomorphism also preserves and reflects the Henselian-pair property.

The integral case uses unique idempotent lifting in finite algebras. Finite subalgebras
are chosen to contain the coefficients witnessing ideal membership; no
extension-contraction identity is needed.

The pair predicate is Mathlib's `HenselianRing`. This module uses Mathlib's
Henselian-pair formalization by Johan Commelin and ideal-map API by Kenny Lau.

## References

* The Stacks Project Authors, *The Stacks Project*, Section 15.11, "Henselian pairs":
  [Lemma 15.11.6 (Tag 09XI)](https://stacks.math.columbia.edu/tag/09XI), the finite-algebra
  idempotent-lifting criterion;
  [Lemma 15.11.8 (Tag 09XK)](https://stacks.math.columbia.edu/tag/09XK), integral-map
  transport; [Lemma 15.11.9 (Tag 0DYD)](https://stacks.math.columbia.edu/tag/0DYD),
  nested-ideal transitivity; and
  [Lemma 15.11.2 (Tag 0ALI)](https://stacks.math.columbia.edu/tag/0ALI), locally
  nilpotent ideals.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace HenselianRing

private theorem exists_finite_subalgebra_mem_map {R : Type u} {C : Type v}
    [CommRing R] [CommRing C] [Algebra R C] [Algebra.IsIntegral R C]
    (I : Ideal R) (s : Finset C) (x : C) (hx : x ∈ I.map (algebraMap R C)) :
    ∃ D : Subalgebra R C, Module.Finite R D ∧ (∀ z ∈ s, z ∈ D) ∧
      ∃ y : D, (y : C) = x ∧ y ∈ I.map (algebraMap R D) := by
  classical
  change x ∈ Submodule.span C ((algebraMap R C) '' (I : Set R)) at hx
  rw [Set.image_eq_range] at hx
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  let t := s ∪ f.support.image f
  let D := Algebra.adjoin R (t : Set C)
  have hcoeff (i : I) : f i ∈ D := by
    by_cases hi : i ∈ f.support
    · exact Algebra.subset_adjoin (Finset.mem_union_right s (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact D.zero_mem
  let g (i : I) : D := ⟨f i, hcoeff i⟩
  let y : D := ∑ i ∈ f.support, g i * algebraMap R D (i : R)
  refine ⟨D, ?_, ?_, y, ?_, ?_⟩
  · exact Algebra.finite_adjoin_of_finite_of_isIntegral (Finset.finite_toSet t)
      (fun z _ => Algebra.IsIntegral.isIntegral z)
  · intro z hz
    exact Algebra.subset_adjoin (Finset.mem_union_left _ hz)
  · change D.val y = x
    dsimp only [y]
    simp only [map_sum, map_mul, AlgHom.commutes]
    exact hf
  · exact Submodule.sum_mem _ fun i _ =>
      Ideal.mul_mem_left _ (g i) (Ideal.mem_map_of_mem _ i.property)

private theorem existsUnique_isIdempotentElem_sub_mem_map
    {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.IsIntegral R C] (I : Ideal R) [HenselianRing R I]
    (c : C) (hc : c * c - c ∈ I.map (algebraMap R C)) :
    ∃! e : C, IsIdempotentElem e ∧ e - c ∈ I.map (algebraMap R C) := by
  classical
  obtain ⟨D, hD, hDs, y, hy, hymem⟩ :=
    exists_finite_subalgebra_mem_map I {c} (c * c - c) hc
  have : Module.Finite R D := hD
  let cD : D := ⟨c, hDs c (by simp)⟩
  have hy' : y = cD * cD - cD := Subtype.ext hy
  have hcD : cD * cD - cD ∈ I.map (algebraMap R D) := by
    simpa only [hy'] using hymem
  have hc0D : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R D)) cD) := by
    rw [isIdempotentElem_iff, ← map_mul, Ideal.Quotient.eq]
    exact hcD
  obtain ⟨eD, heD, _⟩ := HenselianRing.existsUnique_isIdempotentElem_map I hc0D
  have heDmem : eD - cD ∈ I.map (algebraMap R D) :=
    (Ideal.Quotient.eq (I := I.map (algebraMap R D))).mp heD.2
  let e : C := eD
  have he : IsIdempotentElem e := heD.1.map D.val
  have hemem : e - c ∈ I.map (algebraMap R C) := by
    have h := Ideal.mem_map_of_mem D.val.toRingHom heDmem
    have hcomp : D.val.toRingHom.comp (algebraMap R D) = algebraMap R C := by
      ext r
      exact D.val.commutes r
    rw [Ideal.map_map, hcomp] at h
    simpa [e, cD] using h
  refine ⟨e, ⟨he, hemem⟩, ?_⟩
  intro z hz
  have hze : z - e ∈ I.map (algebraMap R C) := by
    simpa only [sub_sub_sub_cancel_right] using
      (I.map (algebraMap R C)).sub_mem hz.2 hemem
  obtain ⟨E, hE, hEs, w, hw, hwmem⟩ :=
    exists_finite_subalgebra_mem_map I {z, e} (z - e) hze
  have : Module.Finite R E := hE
  let zE : E := ⟨z, hEs z (by simp)⟩
  let eE : E := ⟨e, hEs e (by simp)⟩
  have hw' : w = zE - eE := Subtype.ext hw
  have hzeE : zE - eE ∈ I.map (algebraMap R E) := by
    simpa only [hw'] using hwmem
  have hzE : IsIdempotentElem zE := Subtype.ext hz.1
  have heE : IsIdempotentElem eE := Subtype.ext he
  have hze0E : Ideal.Quotient.mk (I.map (algebraMap R E)) zE =
      Ideal.Quotient.mk (I.map (algebraMap R E)) eE :=
    (Ideal.Quotient.eq (I := I.map (algebraMap R E))).mpr hzeE
  obtain ⟨a, _, ha⟩ := HenselianRing.existsUnique_isIdempotentElem_map I
    (hzE.map (Ideal.Quotient.mk (I.map (algebraMap R E))))
  have hzA : zE = a := ha zE ⟨hzE, rfl⟩
  have heA : eE = a := ha eE ⟨heE, hze0E.symm⟩
  exact congrArg E.val (hzA.trans heA.symm)

/-- An integral homomorphism carries a Henselian pair to the pair defined by the
extended ideal. See the Stacks Project, Lemma 15.11.8 (Tag 09XK). -/
theorem map_of_isIntegral {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (I : Ideal R) [HenselianRing R I] (f : R →+* S) (hf : f.IsIntegral) :
    HenselianRing S (I.map f) := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := algebraMap_isIntegral_iff.mp hf
  apply (HenselianRing.iff_existsUnique_isIdempotentElem_map.{v, 0} (I.map f)).2
  intro B _ _ _
  let : Algebra R B := Algebra.compHom B f
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsIntegral S B := inferInstance
  have : Algebra.IsIntegral R B := Algebra.IsIntegral.trans (R := R) (A := S) (B := B)
  have hI : (I.map f).map (algebraMap S B) = I.map (algebraMap R B) := by
    rw [Ideal.map_map, IsScalarTower.algebraMap_eq R S B,
      RingHom.algebraMap_toAlgebra]
  rw [hI]
  intro e0 he0
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective e0
  have hc : c * c - c ∈ I.map (algebraMap R B) := by
    rw [isIdempotentElem_iff, ← map_mul, Ideal.Quotient.eq] at he0
    exact he0
  obtain ⟨e, he, hu⟩ := existsUnique_isIdempotentElem_sub_mem_map I c hc
  refine ⟨e, ⟨he.1, (Ideal.Quotient.eq (I := I.map (algebraMap R B))).mpr he.2⟩, ?_⟩
  intro z hz
  exact hu z ⟨hz.1, (Ideal.Quotient.eq (I := I.map (algebraMap R B))).mp hz.2⟩

/-- A pair is Henselian if and only if its extension along an integral faithfully flat
ring homomorphism is Henselian. -/
theorem iff_map_of_isIntegral_of_faithfullyFlat {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S) (hf : f.IsIntegral)
    (hff : f.FaithfullyFlat) : HenselianRing R I ↔ HenselianRing S (I.map f) := by
  constructor
  · intro hR
    let : HenselianRing R I := hR
    exact map_of_isIntegral I f hf
  · intro hS
    let : Algebra R S := f.toAlgebra
    have : Algebra.IsIntegral R S := algebraMap_isIntegral_iff.mp hf
    have : Module.FaithfullyFlat R S := hff
    let : HenselianRing S (I.map f) := hS
    apply (iff_existsUnique_isIdempotentElem_map.{u, 0} I).2
    intro B _ _ _ e0 he0
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective e0
    have hc : c * c - c ∈ I.map (algebraMap R B) := by
      rw [isIdempotentElem_iff, ← map_mul, Ideal.Quotient.eq] at he0
      exact he0
    let T := B ⊗[R] S
    let g : B →+* T := algebraMap B T
    let k : S →+* T := Algebra.TensorProduct.includeRight.toRingHom
    let J := I.map (algebraMap R B)
    let K := J.map g
    have hk : k.IsIntegral := by
      have hleft : (algebraMap S (S ⊗[R] B)).IsIntegral :=
        algebraMap_isIntegral_iff.mpr inferInstance
      have hcomm := (Algebra.TensorProduct.comm R S B).surjective
      exact RingHom.IsIntegral.trans (algebraMap S (S ⊗[R] B))
        (Algebra.TensorProduct.comm R S B).toRingHom hleft
        ((Algebra.TensorProduct.comm R S B).toRingHom.isIntegral_of_surjective hcomm)
    have hK : (I.map f).map k = K := by
      dsimp [K, J]
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
    have : HenselianRing T K := hK ▸ map_of_isIntegral (I.map f) k hk
    have hcT : g c * g c - g c ∈ K := by
      simpa only [map_sub, map_mul] using Ideal.mem_map_of_mem g hc
    obtain ⟨e, he, hu⟩ : ∃! e : T, IsIdempotentElem e ∧ e - g c ∈ K := by
      simpa using existsUnique_isIdempotentElem_sub_mem_map K (g c) (by simpa using hcT)
    -- Compare the two pullbacks of the lifted idempotent.
    let O := T ⊗[B] T
    let l : T →+* O := algebraMap T O
    let r : T →+* O := Algebra.TensorProduct.includeRight.toRingHom
    have hcomp : l.comp g = r.comp g :=
      Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    have hKr : K.map r = K.map l := by
      change (J.map g).map r = (J.map g).map l
      rw [Ideal.map_map g r, Ideal.map_map g l, hcomp]
    have hcO : l (g c) * l (g c) - l (g c) ∈ K.map l := by
      simpa only [map_sub, map_mul] using Ideal.mem_map_of_mem l hcT
    obtain ⟨a, _, ha⟩ := existsUnique_isIdempotentElem_sub_mem_map K (l (g c)) hcO
    have hle : l e = a := ha (l e) ⟨he.1.map l, by
      simpa only [map_sub] using Ideal.mem_map_of_mem l he.2⟩
    have hre : r e = a := ha (r e) ⟨he.1.map r, by
      have hm := Ideal.mem_map_of_mem r he.2
      rw [hKr, map_sub] at hm
      have hgc : r (g c) = l (g c) := (RingHom.congr_fun hcomp c).symm
      simpa only [hgc] using hm⟩
    have heRange : e ∈ Set.range g := by
      rw [← Algebra.IsEffective.eqLocus_includeLeft_includeRight
        (Algebra.IsEffective.of_faithfullyFlat B T)]
      exact hle.trans hre.symm
    obtain ⟨b, hb⟩ := heRange
    have hinj : Function.Injective g := FaithfulSMul.algebraMap_injective B T
    have heb : IsIdempotentElem b := by
      apply isIdempotentElem_iff.mpr
      apply hinj
      simpa only [map_mul, hb] using isIdempotentElem_iff.mp he.1
    have hbmem : b - c ∈ J := by
      rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := T) J]
      change g (b - c) ∈ K
      simpa only [map_sub, hb] using he.2
    refine ⟨b, ⟨heb, (Ideal.Quotient.eq (I := J)).mpr hbmem⟩, ?_⟩
    intro z hz
    apply hinj
    apply Eq.trans ?_ hb.symm
    apply hu (g z)
    refine ⟨hz.1.map g, ?_⟩
    have hzmem := (Ideal.Quotient.eq (I := J)).mp hz.2
    simpa only [map_sub] using Ideal.mem_map_of_mem g hzmem

/-- A surjective homomorphism sends a Henselian pair to the pair defined by the image ideal.

This is the surjective case of the Stacks Project, Lemma 15.11.8 (Tag 09XK), which
allows an integral ring homomorphism. -/
theorem map_of_surjective {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (I : Ideal R) [HenselianRing R I] (f : R →+* S) (hf : Function.Surjective f) :
    HenselianRing S (I.map f) := by
  let : Algebra R S := f.toAlgebra
  exact map_of_isIntegral I f
    (algebraMap_isIntegral_iff.mpr (Algebra.isIntegral_of_surjective hf))

/-- A surjective homomorphism with elementwise-nil kernel preserves and reflects the
Henselian-pair property.

The nil-ideal case of the Stacks Project, Lemma 15.11.9 (Tag 0DYD), with the
nil-ideal assertion of Lemma 15.11.2 (Tag 0ALI), concerns ideals containing the
kernel. This statement extends that case to an arbitrary source ideal. Nilness is
elementwise, with no uniform exponent; the kernel need not be contained in the
source ideal. -/
theorem iff_map_of_surjective_of_nil_ker {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)
    (hf : Function.Surjective f) (hker : ∀ x : R, f x = 0 → IsNilpotent x) :
    HenselianRing R I ↔ HenselianRing S (I.map f) := by
  constructor
  · intro hR
    let : HenselianRing R I := hR
    exact map_of_surjective I f hf
  · intro hS
    classical
    let : HenselianRing S (I.map f) := hS
    let : Algebra R S := f.toAlgebra
    apply (HenselianRing.iff_existsUnique_isIdempotentElem_map.{u, 0} I).mpr
    intro B _ _ _ e0 he0
    let J : Ideal B := (RingHom.ker f).map (algebraMap R B)
    let C := B ⧸ J
    let q : B →+* C := Ideal.Quotient.mk J
    have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
    have hJ : ∀ b ∈ J, IsNilpotent b := by
      have hle : J ≤ nilradical B := by
        apply Ideal.map_le_iff_le_comap.mpr
        intro r hr
        exact mem_nilradical.mpr
          ((hker r (RingHom.mem_ker.mp hr)).map (algebraMap R B))
      intro b hb
      exact mem_nilradical.mp (hle hb)
    have hqnil : ∀ b ∈ RingHom.ker q, IsNilpotent b := by
      intro b hb
      exact hJ b (Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp hb))
    -- The quotient action factors the given surjection.
    have hfactor : RingHom.ker f ≤ RingHom.ker (q.comp (algebraMap R B)) := by
      intro r hr
      apply RingHom.mem_ker.mpr
      change q (algebraMap R B r) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_map_of_mem (algebraMap R B) hr
    let g : S →+* C := f.liftOfSurjective hf ⟨q.comp (algebraMap R B), hfactor⟩
    have hg : g.comp f = q.comp (algebraMap R B) :=
      f.liftOfSurjective_comp hf ⟨q.comp (algebraMap R B), hfactor⟩
    let : Algebra S C := g.toAlgebra
    let : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' (by
      change algebraMap R C = g.comp f
      exact (Ideal.Quotient.mk_comp_algebraMap R J).symm.trans hg.symm)
    let : Module.Finite R C := Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ R J).toLinearMap (Ideal.Quotient.mkₐ_surjective R J)
    let : Module.Finite S C := Module.Finite.of_restrictScalars_finite R S C
    let IB : Ideal B := I.map (algebraMap R B)
    have himage : (I.map f).map (algebraMap S C) = IB.map q := by
      change (I.map f).map g = (I.map (algebraMap R B)).map q
      rw [Ideal.map_map, Ideal.map_map, hg]
    let χ : B ⧸ IB →+* C ⧸ IB.map q :=
      Ideal.quotientMap (IB.map q) q Ideal.le_comap_map
    have hχmk (b : B) : χ (Ideal.Quotient.mk IB b) =
        Ideal.Quotient.mk (IB.map q) (q b) := Ideal.quotientMap_mk
    -- Nilness descends through this square even when J is not contained in IB.
    have hχnil : ∀ x ∈ RingHom.ker χ, IsNilpotent x := by
      intro x hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := IB) x
      have hz := RingHom.mem_ker.mp hx
      rw [hχmk b] at hz
      have hqb : q b ∈ IB.map q := Ideal.Quotient.eq_zero_iff_mem.mp hz
      obtain ⟨a, ha, hab⟩ := (Ideal.mem_map_iff_of_surjective q hq).mp hqb
      have hba : b - a ∈ RingHom.ker q := (RingHom.sub_mem_ker_iff q).mpr hab.symm
      have hnil := (hqnil (b - a) hba).map (Ideal.Quotient.mk IB)
      have ha0 : Ideal.Quotient.mk IB a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
      simpa only [map_sub, ha0, sub_zero] using hnil
    have hliftC : ∀ c0 : C ⧸ (I.map f).map (algebraMap S C),
        IsIdempotentElem c0 → ∃! c : C, IsIdempotentElem c ∧
          Ideal.Quotient.mk ((I.map f).map (algebraMap S C)) c = c0 := by
      intro c0 hc0
      exact HenselianRing.existsUnique_isIdempotentElem_map (I.map f) hc0
    rw [himage] at hliftC
    obtain ⟨eC, heC, uniqueC⟩ := hliftC (χ e0) (he0.map χ)
    obtain ⟨eB, heB, uniqueB⟩ :=
      existsUnique_isIdempotentElem_eq_of_ker_isNilpotent q hqnil eC
        (RingHom.mem_range.mpr (hq eC)) heC.1
    have heBraw : Ideal.Quotient.mk IB eB = e0 := by
      apply eq_of_isNilpotent_sub_of_isIdempotentElem
        (heB.1.map (Ideal.Quotient.mk IB)) he0
      apply hχnil
      apply (RingHom.sub_mem_ker_iff χ).mpr
      calc
        χ (Ideal.Quotient.mk IB eB) = Ideal.Quotient.mk (IB.map q) (q eB) := hχmk eB
        _ = Ideal.Quotient.mk (IB.map q) eC := congrArg _ heB.2
        _ = χ e0 := heC.2
    refine ⟨eB, ⟨heB.1, heBraw⟩, ?_⟩
    intro e he
    apply uniqueB e
    refine ⟨he.1, ?_⟩
    apply uniqueC (q e)
    refine ⟨he.1.map q, ?_⟩
    calc
      Ideal.Quotient.mk (IB.map q) (q e) = χ (Ideal.Quotient.mk IB e) := (hχmk e).symm
      _ = χ e0 := congrArg χ he.2

end HenselianRing
