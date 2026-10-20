/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.HenselianCriterion
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.Algebra.GroupWithZero.Basic

/-!
# Henselian pairs under surjective homomorphisms

For a surjective homomorphism of commutative rings, the image of a Henselian pair is
Henselian. If every element of the kernel is nilpotent, the source pair is Henselian
if and only if its image pair is Henselian.

The pair predicate is Mathlib's `HenselianRing`. This module uses Mathlib's
Henselian-pair formalization by Johan Commelin and ideal-map API by Kenny Lau.

## References

* The Stacks Project Authors, *The Stacks Project*, Section 15.11, "Henselian pairs":
  [Lemma 15.11.8 (Tag 09XK)](https://stacks.math.columbia.edu/tag/09XK), integral-map
  transport; [Lemma 15.11.9 (Tag 0DYD)](https://stacks.math.columbia.edu/tag/0DYD),
  nested-ideal transitivity; and
  [Lemma 15.11.2 (Tag 0ALI)](https://stacks.math.columbia.edu/tag/0ALI), locally
  nilpotent ideals.
-/

@[expose] public section

universe u v

namespace HenselianRing

/-- A surjective homomorphism sends a Henselian pair to the pair defined by the image ideal.

This is the surjective case of the Stacks Project, Lemma 15.11.8 (Tag 09XK), which
allows an integral ring homomorphism. -/
theorem map_of_surjective {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (I : Ideal R) [HenselianRing R I] (f : R →+* S) (hf : Function.Surjective f) :
    HenselianRing S (I.map f) := by
  letI : Algebra R S := f.toAlgebra
  letI : Module.Finite R S :=
    Module.Finite.of_surjective (Algebra.linearMap R S) (by
      intro s
      obtain ⟨r, hr⟩ := hf s
      refine ⟨r, ?_⟩
      simpa only [Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra] using hr)
  apply (HenselianRing.iff_existsUnique_isIdempotentElem_map.{v, 0} (I.map f)).2
  intro B _ _ _
  letI : Algebra R B := Algebra.compHom B f
  letI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite R B := Module.Finite.trans S B
  have hI : (I.map f).map (algebraMap S B) = I.map (algebraMap R B) := by
    rw [Ideal.map_map, IsScalarTower.algebraMap_eq R S B,
      RingHom.algebraMap_toAlgebra]
  rw [hI]
  intro e0 he0
  exact HenselianRing.existsUnique_isIdempotentElem_map I he0

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
    letI : HenselianRing R I := hR
    exact map_of_surjective I f hf
  · intro hS
    classical
    letI : HenselianRing S (I.map f) := hS
    letI : Algebra R S := f.toAlgebra
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
    letI : Algebra S C := g.toAlgebra
    letI : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' (by
      change algebraMap R C = g.comp f
      exact (Ideal.Quotient.mk_comp_algebraMap R J).symm.trans hg.symm)
    letI : Module.Finite R C := Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ R J).toLinearMap (Ideal.Quotient.mkₐ_surjective R J)
    letI : Module.Finite S C := Module.Finite.of_restrictScalars_finite R S C
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
