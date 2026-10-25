/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianTransport
import Mathlib.Algebra.Ring.Fin
import Mathlib.Algebra.Ring.ULift

public import AdicModules.RingTheory.HenselianIdeal

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Prod

/-!
# Henselian pairs in products

For a dependent family of commutative rings, the product ring is Henselian at the
componentwise product ideal if and only if each component is Henselian at its ideal.
The index type is arbitrary, including the empty type.

The statements use Mathlib's `HenselianRing` and `Ideal.pi`.
Binary products allow the two factors to lie in independent universes. The greatest
Henselian ideal commutes with dependent products and binary products.

## References

The product statements extend `HenselianRing.pi` and `HenselianRing.pi_iff` in this
module, using Mathlib's `HenselianRing`, `Ideal.pi`, `Ideal.prod` and ring-map APIs.
The greatest-ideal statements use `Ideal.henselianRadical`, its defining bound
`Ideal.le_henselianRadical` and `HenselianRing.map_of_surjective` from
`AdicModules.RingTheory.HenselianIdeal` and `AdicModules.RingTheory.HenselianTransport`.
-/

@[expose] public section

universe u v

namespace HenselianRing

variable {ι : Type u} {R : ι → Type v} [∀ i, CommRing (R i)]

/-- A product of Henselian pairs is Henselian at the componentwise product ideal. -/
instance pi (I : ∀ i, Ideal (R i)) [∀ i, HenselianRing (R i) (I i)] :
    HenselianRing (∀ i, R i) (Ideal.pi I) := by
  classical
  refine { jac := ?_, is_henselian := ?_ }
  · intro x hx
    apply Ideal.mem_jacobson_iff.mpr
    intro y
    have h (i : ι) :
        ∃ z : R i, z * y i * x i + z - 1 ∈ (⊥ : Ideal (R i)) :=
      Ideal.mem_jacobson_iff.mp
        (HenselianRing.jac (R := R i) (I := I i) ((Ideal.mem_pi I x).mp hx i)) (y i)
    let z : ∀ i, R i := fun i => Classical.choose (h i)
    refine ⟨z, ?_⟩
    have hz_zero : z * y * x + z - 1 = 0 := by
      funext i
      simpa [z] using Classical.choose_spec (h i)
    simpa using hz_zero
  · intro f hf a₀ hroot hunit
    let e (i : ι) : (∀ j, R j) →+* R i := Pi.evalRingHom R i
    have heval (p : Polynomial (∀ i, R i)) (a : ∀ i, R i) (i : ι) :
        (p.map (e i)).eval (a i) = (p.eval a) i :=
      Polynomial.eval_map_apply (e i) a
    have hbridge (d : ∀ i, R i)
        (hd : IsUnit (Ideal.Quotient.mk (Ideal.pi I) d)) (i : ι) :
        IsUnit (Ideal.Quotient.mk (I i) (d i)) := by
      simpa only [Ideal.Quotient.lift_mk, RingHom.comp_apply, e,
        Pi.evalRingHom_apply] using
        (IsUnit.map (Ideal.Quotient.lift (Ideal.pi I)
          ((Ideal.Quotient.mk (I i)).comp (e i))
          (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr
            ((Ideal.mem_pi I x).mp hx i))) hd)
    have hcomponent (i : ι) :
        ∃ a : R i, (f.map (e i)).IsRoot a ∧ a - a₀ i ∈ I i := by
      refine HenselianRing.is_henselian (I := I i)
        (f.map (e i)) (Polynomial.Monic.map (e i) hf) (a₀ i) ?_ ?_
      · rw [heval f a₀ i]
        exact (Ideal.mem_pi I (f.eval a₀)).mp hroot i
      · rw [Polynomial.derivative_map, heval f.derivative a₀ i]
        exact hbridge (f.derivative.eval a₀) hunit i
    let a : ∀ i, R i := fun i => Classical.choose (hcomponent i)
    refine ⟨a, Polynomial.IsRoot.def.mpr ?_, (Ideal.mem_pi I _).mpr ?_⟩
    · funext i
      have hi : (f.map (e i)).eval (a i) = 0 :=
        Polynomial.IsRoot.def.mp (Classical.choose_spec (hcomponent i)).1
      rw [heval f a i] at hi
      exact hi
    · intro i
      exact (Classical.choose_spec (hcomponent i)).2

/-- A product is Henselian at the componentwise product ideal exactly when every
component is Henselian at its corresponding ideal. -/
theorem pi_iff (I : ∀ i, Ideal (R i)) :
    HenselianRing (∀ i, R i) (Ideal.pi I) ↔ ∀ i, HenselianRing (R i) (I i) := by
  classical
  constructor
  · intro h i
    let : HenselianRing (∀ j, R j) (Ideal.pi I) := h
    have himage : (Ideal.pi I).map (Pi.evalRingHom R i) = I i := by
      apply le_antisymm
      · apply (Ideal.map_le_iff_le_comap (f := Pi.evalRingHom R i)).2
        intro x hx
        exact (Ideal.mem_pi I x).1 hx i
      · intro x hx
        let g : ∀ j, R j := fun j => if e : j = i then e.symm ▸ x else 0
        have hg : g ∈ Ideal.pi I := by
          apply (Ideal.mem_pi I g).2
          intro j
          by_cases e : j = i
          · subst j
            simpa [g] using hx
          · simp [g, e]
        have hle : Ideal.pi I ≤ Ideal.comap (Pi.evalRingHom R i)
            ((Ideal.pi I).map (Pi.evalRingHom R i)) :=
          (Ideal.map_le_iff_le_comap (f := Pi.evalRingHom R i)).1 le_rfl
        have hmem : (Pi.evalRingHom R i) g ∈
            (Ideal.pi I).map (Pi.evalRingHom R i) := hle hg
        change g i ∈ (Ideal.pi I).map (Pi.evalRingHom R i) at hmem
        simpa [g] using hmem
    have heval : Function.Surjective (Pi.evalRingHom R i) :=
      Function.surjective_eval i
    simpa only [himage] using
      (HenselianRing.map_of_surjective (Ideal.pi I) (Pi.evalRingHom R i) heval)
  · intro h
    let : ∀ i, HenselianRing (R i) (I i) := h
    exact HenselianRing.pi I

/-- Henselianity at an arbitrary ideal of a dependent product is equivalent to
Henselianity at each coordinate image ideal. -/
theorem pi_iff_map (K : Ideal (∀ i, R i)) :
    HenselianRing (∀ i, R i) K ↔
      ∀ i, HenselianRing (R i) (K.map (Pi.evalRingHom R i)) := by
  constructor
  · intro h i
    let : HenselianRing (∀ i, R i) K := h
    exact HenselianRing.map_of_surjective K (Pi.evalRingHom R i)
      (Function.surjective_eval i)
  · intro h
    let : ∀ i, HenselianRing (R i) (K.map (Pi.evalRingHom R i)) := h
    apply HenselianRing.of_le (J := Ideal.pi (fun i => K.map (Pi.evalRingHom R i)))
    intro x hx
    exact (Ideal.mem_pi _ _).mpr fun i => Ideal.mem_map_of_mem (Pi.evalRingHom R i) hx

end HenselianRing

/-- A binary product of Henselian pairs is Henselian at the product ideal. -/
instance HenselianRing.prod {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) [HenselianRing R I] [HenselianRing S J] :
    HenselianRing (R × S) (I.prod J) := by
  -- Lift the factors to a common universe for the dependent-product instance.
  let eR : ULift.{v} R ≃+* R := ULift.ringEquiv
  let eS : ULift.{u} S ≃+* S := ULift.ringEquiv
  have hR : HenselianRing (ULift.{v} R) (I.comap eR) := by
    simpa only [Ideal.map_coe, Ideal.map_symm] using
      (HenselianRing.map_of_surjective I (eR.symm : R →+* ULift.{v} R) eR.symm.surjective)
  have hS : HenselianRing (ULift.{u} S) (J.comap eS) := by
    simpa only [Ideal.map_coe, Ideal.map_symm] using
      (HenselianRing.map_of_surjective J (eS.symm : S →+* ULift.{u} S) eS.symm.surjective)
  let T : Fin 2 → Type (max u v) :=
    Fin.cases (ULift.{v} R) (fun _ => ULift.{u} S)
  let : ∀ i, CommRing (T i) := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · change CommRing (ULift.{v} R)
      infer_instance
    · change CommRing (ULift.{u} S)
      infer_instance
  let K : ∀ i, Ideal (T i) := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · change Ideal (ULift.{v} R)
      exact I.comap eR
    · change Ideal (ULift.{u} S)
      exact J.comap eS
  let : ∀ i, HenselianRing (T i) (K i) := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · change HenselianRing (ULift.{v} R) (I.comap eR)
      exact hR
    · change HenselianRing (ULift.{u} S) (J.comap eS)
      exact hS
  let : HenselianRing (∀ i, T i) (Ideal.pi K) := HenselianRing.pi K
  let e : (∀ i, T i) ≃+* R × S := (RingEquiv.piFinTwo T).trans (by
    change ULift.{v} R × ULift.{u} S ≃+* R × S
    exact RingEquiv.prodCongr eR eS)
  have himage : (Ideal.pi K).map (e : (∀ i, T i) →+* R × S) = I.prod J := by
    rw [Ideal.map_comap_of_equiv e]
    ext x
    change (∀ i, e.symm x i ∈ K i) ↔ x.1 ∈ I ∧ x.2 ∈ J
    rw [Fin.forall_fin_two]
    rfl
  simpa only [himage] using
    (HenselianRing.map_of_surjective (Ideal.pi K) (e : (∀ i, T i) →+* R × S) e.surjective)

/-- A binary product is Henselian exactly when both factors are Henselian. -/
theorem HenselianRing.prod_iff {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) :
    HenselianRing (R × S) (I.prod J) ↔ HenselianRing R I ∧ HenselianRing S J := by
  constructor
  · intro h
    let : HenselianRing (R × S) (I.prod J) := h
    constructor
    · simpa only [Ideal.map_fst_prod] using
        (HenselianRing.map_of_surjective (I.prod J) (RingHom.fst R S) Prod.fst_surjective)
    · simpa only [Ideal.map_snd_prod] using
        (HenselianRing.map_of_surjective (I.prod J) (RingHom.snd R S) Prod.snd_surjective)
  · rintro ⟨hR, hS⟩
    let : HenselianRing R I := hR
    let : HenselianRing S J := hS
    exact HenselianRing.prod I J

/-- Henselianity at an arbitrary ideal of a binary product is equivalent to
Henselianity at its two projection image ideals. -/
theorem HenselianRing.prod_iff_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (K : Ideal (R × S)) :
    HenselianRing (R × S) K ↔
      HenselianRing R (K.map (RingHom.fst R S)) ∧
        HenselianRing S (K.map (RingHom.snd R S)) := by
  simpa only [← Ideal.ideal_prod_eq K] using
    (HenselianRing.prod_iff (K.map (RingHom.fst R S)) (K.map (RingHom.snd R S)))

/-- The greatest Henselian ideal of a dependent product is componentwise. -/
theorem Ideal.henselianRadical_pi {ι : Type u} (R : ι → Type v) [∀ i, CommRing (R i)] :
    Ideal.henselianRadical (∀ i, R i) = Ideal.pi (fun i => Ideal.henselianRadical (R i)) := by
  classical
  let : ∀ i, HenselianRing (R i) (Ideal.henselianRadical (R i)) :=
    fun i => HenselianRing.henselianRadical (R i)
  let : HenselianRing (∀ i, R i) (Ideal.henselianRadical (∀ i, R i)) :=
    HenselianRing.henselianRadical _
  apply le_antisymm
  · intro x hx
    apply (Ideal.mem_pi _ _).mpr
    intro i
    have h := HenselianRing.map_of_surjective
      (Ideal.henselianRadical (∀ i, R i)) (Pi.evalRingHom R i)
      (Function.surjective_eval i)
    exact Ideal.le_henselianRadical _ h (Ideal.mem_map_of_mem (Pi.evalRingHom R i) hx)
  · exact Ideal.le_henselianRadical _ (HenselianRing.pi _)

/-- The greatest Henselian ideal of a binary product is the product ideal. -/
theorem Ideal.henselianRadical_prod (R : Type u) (S : Type v) [CommRing R] [CommRing S] :
    Ideal.henselianRadical (R × S) =
      (Ideal.henselianRadical R).prod (Ideal.henselianRadical S) := by
  let : HenselianRing R (Ideal.henselianRadical R) := HenselianRing.henselianRadical R
  let : HenselianRing S (Ideal.henselianRadical S) := HenselianRing.henselianRadical S
  let : HenselianRing (R × S) (Ideal.henselianRadical (R × S)) :=
    HenselianRing.henselianRadical _
  apply le_antisymm
  · intro x hx
    apply (Ideal.mem_prod _ _).mpr
    constructor
    · have h := HenselianRing.map_of_surjective
        (Ideal.henselianRadical (R × S)) (RingHom.fst R S) Prod.fst_surjective
      exact Ideal.le_henselianRadical _ h (Ideal.mem_map_of_mem (RingHom.fst R S) hx)
    · have h := HenselianRing.map_of_surjective
        (Ideal.henselianRadical (R × S)) (RingHom.snd R S) Prod.snd_surjective
      exact Ideal.le_henselianRadical _ h (Ideal.mem_map_of_mem (RingHom.snd R S) hx)
  · exact Ideal.le_henselianRadical _ (HenselianRing.prod _ _)
