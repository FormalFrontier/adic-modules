/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianTransport

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Basic

/-!
# Henselian pairs in products

For a dependent family of commutative rings, the product ring is Henselian at the
componentwise product ideal if and only if each component is Henselian at its ideal.
The index type is arbitrary, including the empty type.

The statements use Mathlib's `HenselianRing` and `Ideal.pi`.
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

end HenselianRing
