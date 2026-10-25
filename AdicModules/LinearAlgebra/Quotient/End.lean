/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Endomorphisms on ideal-smul quotients

Reduction modulo an ideal acts on endomorphisms of the original module, with
scalars unchanged. The quotient and its induced maps are Mathlib's constructions.
For commutative scalars, restriction of scalars identifies this construction with
Mathlib's `LinearMap.reduceModIdeal`. The finite-module unit-reflection statement
combines Nakayama's lemma with
Orzech's theorem, as supplied by Mathlib.

## References

* Mathlib's quotient, Nakayama and Orzech formalizations, including
  `Submodule.mapQ`, `LinearMap.reduceModIdeal`, `CommRing.orzechProperty` and
  `Module.End.isUnit_iff`.
* [The Stacks Project, Nakayama's lemma, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV).
* M. Orzech, *Onto endomorphisms are isomorphisms*, American Mathematical
  Monthly 78 (1971), 357–362.
-/

@[expose] public section

universe u v

namespace Module.End

section Ring

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The endomorphism ring homomorphism induced on the quotient by `I • ⊤`. -/
def reduceModIdeal (I : Ideal R) :
    Module.End R M →+* Module.End R (M ⧸ (I • (⊤ : Submodule R M))) where
  toFun f := (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R M)) f
    (Submodule.smul_top_le_comap_smul_top I f)
  map_zero' := Submodule.quot_hom_ext (I • (⊤ : Submodule R M)) _ _ (fun _ => rfl)
  map_one' := Submodule.quot_hom_ext (I • (⊤ : Submodule R M)) _ _ (fun _ => rfl)
  map_add' _ _ := Submodule.quot_hom_ext (I • (⊤ : Submodule R M)) _ _ (fun _ => rfl)
  map_mul' _ _ := Submodule.quot_hom_ext (I • (⊤ : Submodule R M)) _ _ (fun _ => rfl)

/-- Reduction sends the class of an element to the class of its image. -/
@[simp]
theorem reduceModIdeal_apply_mk (I : Ideal R) (f : Module.End R M) (m : M) :
    reduceModIdeal I f (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m) := rfl

/-- Reduction evaluated through the quotient linear map. -/
theorem reduceModIdeal_apply_mkQ (I : Ideal R) (f : Module.End R M) (m : M) :
    reduceModIdeal I f ((I • (⊤ : Submodule R M)).mkQ m) =
      (I • (⊤ : Submodule R M)).mkQ (f m) := rfl

/-- Reduction intertwines the original endomorphism with the quotient map. -/
theorem reduceModIdeal_comp_mkQ (I : Ideal R) (f : Module.End R M) :
    (reduceModIdeal I f).comp (I • (⊤ : Submodule R M)).mkQ =
      (I • (⊤ : Submodule R M)).mkQ.comp f :=
  Submodule.mapQ_mkQ _ _ _ (h := Submodule.smul_top_le_comap_smul_top I f)

/-- Two endomorphisms have equal reductions exactly when their values differ in
`I • ⊤` at every element of the original module. -/
theorem reduceModIdeal_eq_iff (I : Ideal R) (f g : Module.End R M) :
    reduceModIdeal I f = reduceModIdeal I g ↔
      ∀ m, f m - g m ∈ I • (⊤ : Submodule R M) := by
  constructor
  · intro h m
    apply (Submodule.Quotient.eq (I • (⊤ : Submodule R M))).mp
    exact congrArg (fun a : Module.End R (M ⧸ (I • (⊤ : Submodule R M))) =>
      a ((I • (⊤ : Submodule R M)).mkQ m)) h
  · intro h
    apply Submodule.quot_hom_ext (I • (⊤ : Submodule R M)) _ _
    intro m
    exact (Submodule.Quotient.eq (I • (⊤ : Submodule R M))).mpr (h m)

/-- Reduction modulo the zero ideal loses no endomorphisms. -/
theorem reduceModIdeal_injective_bot :
    Function.Injective (reduceModIdeal (M := M) (⊥ : Ideal R)) := by
  intro f g h
  apply LinearMap.ext
  intro m
  have hm := (reduceModIdeal_eq_iff (⊥ : Ideal R) f g).mp h m
  simpa only [Submodule.bot_smul, Submodule.mem_bot, sub_eq_zero] using hm

end Ring

section CommRing

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- For commutative scalars, endomorphism reduction agrees with Mathlib's quotient
linear map after restriction from `R ⧸ I` to the original scalars. -/
theorem reduceModIdeal_eq_restrictScalars (I : Ideal R) (f : Module.End R M) :
    reduceModIdeal I f = (LinearMap.reduceModIdeal I f).restrictScalars R := by
  apply Submodule.quot_hom_ext
  intro m
  rfl

variable [Module.Finite R M]

/-- Reduction of a finite-module endomorphism modulo an ideal contained in the
Jacobson radical of the module annihilator reflects units.

The proof combines Nakayama's lemma (Stacks Project, Tag 00DV) and Orzech's
theorem on surjective endomorphisms (1971), through their Mathlib formalizations;
see the module references. -/
theorem isLocalHom_reduceModIdeal (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (Module.annihilator R M)) :
    IsLocalHom (reduceModIdeal (M := M) I) := by
  refine ⟨fun f hf => ?_⟩
  have hsurj : Function.Surjective (reduceModIdeal I f) :=
    ((Module.End.isUnit_iff _).mp hf).surjective
  have hcomp : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ.comp f) := by
    rw [← reduceModIdeal_comp_mkQ I f]
    exact hsurj.comp (Submodule.mkQ_surjective _)
  have hrange : f.range ⊔ I • (⊤ : Submodule R M) = ⊤ := by
    have hmap : Submodule.map (I • (⊤ : Submodule R M)).mkQ f.range = ⊤ := by
      rw [← LinearMap.range_comp]
      exact LinearMap.range_eq_top_of_surjective _ hcomp
    simpa only [sup_comm] using
      (Submodule.map_mkQ_eq_top (I • (⊤ : Submodule R M)) f.range).mp hmap
  have hnak := Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson
    (N := f.range) (N' := (⊤ : Submodule R M))
    (Module.finite_def.mp ‹Module.Finite R M›) hI (le_of_eq hrange.symm)
  have hzero : Module.annihilator R M • (⊤ : Submodule R M) = ⊥ := by
    simpa only [Submodule.annihilator_top] using
      (Submodule.annihilator_smul (⊤ : Submodule R M))
  have htop : f.range = ⊤ := by
    simpa only [sup_top_eq, hzero, sup_bot_eq] using hnak.symm
  exact (Module.End.isUnit_iff f).mpr
    (OrzechProperty.bijective_of_surjective_endomorphism f
      (LinearMap.range_eq_top.mp htop))

end CommRing

end Module.End
