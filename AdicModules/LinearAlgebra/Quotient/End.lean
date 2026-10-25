/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective
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
Reduction is injective when the ideal annihilates the module, over any ring.
When scalar multiplications commute on the module, this condition also
characterizes injectivity, with no finiteness or projectivity assumption.
In particular, the criterion applies over every commutative ring.
For projective modules, every endomorphism of the quotient lifts to an
endomorphism of the original module. For finite projective modules over a
commutative ring, every quotient automorphism lifts when the ideal is contained
in the Jacobson radical of the module annihilator.
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

/-- Reduction is injective if the ideal annihilates the original module. -/
theorem reduceModIdeal_injective_of_le_annihilator (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) :
    Function.Injective (reduceModIdeal (R := R) (M := M) I) := by
  have hzero : I • (⊤ : Submodule R M) ≤ ⊥ := by
    apply Submodule.smul_le.mpr
    intro a ha m _
    simpa only [Submodule.mem_bot] using Module.mem_annihilator.mp (hI ha) m
  intro f g h
  apply LinearMap.ext
  intro m
  have hm := hzero ((reduceModIdeal_eq_iff I f g).mp h m)
  simpa only [Submodule.mem_bot, sub_eq_zero] using hm

/-- Every endomorphism of an ideal-smul quotient of a projective module lifts to
an endomorphism of the original module. -/
theorem reduceModIdeal_surjective [Module.Projective R M] (I : Ideal R) :
    Function.Surjective (reduceModIdeal (R := R) (M := M) I) := by
  intro g
  obtain ⟨f, hf⟩ := Module.projective_lifting_property
    (I • (⊤ : Submodule R M)).mkQ (g.comp (I • (⊤ : Submodule R M)).mkQ)
    (Submodule.mkQ_surjective _)
  refine ⟨f, ?_⟩
  apply Submodule.quot_hom_ext (I • (⊤ : Submodule R M)) _ _
  intro m
  exact DFunLike.congr_fun ((reduceModIdeal_comp_mkQ I f).trans hf) m

/-- Reduction modulo the zero ideal loses no endomorphisms. -/
theorem reduceModIdeal_injective_bot :
    Function.Injective (reduceModIdeal (M := M) (⊥ : Ideal R)) :=
  reduceModIdeal_injective_of_le_annihilator ⊥ bot_le

/-- When scalar multiplications commute on the module, reduction is injective
exactly when the ideal annihilates the original module. No finiteness or
projectivity is required. In particular, this applies over a commutative ring. -/
theorem reduceModIdeal_injective_iff [SMulCommClass R R M] (I : Ideal R) :
    Function.Injective (reduceModIdeal (R := R) (M := M) I) ↔
      I ≤ Module.annihilator R M := by
  constructor
  · intro hinj a ha
    apply Module.mem_annihilator.mpr
    intro m
    have hred : reduceModIdeal I (a • (1 : Module.End R M)) = reduceModIdeal I 0 := by
      apply (reduceModIdeal_eq_iff I _ _).mpr
      intro x
      simpa using (Submodule.smul_mem_smul ha (show x ∈ (⊤ : Submodule R M) by trivial))
    have hscalar := hinj hred
    simpa using DFunLike.congr_fun hscalar m
  · exact reduceModIdeal_injective_of_le_annihilator I

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

/-- Every automorphism of an ideal-smul quotient of a finite projective module
over a commutative ring lifts to an automorphism of the original module when the
ideal lies in the Jacobson radical of the module annihilator.

Projectivity lifts the underlying endomorphism; finite-module unit reflection,
using Nakayama's lemma and Orzech's theorem as above, makes this lift a unit. -/
theorem unitsMap_reduceModIdeal_surjective [Module.Projective R M] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (Module.annihilator R M)) :
    Function.Surjective (Units.map (reduceModIdeal (M := M) I).toMonoidHom) := by
  let : IsLocalHom (reduceModIdeal (M := M) I) := isLocalHom_reduceModIdeal I hI
  intro g
  obtain ⟨f, hf⟩ := reduceModIdeal_surjective (M := M) I ↑g
  have hfunit : IsUnit (reduceModIdeal I f) := hf.symm ▸ g.isUnit
  obtain ⟨u, rfl⟩ := IsLocalHom.map_nonunit f hfunit
  exact ⟨u, Units.ext hf⟩

end CommRing

end Module.End
