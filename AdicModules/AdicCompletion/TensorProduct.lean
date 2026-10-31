/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

import AdicModules.AdicCompletion.Kernel
import AdicModules.AdicCompletion.Pi
import AdicModules.AdicCompletion.Quotient
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Adic completion and tensor products

For any ideal `I` of a commutative ring `R`, finiteness of the original first quotient
`M / I M` makes the canonical completed-ring-linear comparison from tensoring with
`AdicCompletion I R` to `AdicCompletion I M` surjective. No projectivity or finiteness of
original `M` is required. If original `M` is projective, the comparison is also injective,
hence an equivalence. It sends pure tensors to scalar multiples of canonical module elements
and agrees with Mathlib's finite-Noetherian equivalence where both apply. The finite-original
projective API is retained as a specialization.

If a positive power of `I` is finitely generated, the kernel of the comparison for any
original module is the intersection of all extended ideal-power submodules of the tensor
source. Thus injectivity is equivalent to original-`I` Hausdorffness of that source. With
only finiteness of the original first quotient added, the comparison induces a named
completed-ring-linear equivalence from the source's Hausdorffification to the completed
module. Its whole-map and representative laws describe the forward and inverse maps.
The bijectivity criterion uses this equivalence and its quotient projection.

For projective modules, injectivity detects coefficients in a free Finsupp module and uses
a projective retraction and naturality. For surjectivity, choose finite quotient generators
and original lifts. The chosen-family spanning theorem below makes those same completed
lifts span the raw completion; each lies in the range of the canonical comparison.
No Noetherian hypothesis on the ring or finite-generation hypothesis on the ideal is needed.

Finiteness of `M / I M` also gives finiteness of the raw completion over the canonical
completed ring. With original projectivity, the completion is projective over that ring by
base change and the canonical equivalence. These results use Mathlib's coefficientwise
completed-ring action, without an action of the completed ring on original `M`.
`AdicModules.AdicCompletion.FinitePresentation` consumes completed finiteness and projectivity
in one explicit finite-presentation theorem via `Module.finitePresentation_of_projective`.

For an original split surjection, finiteness of the intrinsic original kernel's first adic
quotient makes the completed-map kernel finite over the same completed ring. The consumer
`moduleFinite_ker_map_of_rightInverse_of_finite_quotient` transports completion finiteness
through the canonical split-kernel comparison from `AdicModules.AdicCompletion.Kernel`.

## Implementation notes

The kernel calculation uses the coefficient quotient comparison at stages `n * k`,
including zero, and the tensor quotient and base-change equivalences. Stage comparisons
are linear over the original ring. The Hausdorffification and first isomorphism theorem
are Mathlib's existing constructions. The positive-power hypothesis is sufficient, not
an individual-ideal necessity criterion; no such hypothesis is added to the projective APIs.

The ring and module universes are independent. Only the agreement with Mathlib's Noetherian
equivalence uses a common universe, as required by that equivalence.

The finite-first-quotient theorem concerns the raw inverse limit for arbitrary ideals.
Fujiwara–Kato, Proposition 7.2.16, also asserts intrinsic completion existence for finitely
generated ideals; no arbitrary-ideal intrinsic completeness assertion is made here.

For a finite module over a commutative Noetherian ring, the same canonical comparison is
bijective without projectivity. The ring and module universes are independent, and the
common-universe comparison with Mathlib identifies the equivalence obtained by
`LinearEquiv.ofBijective` with Mathlib's finite-Noetherian equivalence.

## References

Mathlib's `RingTheory/AdicCompletion/AsTensorProduct.lean`, by Judith Ludwig and Christian Merten,
supplies the canonical comparison, its naturality, the finite-power comparison, finite-module
surjectivity, and the Noetherian equivalence. Mathlib's `Algebra/Module/Projective.lean`, by
Kevin Buzzard and Antoine Labelle, supplies the projective Finsupp retraction, base-change
projectivity and transport along linear equivalences. Mathlib's
`RingTheory/TensorProduct/Finite.lean`, by Kim Morrison and Johan Commelin, supplies
base-change finiteness; `RingTheory/Finiteness/Basic.lean` supplies its transport along surjections.
The tensor surjectivity argument uses `Module.Finite.exists_fin` from Johan Commelin's
`RingTheory/Finiteness/Defs.lean`, quotient representatives, and this library's chosen-lifts
spanning refinement. The completion-finiteness argument uses `Module.Finite.exists_fin'` from
his `RingTheory/Finiteness/Cardinality.lean`, projective lifting of its finite-free source, and
`map_surjective_of_mkQ_comp_surjective` and `piEquivFin` from Mathlib's
`RingTheory/AdicCompletion/Functoriality.lean`, by Judith Ludwig and Christian Merten.
The chosen-family refinement uses the finite linear-combination API from Johannes Hölzl's
`LinearAlgebra/Finsupp/LinearCombination.lean` and the finite-product linear map equivalence
from Mathlib's `LinearAlgebra/Pi.lean`.
See also K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
Proposition 7.2.16, for the finitely generated ideal intrinsic-completion statement.
Mathlib's
`LinearAlgebra/DirectSum/Finsupp.lean`, by Johannes Hölzl and Antoine Chambert-Loir, supplies
the tensor/Finsupp coefficient equivalence. Related finite-projective retraction results are
in Mathlib's `RingTheory/Finiteness/Projective.lean`, by Johan Commelin.
The independent-universe Noetherian comparison uses finite-module smallness from Mathlib's
`RingTheory/Finiteness/Small.lean`, by Antoine Chambert-Loir and María-Inés de Frutos-Fernández,
and the `Shrink` linear equivalence from Kim Morrison's module API.
The kernel calculation reuses this library's coefficient quotient equivalence and its
fixed-stage kernel theorem, whose finite-linear-combination proof follows Bingyu Xia's
Mathlib formalization. Tensor quotient equivalences are from Antoine Chambert-Loir and
Jujian Zhang's `LinearAlgebra/TensorProduct/Quotient.lean`; scalar base cancellation uses
Kim Morrison, Johan Commelin and Eric Wieser's `LinearAlgebra/TensorProduct/Tower.lean`.
The Hausdorffification is from Mathlib's adic-completion Basic module by Kenny Lau,
Judith Ludwig, Christian Merten and Jiedong Jiang. The first isomorphism theorem is from
Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury Kudryashov's
`LinearAlgebra/Isomorphisms.lean`.
-/

set_option warningAsError true

@[expose] public section

noncomputable section

universe uR uM uN uσ uι

open TensorProduct

namespace AdicCompletion

variable {R : Type uR} [CommRing R] (I : Ideal R)

/-- The comparison for the scalar module agrees pointwise with the tensor right unitor. -/
private lemma ofTensorProduct_self_eq_rid_apply
    (x : AdicCompletion I R ⊗[R] R) :
    ofTensorProduct I R x =
      AlgebraTensorModule.rid R R (AdicCompletion I R) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a r =>
      rw [ofTensorProduct_tmul, AlgebraTensorModule.rid_tmul]
      apply AdicCompletion.ext
      intro n
      rw [smul_eval, of_apply, val_smul_apply]
      induction a.val n using Quotient.inductionOn' with
      | _ s =>
          change
            (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R R)) (s * r)) =
              Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R R)) (r * s)
          rw [mul_comm]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- A coefficient of the tensor/Finsupp equivalence is the completion of the corresponding
coefficient of the canonical comparison. -/
private lemma finsuppScalarRight_apply_eq_map_ofTensorProduct
    (σ : Type uσ) [DecidableEq σ]
    (x : AdicCompletion I R ⊗[R] (σ →₀ R)) (b : σ) :
    TensorProduct.finsuppScalarRight R R (AdicCompletion I R) σ x b =
      map I (Finsupp.lapply b : (σ →₀ R) →ₗ[R] R)
        (ofTensorProduct I (σ →₀ R) x) := by
  rw [TensorProduct.finsuppScalarRight_apply, ← ofTensorProduct_self_eq_rid_apply I]
  rw [← LinearMap.baseChange_eq_ltensor]
  exact (LinearMap.congr_fun
    (ofTensorProduct_naturality I (Finsupp.lapply b : (σ →₀ R) →ₗ[R] R)) x).symm

/-- The canonical tensor comparison is injective on an arbitrary Finsupp module. -/
private theorem ofTensorProduct_injective_finsupp (σ : Type uσ) :
    Function.Injective (ofTensorProduct I (σ →₀ R)) := by
  classical
  intro x y hxy
  apply (TensorProduct.finsuppScalarRight R R (AdicCompletion I R) σ).injective
  apply Finsupp.ext
  intro b
  rw [finsuppScalarRight_apply_eq_map_ofTensorProduct I σ x b,
    finsuppScalarRight_apply_eq_map_ofTensorProduct I σ y b, hxy]

variable (M : Type uM) [AddCommGroup M] [Module R M]

/-- A finite family spanning the first adic quotient has completed images
spanning the raw completion over the canonical completed ring. -/
theorem span_range_eq_top_of_span_mkQ_eq_top
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {ι : Type uι} [Finite ι] (v : ι → M)
    (hv : Submodule.span R
      (Set.range (fun i : ι =>
        (I • (⊤ : Submodule R M)).mkQ (v i))) = ⊤) :
    Submodule.span (AdicCompletion I R)
      (Set.range (fun i : ι => AdicCompletion.of I M (v i))) = ⊤ := by
  classical
  let := Fintype.ofFinite ι
  let f := Fintype.linearCombination R v
  have hq : (I • (⊤ : Submodule R M)).mkQ ∘ₗ f =
      Fintype.linearCombination R (fun i => (I • (⊤ : Submodule R M)).mkQ (v i)) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, f, Fintype.linearCombination_apply, map_sum, map_smul]
  have hsurj : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ ∘ₗ f) := by
    rw [hq]
    exact (span_range_eq_top_iff_surjective_fintypeLinearCombination R _).mp hv
  let e := piEquivOfFintype I (fun _ : ι => R)
  let g := (map I f).comp e.symm.toLinearMap
  have hone : of I R 1 = (1 : AdicCompletion I R) := by
    simpa only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
      (map_one (algebraMap R (AdicCompletion I R)))
  -- The finite-product comparison respects the same original basis vectors.
  have he (i : ι) : e.symm (Pi.single i 1) = of I (ι → R) (Pi.single i 1) := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    change Pi.single i 1 = piEquivOfFintype I (fun _ : ι => R)
      (of I (ι → R) (Pi.single i 1))
    rw [piEquivOfFintype_apply, pi_of]
    funext j
    by_cases hij : i = j <;> simp [hij, hone]
  have hg : g = Fintype.linearCombination (AdicCompletion I R)
      (fun i : ι => of I M (v i)) := by
    apply (LinearEquiv.piRing (AdicCompletion I R) (AdicCompletion I M) ι
      (AdicCompletion I R)).injective
    funext i
    change map I f (e.symm (Pi.single i 1)) =
      Fintype.linearCombination (AdicCompletion I R) (fun i : ι => of I M (v i))
        (Pi.single i 1)
    rw [he, map_of]
    simp only [f, Fintype.linearCombination_apply_single, one_smul]
  apply (span_range_eq_top_iff_surjective_fintypeLinearCombination (AdicCompletion I R) _).mpr
  rw [← hg]
  exact (map_surjective_of_mkQ_comp_surjective hsurj).comp e.symm.surjective

/-- Finiteness of the original first adic quotient makes the canonical completed-ring-linear
tensor comparison surjective, for any ideal and without projectivity of the original module. -/
theorem ofTensorProduct_surjective_of_finite_quotient
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] :
    Function.Surjective (ofTensorProduct I M) := by
  classical
  obtain ⟨n, q, hq⟩ :=
    Module.Finite.exists_fin (R := R) (M := M ⧸ (I • (⊤ : Submodule R M)))
  choose v hv using fun i : Fin n =>
    Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) (q i)
  have hspan := span_range_eq_top_of_span_mkQ_eq_top I v (by simpa only [hv] using hq)
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨(1 : AdicCompletion I R) ⊗ₜ[R] v i, by
    simp only [ofTensorProduct_tmul, one_smul]⟩

/-- If the first adic quotient is finite over the original ring, its raw inverse-limit
completion is finite over the canonical completed ring, for any ideal. This generalizes the
finite-generation part of Fujiwara–Kato, Proposition 7.2.16, without asserting intrinsic
completeness for arbitrary ideals. -/
theorem moduleFinite_of_finite_quotient
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Finite (AdicCompletion I R) (AdicCompletion I M) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R (M ⧸ (I • (⊤ : Submodule R M)))
  obtain ⟨f, hf⟩ := Module.projective_lifting_property
    (I • (⊤ : Submodule R M)).mkQ g (Submodule.mkQ_surjective _)
  have hsurj : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ ∘ₗ f) := by
    rwa [hf]
  let e := piEquivFin I n
  let : Module.Finite (AdicCompletion I R) (AdicCompletion I (Fin n → R)) :=
    Module.Finite.equiv e.symm
  exact Module.Finite.of_surjective (map I f)
    (map_surjective_of_mkQ_comp_surjective hsurj)

section SplitKernel

variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

/-- If the original kernel's first adic quotient is finite over the original ring, the kernel
of the completed split surjection is finite over the completed ring, for any ideal. -/
theorem moduleFinite_ker_map_of_rightInverse_of_finite_quotient
    (I : Ideal R) (f : M →ₗ[R] N) (r : N →ₗ[R] M)
    (h : f.comp r = LinearMap.id)
    [Module.Finite R ((LinearMap.ker f) ⧸
      (I • (⊤ : Submodule R (LinearMap.ker f))))] :
    Module.Finite (AdicCompletion I R) (LinearMap.ker (map I f)) := by
  let := moduleFinite_of_finite_quotient I (LinearMap.ker f)
  exact Module.Finite.equiv (kerEquivOfRightInverse I f r h)

end SplitKernel

/-- The completion of a finite module is finite over the completed ring, for any ideal. -/
instance instModuleFinite [Module.Finite R M] :
    Module.Finite (AdicCompletion I R) (AdicCompletion I M) :=
  moduleFinite_of_finite_quotient I M

/-- For a projective module over a commutative ring, the canonical comparison from tensoring
with the completed ring to the completed module is injective, for any ideal. -/
theorem ofTensorProduct_injective_of_projective
    [Module.Projective R M] :
    Function.Injective (ofTensorProduct I M) := by
  obtain ⟨g, hfg⟩ := (Module.projective_def' (R := R) (P := M)).mp inferInstance
  have hsplit :
      (Finsupp.linearCombination R id).baseChange (AdicCompletion I R) ∘ₗ
          g.baseChange (AdicCompletion I R) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_id]
  have hg := LinearMap.injective_of_comp_eq_id _ _ hsplit
  intro x y hxy
  apply hg
  apply ofTensorProduct_injective_finsupp I M
  calc
    ofTensorProduct I (M →₀ R) (g.baseChange (AdicCompletion I R) x) =
        map I g (ofTensorProduct I M x) :=
      (LinearMap.congr_fun (ofTensorProduct_naturality I g) x).symm
    _ = map I g (ofTensorProduct I M y) := congrArg (map I g) hxy
    _ = ofTensorProduct I (M →₀ R) (g.baseChange (AdicCompletion I R) y) :=
      LinearMap.congr_fun (ofTensorProduct_naturality I g) y

/-- For an original projective module finite modulo the ideal, the canonical tensor
comparison is bijective: projectivity gives injectivity and the finite first quotient gives
surjectivity. -/
theorem ofTensorProduct_bijective_of_finite_quotient_of_projective
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M] :
    Function.Bijective (ofTensorProduct I M) :=
  ⟨ofTensorProduct_injective_of_projective I M,
    ofTensorProduct_surjective_of_finite_quotient I M⟩

/-- The canonical tensor comparison as a completed-ring-linear equivalence for an original
projective module whose first adic quotient is finite. -/
noncomputable def ofTensorProductEquivOfFiniteQuotientProjective
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M] :
    AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  LinearEquiv.ofBijective (ofTensorProduct I M)
    (ofTensorProduct_bijective_of_finite_quotient_of_projective I M)

/-- The finite-quotient projective equivalence has the canonical comparison as its linear map. -/
@[simp]
theorem coe_ofTensorProductEquivOfFiniteQuotientProjective
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M] :
    (ofTensorProductEquivOfFiniteQuotientProjective I M).toLinearMap = ofTensorProduct I M :=
  rfl

/-- The finite-quotient projective equivalence sends a pure tensor to the corresponding
scalar multiple in the completed module. -/
@[simp]
theorem ofTensorProductEquivOfFiniteQuotientProjective_apply
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M]
    (a : AdicCompletion I R) (m : M) :
    ofTensorProductEquivOfFiniteQuotientProjective I M (a ⊗ₜ[R] m) = a • of I M m :=
  ofTensorProduct_tmul I M a m

/-- The inverse finite-quotient projective equivalence sends a canonical module element to
its tensor with one. -/
@[simp]
theorem ofTensorProductEquivOfFiniteQuotientProjective_symm_of
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M] (m : M) :
    (ofTensorProductEquivOfFiniteQuotientProjective I M).symm (of I M m) =
      (1 : AdicCompletion I R) ⊗ₜ[R] m := by
  apply (ofTensorProductEquivOfFiniteQuotientProjective I M).injective
  simp

/-- An original projective module finite modulo the ideal has projective completion over the
completed ring, for any ideal. -/
instance instModuleProjectiveOfFiniteQuotient
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M] :
    Module.Projective (AdicCompletion I R) (AdicCompletion I M) :=
  Module.Projective.of_equiv' (ofTensorProductEquivOfFiniteQuotientProjective I M)

/-- For a finite projective module, tensoring with the completed ring gives its adic completion.
This is the finite-original specialization of the finite-first-quotient comparison. -/
theorem ofTensorProduct_bijective_of_finite_of_projective
    [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (ofTensorProduct I M) :=
  ofTensorProduct_bijective_of_finite_quotient_of_projective I M

/-- The canonical tensor comparison as an equivalence over the completed ring for a finite
projective module, specializing the finite-first-quotient equivalence. -/
noncomputable def ofTensorProductEquivOfFiniteProjective
    [Module.Finite R M] [Module.Projective R M] :
    AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  ofTensorProductEquivOfFiniteQuotientProjective I M

/-- The finite-projective equivalence has the canonical tensor comparison as its linear map. -/
@[simp]
theorem coe_ofTensorProductEquivOfFiniteProjective
    [Module.Finite R M] [Module.Projective R M] :
    (ofTensorProductEquivOfFiniteProjective I M).toLinearMap = ofTensorProduct I M :=
  coe_ofTensorProductEquivOfFiniteQuotientProjective I M

/-- The finite-projective equivalence sends a pure tensor to the corresponding scalar multiple
in the completed module. -/
@[simp]
theorem ofTensorProductEquivOfFiniteProjective_apply
    [Module.Finite R M] [Module.Projective R M] (a : AdicCompletion I R) (m : M) :
    ofTensorProductEquivOfFiniteProjective I M (a ⊗ₜ[R] m) = a • of I M m :=
  ofTensorProductEquivOfFiniteQuotientProjective_apply I M a m

/-- The inverse finite-projective equivalence sends a canonical module element to its tensor
with one. -/
@[simp]
theorem ofTensorProductEquivOfFiniteProjective_symm_of
    [Module.Finite R M] [Module.Projective R M] (m : M) :
    (ofTensorProductEquivOfFiniteProjective I M).symm (of I M m) =
      (1 : AdicCompletion I R) ⊗ₜ[R] m :=
  ofTensorProductEquivOfFiniteQuotientProjective_symm_of I M m

-- Keep the old definition reducible for explicit callers, without a second instance.
set_option linter.defProp false in
/-- The finite-original specialization of completed projectivity. Instance search uses the
more general `instModuleProjectiveOfFiniteQuotient`. -/
@[instance_reducible]
noncomputable def instModuleProjective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective (AdicCompletion I R) (AdicCompletion I M) :=
  instModuleProjectiveOfFiniteQuotient I M

/-- For a finite module over a commutative Noetherian ring, the canonical comparison from
tensoring with the completed ring to the completed module is bijective for every ideal.
This generalizes the finite-Noetherian comparison of Judith Ludwig and Christian Merten in
Mathlib to independent ring and module universes. -/
theorem ofTensorProduct_bijective [IsNoetherianRing R] [Module.Finite R M] :
    Function.Bijective (ofTensorProduct I M) := by
  have : Small.{uR} M := Module.Finite.small R M
  let e : M ≃ₗ[R] Shrink.{uR} M := (Shrink.linearEquiv R M).symm
  let : Module.Finite R (Shrink.{uR} M) := Module.Finite.equiv e
  have hc := ofTensorProduct_bijective_of_finite_of_isNoetherian I (Shrink.{uR} M)
  have he : Function.Bijective (map I e.toLinearMap) := (congr I e).bijective
  apply (Function.Bijective.of_comp_iff' he _).mp
  change Function.Bijective (map I e.toLinearMap ∘ₗ ofTensorProduct I M)
  rw [ofTensorProduct_naturality]
  exact hc.comp (e.baseChange R (AdicCompletion I R) _ _).bijective

section Noetherian

variable {R : Type uR} [CommRing R] (I : Ideal R)
variable (M : Type uR) [AddCommGroup M] [Module R M]

/-- On the finite-original Noetherian overlap, the finite-quotient projective equivalence
agrees with Mathlib's finite-module Noetherian equivalence through their canonical maps. -/
theorem ofTensorProductEquivOfFiniteQuotientProjective_eq_ofFiniteNoetherian
    [Module.Finite R M] [Module.Projective R M] [IsNoetherianRing R] :
    ofTensorProductEquivOfFiniteQuotientProjective I M =
      ofTensorProductEquivOfFiniteNoetherian I M := by
  ext x
  rfl

/-- When the ring is Noetherian, the finite-projective equivalence agrees with Mathlib's
finite-module Noetherian equivalence: both have the same canonical underlying map. -/
theorem ofTensorProductEquivOfFiniteProjective_eq_ofFiniteNoetherian
    [Module.Finite R M] [Module.Projective R M] [IsNoetherianRing R] :
    ofTensorProductEquivOfFiniteProjective I M = ofTensorProductEquivOfFiniteNoetherian I M :=
  ofTensorProductEquivOfFiniteQuotientProjective_eq_ofFiniteNoetherian I M

/-- Mathlib's finite-Noetherian equivalence is the equivalence obtained from the canonical
completed-ring-linear comparison and its bijectivity. -/
theorem ofTensorProductEquivOfFiniteNoetherian_eq_ofBijective
    [IsNoetherianRing R] [Module.Finite R M] :
    ofTensorProductEquivOfFiniteNoetherian I M =
      LinearEquiv.ofBijective (ofTensorProduct I M) (ofTensorProduct_bijective I M) := by
  apply LinearEquiv.ext
  intro x
  exact ofTensorProductEquivOfFiniteNoetherian_apply I M x

end Noetherian

end AdicCompletion

namespace AdicCompletion

section Hausdorffification

variable {R : Type uR} [CommRing R] (I : Ideal R)
variable (M : Type uM) [AddCommGroup M] [Module R M]

/-- At a finitely generated ideal-power stage, evaluation after the tensor comparison
has precisely the extended ideal-power kernel. The quotient calculation is over `R`;
no completed-ring action on the original module is used. -/
private theorem eval_ofTensorProduct_eq_zero_iff (k : ℕ) (hk : (I ^ k).FG)
    (t : AdicCompletion I R ⊗[R] M) :
    eval I M k (ofTensorProduct I M t) = 0 ↔
      t ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ k •
        (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I R ⊗[R] M)) := by
  let S := AdicCompletion I R
  let T := S ⊗[R] M
  let K := (I.map (algebraMap R S)) ^ k
  let e : (T ⧸ K • (⊤ : Submodule S T)) ≃ₗ[R]
      M ⧸ (I ^ k • (⊤ : Submodule R M)) :=
    ((quotTensorEquivQuotSMul T K).symm.restrictScalars R).trans
      (((AlgebraTensorModule.cancelBaseChange R S S (S ⧸ K) M).restrictScalars R).trans
        ((TensorProduct.congr (quotientPowAlgEquiv I k hk).toLinearEquiv
          (LinearEquiv.refl R M)).trans (quotTensorEquivQuotSMul M (I ^ k))))
  have he : e.toLinearMap ∘ₗ
      ((K • (⊤ : Submodule S T)).mkQ.restrictScalars R) =
      (eval I M k) ∘ₗ (ofTensorProduct I M).restrictScalars R := by
    apply TensorProduct.ext'
    intro a m
    have ha : a • (1 : S ⧸ K) = Ideal.Quotient.mk K a := by
      change a • Submodule.Quotient.mk (p := K) (1 : S) = _
      rw [← Submodule.Quotient.mk_smul]
      simp only [smul_eq_mul, mul_one]
      rfl
    change e (Submodule.Quotient.mk (a ⊗ₜ[R] m)) =
      eval I M k (ofTensorProduct I M (a ⊗ₜ[R] m))
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      quotTensorEquivQuotSMul_symm_mk]
    rw [AlgebraTensorModule.cancelBaseChange_tmul R S S (1 : S ⧸ K) m a,
      ha, TensorProduct.congr_tmul]
    change quotTensorEquivQuotSMul M (I ^ k)
      (quotientPowAlgEquiv I k hk (Ideal.Quotient.mk K a) ⊗ₜ[R] m) = _
    rw [quotientPowAlgEquiv_mk, ofTensorProduct_tmul]
    change quotTensorEquivQuotSMul M (I ^ k) (evalₐ I k a ⊗ₜ[R] m) =
      a.val k • (of I M m).val k
    rw [val_smul_eq_evalₐ_smul, of_apply]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I k a)
    rw [← hr, quotTensorEquivQuotSMul_mk_tmul]
    rfl
  have het := LinearMap.congr_fun he t
  change e (Submodule.Quotient.mk t) = eval I M k (ofTensorProduct I M t) at het
  rw [← het, e.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

/-- If a positive power of the ideal is finitely generated, the kernel of the canonical
tensor comparison is the intersection of the extended ideal-power submodules. No finiteness
or separation of the original module is required. -/
theorem ker_ofTensorProduct_eq_iInf_of_fg_pow
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) :
    (ofTensorProduct I M).ker =
      (⨅ k : ℕ,
        (I.map (algebraMap R (AdicCompletion I R))) ^ k •
          (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I R ⊗[R] M))) := by
  have hfg (k : ℕ) : (I ^ (n * k)).FG := by
    rw [pow_mul]
    exact hI.pow
  ext t
  constructor
  · intro ht
    apply (Submodule.mem_iInf _).mpr
    intro k
    have hzero : eval I M (n * k) (ofTensorProduct I M t) = 0 := by
      rw [LinearMap.mem_ker.mp ht]
      exact (eval I M (n * k)).map_zero
    exact Submodule.pow_smul_top_le _ _ (Nat.le_mul_of_pos_left k hn)
      ((eval_ofTensorProduct_eq_zero_iff I M (n * k) (hfg k) t).mp hzero)
  · intro ht
    change ofTensorProduct I M t = 0
    apply AdicCompletion.ext
    intro k
    have hzero := (eval_ofTensorProduct_eq_zero_iff I M (n * k) (hfg k) t).mpr
      ((Submodule.mem_iInf _).mp ht (n * k))
    change eval I M k (ofTensorProduct I M t) = 0
    calc
      _ = transitionMap I M (Nat.le_mul_of_pos_left k hn)
          (eval I M (n * k) (ofTensorProduct I M t)) :=
        (transitionMap_comp_eval_apply I M _ _).symm
      _ = 0 := by rw [hzero]; rfl

/-- Under finite generation of a positive ideal power, the canonical tensor comparison is
injective exactly when its source is Hausdorff for the original ideal action. -/
theorem ofTensorProduct_injective_iff_isHausdorff_of_fg_pow
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) :
    Function.Injective (ofTensorProduct I M) ↔
      IsHausdorff I (AdicCompletion I R ⊗[R] M) := by
  rw [← LinearMap.ker_eq_bot, ker_ofTensorProduct_eq_iInf_of_fg_pow I M hn hI]
  constructor
  · intro h
    apply (IsHausdorff.map_algebraMap_iff (I := I) (S := AdicCompletion I R)).mp
    refine ⟨fun t ht => ?_⟩
    have hm := (Submodule.mem_iInf (fun k : ℕ =>
      (I.map (algebraMap R (AdicCompletion I R))) ^ k •
        (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I R ⊗[R] M)))).mpr
      (fun k => SModEq.zero.mp (ht k))
    rw [h] at hm
    exact (Submodule.mem_bot _).mp hm
  · intro h
    exact ((IsHausdorff.map_algebraMap_iff (I := I)
      (S := AdicCompletion I R)).mpr h).iInf_pow_smul

/-- For a module finite modulo the original ideal, the canonical tensor comparison identifies
its source's Hausdorffification with the completed module, provided a positive ideal power is
finitely generated. The equivalence is induced by the same tensor comparison. -/
noncomputable def ofTensorProductHausdorffificationEquivOfFiniteQuotient
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] :
    Hausdorffification
      (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R ⊗[R] M)
        ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  (Submodule.quotEquivOfEq _ _ (ker_ofTensorProduct_eq_iInf_of_fg_pow I M hn hI).symm).trans
    ((ofTensorProduct I M).quotKerEquivOfSurjective
      (ofTensorProduct_surjective_of_finite_quotient I M))

/-- The Hausdorffification equivalence composed with the quotient projection is the
canonical tensor comparison on the whole tensor product. -/
theorem ofTensorProductHausdorffificationEquivOfFiniteQuotient_comp_of
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] :
    (ofTensorProductHausdorffificationEquivOfFiniteQuotient I M hn hI).toLinearMap
        ∘ₗ Hausdorffification.of (I.map (algebraMap R (AdicCompletion I R)))
          (AdicCompletion I R ⊗[R] M) =
      ofTensorProduct I M := by
  ext t
  rfl

/-- The Hausdorffification equivalence sends the class of any tensor to its canonical
comparison image. -/
@[simp]
theorem ofTensorProductHausdorffificationEquivOfFiniteQuotient_apply_of
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))]
    (t : AdicCompletion I R ⊗[R] M) :
    ofTensorProductHausdorffificationEquivOfFiniteQuotient I M hn hI
        (Hausdorffification.of (I.map (algebraMap R (AdicCompletion I R)))
          (AdicCompletion I R ⊗[R] M) t) =
      ofTensorProduct I M t :=
  LinearMap.congr_fun
    (ofTensorProductHausdorffificationEquivOfFiniteQuotient_comp_of I M hn hI) t

/-- The inverse Hausdorffification equivalence sends a comparison image to the class of
the original tensor. -/
@[simp]
theorem ofTensorProductHausdorffificationEquivOfFiniteQuotient_symm_apply
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))]
    (t : AdicCompletion I R ⊗[R] M) :
    (ofTensorProductHausdorffificationEquivOfFiniteQuotient I M hn hI).symm
        (ofTensorProduct I M t) =
      Hausdorffification.of (I.map (algebraMap R (AdicCompletion I R)))
        (AdicCompletion I R ⊗[R] M) t := by
  rw [← ofTensorProductHausdorffificationEquivOfFiniteQuotient_apply_of I M hn hI t,
    LinearEquiv.symm_apply_apply]

/-- The inverse Hausdorffification equivalence sends an original module element to the
class of its tensor with one. -/
@[simp]
theorem ofTensorProductHausdorffificationEquivOfFiniteQuotient_symm_of
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] (m : M) :
    (ofTensorProductHausdorffificationEquivOfFiniteQuotient I M hn hI).symm
        (of I M m) =
      Hausdorffification.of (I.map (algebraMap R (AdicCompletion I R)))
        (AdicCompletion I R ⊗[R] M) ((1 : AdicCompletion I R) ⊗ₜ[R] m) := by
  simpa only [ofTensorProduct_tmul, one_smul] using
    ofTensorProductHausdorffificationEquivOfFiniteQuotient_symm_apply I M hn hI
      ((1 : AdicCompletion I R) ⊗ₜ[R] m)

/-- For a module finite modulo the original ideal, the comparison is bijective exactly when
the tensor source is Hausdorff. This follows by factoring through the Hausdorffification
equivalence and its quotient projection. -/
theorem ofTensorProduct_bijective_iff_isHausdorff_of_fg_pow
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] :
    Function.Bijective (ofTensorProduct I M) ↔
      IsHausdorff I (AdicCompletion I R ⊗[R] M) := by
  constructor
  · intro h
    exact (ofTensorProduct_injective_iff_isHausdorff_of_fg_pow I M hn hI).mp h.1
  · intro h
    have hJ : IsHausdorff (I.map (algebraMap R (AdicCompletion I R)))
        (AdicCompletion I R ⊗[R] M) := IsHausdorff.map_algebraMap_iff.mpr h
    have hq : Function.Bijective
        (Hausdorffification.of (I.map (algebraMap R (AdicCompletion I R)))
          (AdicCompletion I R ⊗[R] M)) := by
      refine ⟨?_, Submodule.mkQ_surjective _⟩
      apply LinearMap.ker_eq_bot.mp
      rw [Hausdorffification.of, Submodule.ker_mkQ]
      exact hJ.iInf_pow_smul
    rw [← ofTensorProductHausdorffificationEquivOfFiniteQuotient_comp_of I M hn hI]
    exact (ofTensorProductHausdorffificationEquivOfFiniteQuotient I M hn hI).bijective.comp hq

end Hausdorffification

end AdicCompletion
