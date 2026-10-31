/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Exactness
public import AdicModules.AdicCompletion.TensorProduct
public import Mathlib.Algebra.Module.FinitePresentation

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Filtration

/-!
# Finite presentation and adic completion

For any ideal `I` of a commutative ring `R`, a module `M` with finite original first quotient
`M / I M` has finitely presented raw completion over the canonical completed ring whenever
`AdicCompletion I R ⊗[R] M` is projective over that ring. This uses finite-first-quotient
completion finiteness, projectivity transported through the canonical tensor comparison,
and stock finite-plus-projective finite presentation. It requires no finite-free cofinality,
original-module finiteness, projectivity, flatness or separation, or finite generation of `I`.
Original projectivity supplies projectivity of the tensor source by base change; the
original-projective theorem is retained with its original hypotheses.

A separate comparison concerns finitely presented original modules. Let `R` be a commutative
ring and `I` any ideal. Suppose that, for every finitely generated submodule `K` of a finite
power of `R`, the induced `I`-adic filtration on `K` is cofinal with
its intrinsic `I`-adic filtration. For a finitely presented `R`-module `M`, the canonical map
`AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M` is then bijective.

The resulting equivalence has precisely this canonical map as its forward map. Its
pure-tensor and inverse-on-canonical-element formulas determine its compatibility with the
finite-projective and finite-Noetherian comparisons. The ring and module universes are
independent, except in the overlap with Mathlib's finite-Noetherian equivalence.

The proof uses a finite free presentation, middle exactness of completion under range
cofinality, and an element chase with the canonical finite-power comparisons. Only
surjectivity and a zero composite are needed on the tensor side, not tensor middle exactness.
Finite presentation supplies finite generation of the relation range and of `M`; no
Noetherian, finite-generation-of-`I`, projectivity or flatness assumption is imposed.

The completion here is Mathlib's algebraic inverse limit of the quotients by powers of `I`.
The comparison assumes finite-free cofinality; it does not assert an intrinsic or universal
completeness property. Identifications with other completion conventions and changes of
tensor-factor order require separate bridges.

## References

Fujiwara–Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5 (2017),
Proposition 7.4.15, motivates the completion–tensor comparison. The theorem here is stated
for arbitrary `I` under the finite-free cofinality hypothesis above.

Mathlib's `RingTheory/AdicCompletion/AsTensorProduct.lean`, by Judith Ludwig and Christian
Merten, supplies the canonical comparison, its naturality, finite-power bijectivity,
finite-module surjectivity and the finite-Noetherian comparison. The range-cofinality
exactness theorem follows their Cauchy-sequence approach in
`Mathlib.RingTheory.AdicCompletion.Exactness`. Finite presentations and tensor surjectivity
are reused from Mathlib. The Noetherian bridge uses Mathlib's Artin–Rees lemma
`Ideal.exists_pow_inf_eq_pow_smul` and `Module.finitePresentation_of_finite`.
The completed-module finite-presentation theorem uses Andrew Yang's formalization
`Module.finitePresentation_of_projective` in `Mathlib.Algebra.Module.FinitePresentation`.
-/

@[expose] public section

noncomputable section

universe uR uM

open TensorProduct

namespace AdicCompletion

/-- If the original first quotient is finite and the completed scalar extension is
projective, the raw completion is finitely presented over the completed ring, for any ideal.
No cofinality, finiteness or projectivity assumption on the original module is needed. -/
theorem moduleFinitePresentation_of_finite_quotient_of_projective_tensorProduct
    {R : Type uR} [CommRing R] (I : Ideal R)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))]
    [Module.Projective (AdicCompletion I R) (AdicCompletion I R ⊗[R] M)] :
    Module.FinitePresentation (AdicCompletion I R) (AdicCompletion I M) := by
  let := moduleFinite_of_finite_quotient I M
  let : Module.Projective (AdicCompletion I R) (AdicCompletion I M) :=
    Module.Projective.of_equiv (ofTensorProductEquivOfFiniteQuotientProjectiveTensorProduct I M)
  exact Module.finitePresentation_of_projective (AdicCompletion I R) (AdicCompletion I M)

/-- An original projective module with finite first adic quotient has finitely presented
completion over the canonical completed ring, for any ideal. No cofinality assumption on
finite free submodules is needed for this conclusion. -/
theorem moduleFinitePresentation_of_finite_quotient_of_projective
    {R : Type uR} [CommRing R] (I : Ideal R)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M] :
    Module.FinitePresentation (AdicCompletion I R) (AdicCompletion I M) :=
  moduleFinitePresentation_of_finite_quotient_of_projective_tensorProduct I M

section FinitePresentation

variable {R : Type uR} [CommRing R] (I : Ideal R)
variable (M : Type uM) [AddCommGroup M] [Module R M] [hfp : Module.FinitePresentation R M]
variable (hcofinal : ∀ (n : ℕ) (K : Submodule R (Fin n → R)), K.FG →
  ∀ k : ℕ, ∃ l : ℕ, K ⊓ (I ^ l • ⊤ : Submodule R (Fin n → R)) ≤ I ^ k • K)

include hfp hcofinal

/-- The canonical tensor comparison is bijective for a finitely presented module when the
induced and intrinsic adic filtrations are cofinal on every finitely generated submodule of
a finite free module.

This uses Mathlib's algebraic inverse-limit completion. Compare Fujiwara–Kato,
*Foundations of Rigid Geometry I*, arXiv:1308.4734v5 (2017), Proposition 7.4.15:
that statement assumes a finitely generated ideal and (APf), whereas the input here is
explicit finite-free cofinality for arbitrary `I`. Identifications with its completion
convention and tensor-factor order require separate bridges. -/
theorem ofTensorProduct_bijective_of_finitePresentation :
    Function.Bijective (ofTensorProduct I M) := by
  obtain ⟨q, p, g, f, hg, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  let S := AdicCompletion I R
  let cA := ofTensorProduct I (Fin p → R)
  let cB := ofTensorProduct I (Fin q → R)
  let Tf := f.baseChange S
  let Tg := g.baseChange S
  have hA : Function.Bijective cA :=
    ofTensorProduct_bijective_of_pi_of_fintype I (Fin p)
  have hB : Function.Bijective cB :=
    ofTensorProduct_bijective_of_pi_of_fintype I (Fin q)
  have hC : Function.Exact (map I f) (map I g) :=
    map_exact_of_range_cofinal hfg hg
      (hcofinal q (LinearMap.range f) (Submodule.fg_range f))
  have hnatf (a : S ⊗[R] (Fin p → R)) :
      map I f (cA a) = cB (Tf a) :=
    LinearMap.congr_fun (ofTensorProduct_naturality I f) a
  have hnatg (b : S ⊗[R] (Fin q → R)) :
      map I g (cB b) = ofTensorProduct I M (Tg b) :=
    LinearMap.congr_fun (ofTensorProduct_naturality I g) b
  have hTg : Function.Surjective Tg := by
    simpa only [Tg, LinearMap.baseChange_eq_ltensor] using
      (LinearMap.lTensor_surjective S hg)
  have hgf : g ∘ₗ f = 0 := by
    apply LinearMap.ext
    intro a
    exact (hfg (f a)).mpr ⟨a, rfl⟩
  have hTgf : Tg ∘ₗ Tf = 0 := by
    dsimp only [Tg, Tf]
    rw [← LinearMap.baseChange_comp, hgf, LinearMap.baseChange_zero]
  have hker : ∀ t, ofTensorProduct I M t = 0 → t = 0 := by
    intro t ht
    obtain ⟨b, hb⟩ := hTg t
    have hb0 : map I g (cB b) = 0 := by
      rw [hnatg b, hb, ht]
    obtain ⟨y, hy⟩ := (hC (cB b)).mp hb0
    obtain ⟨a, ha⟩ := hA.surjective y
    have hfb : Tf a = b := hB.injective <|
      (hnatf a).symm.trans ((congrArg (map I f) ha).trans hy)
    calc
      t = Tg b := hb.symm
      _ = Tg (Tf a) := congrArg Tg hfb.symm
      _ = 0 := LinearMap.congr_fun hTgf a
  refine ⟨?_, ofTensorProduct_surjective_of_finite I M⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker (x - y)
  simp only [map_sub, hxy, sub_self]

/-- The canonical completion–tensor equivalence for a finitely presented module under
finite-free cofinality, linear over the completed ring. -/
def ofTensorProductEquivOfFinitePresentation :
    AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  LinearEquiv.ofBijective (ofTensorProduct I M)
    (ofTensorProduct_bijective_of_finitePresentation I M hcofinal)

/-- The finite-presentation equivalence has the canonical comparison as its linear map. -/
@[simp]
theorem coe_ofTensorProductEquivOfFinitePresentation :
    (ofTensorProductEquivOfFinitePresentation I M hcofinal).toLinearMap =
      ofTensorProduct I M :=
  rfl

/-- The finite-presentation equivalence sends pure tensors to scalar multiples of canonical
module elements. -/
@[simp]
theorem ofTensorProductEquivOfFinitePresentation_apply (a : AdicCompletion I R) (m : M) :
    ofTensorProductEquivOfFinitePresentation I M hcofinal (a ⊗ₜ[R] m) = a • of I M m :=
  ofTensorProduct_tmul I M a m

/-- The inverse finite-presentation equivalence sends a canonical module element to its
tensor with one. -/
@[simp]
theorem ofTensorProductEquivOfFinitePresentation_symm_of (m : M) :
    (ofTensorProductEquivOfFinitePresentation I M hcofinal).symm (of I M m) =
      (1 : AdicCompletion I R) ⊗ₜ[R] m := by
  apply (ofTensorProductEquivOfFinitePresentation I M hcofinal).injective
  simp

/-- Any completed-ring-linear equivalence with the canonical forward map is the
finite-presentation equivalence. In particular the construction is independent of the
finite presentation and of the cofinality witness. -/
theorem ofTensorProductEquivOfFinitePresentation_unique
    (E : AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M)
    (hE : E.toLinearMap = ofTensorProduct I M) :
    E = ofTensorProductEquivOfFinitePresentation I M hcofinal := by
  apply LinearEquiv.toLinearMap_injective
  exact hE.trans (coe_ofTensorProductEquivOfFinitePresentation I M hcofinal).symm

/-- Where both apply, the finite-presentation and finite-projective equivalences agree,
since their forward maps are the same canonical comparison. -/
theorem ofTensorProductEquivOfFinitePresentation_eq_ofFiniteProjective
    [Module.Projective R M] :
    ofTensorProductEquivOfFinitePresentation I M hcofinal =
      ofTensorProductEquivOfFiniteProjective I M := by
  ext x
  rfl

end FinitePresentation

section NoetherianCofinality

variable {R : Type uR} [CommRing R] (I : Ideal R)

/-- Artin–Rees supplies induced/intrinsic cofinality on every submodule of a finite free
module over a Noetherian ring.
Together with `Module.finitePresentation_of_finite`, this recovers the hypotheses of the
finite-presentation comparison from those of the finite-Noetherian comparison. -/
theorem finite_free_cofinality_of_isNoetherian [IsNoetherianRing R] :
    ∀ (n : ℕ) (K : Submodule R (Fin n → R)) (k : ℕ),
      ∃ l : ℕ, K ⊓ (I ^ l • ⊤ : Submodule R (Fin n → R)) ≤ I ^ k • K := by
  intro n K k
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I K
  refine ⟨k + c, ?_⟩
  rw [inf_comm, hc (k + c) (Nat.le_add_left c k), Nat.add_sub_cancel]
  exact smul_mono_right _ inf_le_right

end NoetherianCofinality

section Noetherian

-- Mathlib's finite-Noetherian equivalence requires this common universe.
variable {R : Type uR} [CommRing R] (I : Ideal R)
variable (M : Type uR) [AddCommGroup M] [Module R M]

/-- Where both apply, the finite-presentation equivalence agrees with Mathlib's
finite-Noetherian equivalence by equality of canonical forward maps. -/
theorem ofTensorProductEquivOfFinitePresentation_eq_ofFiniteNoetherian
    [Module.FinitePresentation R M] [IsNoetherianRing R]
    (hcofinal : ∀ (n : ℕ) (K : Submodule R (Fin n → R)), K.FG →
      ∀ k : ℕ, ∃ l : ℕ, K ⊓ (I ^ l • ⊤ : Submodule R (Fin n → R)) ≤ I ^ k • K) :
    ofTensorProductEquivOfFinitePresentation I M hcofinal =
      ofTensorProductEquivOfFiniteNoetherian I M := by
  ext x
  rfl

/-- The stock finite-Noetherian hypotheses derive both finite presentation and finite-free
cofinality, and the resulting equivalence is still the stock canonical equivalence. -/
theorem ofTensorProductEquivOfFiniteNoetherian_eq_ofFinitePresentation
    [Module.Finite R M] [IsNoetherianRing R] :
    ofTensorProductEquivOfFiniteNoetherian I M =
      ofTensorProductEquivOfFinitePresentation I M
        (fun n K _ => finite_free_cofinality_of_isNoetherian I n K)
        (hfp := Module.finitePresentation_of_finite R M) := by
  ext x
  rfl

end Noetherian

end AdicCompletion
