/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.TensorProduct
public import AdicModules.Ideal.Cotangent

import AdicModules.AdicCompletion.Completeness
import AdicModules.Noetherian
import Mathlib.RingTheory.Nakayama

/-!
# Modules over adically complete bases

Let `I` be any ideal of a commutative ring `R` that is `I`-adically precomplete.
If the original quotient `M / I M` is finite over `R / I`, then `M` is precomplete.
If `M` is also `I`-Hausdorff, then it is finite over `R`.

When the base is fully `I`-adically complete, a module with finite projective first
quotient and flat positive power quotients is projective over `R` if it is Hausdorff
or finite over `R`. The finite-module branch does not assume original Hausdorffness:
the canonical completion surjection splits, its kernel is finite as a split image,
and finite Nakayama kills that kernel. A finite original-flat specialization uses
the usual quotient base change rather than a second projectivity argument.

Precompleteness of the base makes the canonical coefficient map to `AdicCompletion I R`
surjective. Tensoring this map with `M` shows that every tensor is `1 ⊗ m` for some
original `m`. The finite-first-quotient tensor comparison therefore makes the canonical
map `M → AdicCompletion I M` surjective. Completed finiteness descends along the same
coefficient map, and Hausdorffness identifies the original module with its completion.

The two precompleteness and finiteness results need no Hausdorffness of the base.
The projectivity criteria retain full base completeness and their separate original-module
floors. These module criteria require no finite generation of `I` or a positive power,
Noetherianity, original projectivity or original completeness. The ring and module universes
are independent. All actions are the canonical ones; no completed-ring action on the original
module is added. Raw completion is not asserted intrinsically complete for an arbitrary ideal.

For a fully complete base, an ideal is finitely generated exactly when its canonical
conormal module `I.Cotangent` is finite over `R / I`. The ideal subtype inherits
Hausdorffness from the base, and the conormal is its first adic quotient, so the
Hausdorff-module finiteness criterion applies to the original ideal module.
Consequently, the complete base is Noetherian exactly when its residue ring is
Noetherian and its conormal module is finite. The Noetherian implication uses the
finitely generated ideal criterion from `AdicModules.Noetherian`.

## References

The finite-first-quotient comparison and completed finiteness are from
`AdicModules.AdicCompletion.TensorProduct`. Mathlib's adic-completion API by Kenny Lau,
Judith Ludwig, Christian Merten and Jiedong Jiang supplies the canonical maps and their
completeness criteria. The coefficient-lifting step uses Antoine Chambert-Loir's tensor
right-exactness API and the tensor left unitor from Kenny Lau and Mario Carneiro's
associator API. Finiteness uses Johan Commelin's scalar-tower, quotient,
surjective-image and linear-equivalence transport results. Kevin Buzzard and Antoine
Labelle's projectivity API supplies semilinear transport and liftings; the split-kernel
range formula and Chris Hughes's finite Nakayama theorem give the finite-module argument.
Andrew Yang's `RingTheory/Ideal/Cotangent.lean` supplies the canonical conormal module,
its quotient action and its quotient map. The Noetherian consequence uses this library's
formalization of the finitely generated ideal criterion from K. Fujiwara and F. Kato,
*Foundations of Rigid Geometry I*, arXiv:1308.4734v5.
-/

set_option warningAsError true

@[expose] public section

universe uR uM

open TensorProduct

/-- Over an adically precomplete commutative ring, a module finite modulo the ideal
is precomplete. Neither the base nor the original module needs to be Hausdorff. -/
theorem IsPrecomplete.of_finite_quotient
    {R : Type uR} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    IsPrecomplete I M := by
  let : Module.Finite R (M ⧸ (I • (⊤ : Submodule R M))) :=
    Module.Finite.trans (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))
  have hone : AdicCompletion.of I R 1 = (1 : AdicCompletion I R) := by
    simpa only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      using (map_one (algebraMap R (AdicCompletion I R)))
  -- Surjectivity of the coefficient map lifts all tensors from the scalar left unitor.
  have hj : Function.Surjective
      ((AdicCompletion.of I R).rTensor M ∘ₗ
        (TensorProduct.lid R M).symm.toLinearMap) :=
    (LinearMap.rTensor_surjective M (AdicCompletion.of_surjective I R)).comp
      (TensorProduct.lid R M).symm.surjective
  apply AdicCompletion.of_surjective_iff.mp
  intro x
  obtain ⟨t, ht⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite_quotient I M x
  obtain ⟨m, hm⟩ := hj t
  have hm' : (1 : AdicCompletion I R) ⊗ₜ[R] m = t := by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, hone] using hm
  refine ⟨m, ?_⟩
  rw [← ht, ← hm', AdicCompletion.ofTensorProduct_tmul, one_smul]

/-- Over an adically precomplete commutative ring, a Hausdorff module finite modulo the
ideal is finite over the original ring. No Hausdorffness of the base is required. -/
theorem IsPrecomplete.moduleFinite_of_isHausdorff_of_finite_quotient
    {R : Type uR} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (M : Type uM) [AddCommGroup M] [Module R M]
    [IsHausdorff I M]
    [Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Finite R M := by
  let : Module.Finite R (M ⧸ (I • (⊤ : Submodule R M))) :=
    Module.Finite.trans (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))
  let : Module.Finite R (AdicCompletion I R) :=
    Module.Finite.of_surjective (AdicCompletion.of I R) (AdicCompletion.of_surjective I R)
  let : Module.Finite (AdicCompletion I R) (AdicCompletion I M) :=
    AdicCompletion.moduleFinite_of_finite_quotient I M
  let : Module.Finite R (AdicCompletion I M) :=
    Module.Finite.trans (AdicCompletion I R) (AdicCompletion I M)
  let : IsAdicComplete I M :=
    { toIsHausdorff := inferInstance
      toIsPrecomplete := IsPrecomplete.of_finite_quotient I M }
  exact Module.Finite.equiv (AdicCompletion.ofLinearEquiv I M).symm

namespace AdicCompletion

/-- Restriction along the canonical coefficient isomorphism preserves projectivity
of the completed module. -/
private theorem moduleProjective_restrictScalars
    {R : Type uR} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Projective (AdicCompletion I R) (AdicCompletion I M)] :
    Module.Projective R (AdicCompletion I M) := by
  let e : R ≃+* AdicCompletion I R := (ofAlgEquiv (S := R) I).toRingEquiv
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let c : LinearEquiv e.symm.toRingHom (σ' := e.toRingHom)
      (AdicCompletion I M) (AdicCompletion I M) :=
    { AddEquiv.refl (AdicCompletion I M) with
      map_smul' := by
        intro s x
        change s • x = e.symm s • x
        have hs : algebraMap R (AdicCompletion I R) (e.symm s) = s := by
          change e (e.symm s) = s
          exact e.apply_symm_apply s
        calc
          s • x = (algebraMap R (AdicCompletion I R) (e.symm s)) • x :=
            congrArg (fun t : AdicCompletion I R => t • x) hs.symm
          _ = e.symm s • x := by rw [IsScalarTower.algebraMap_smul] }
  exact Module.Projective.of_equiv c

end AdicCompletion

namespace IsAdicComplete

/-- A finite module over a complete base is projective if its raw completion is
projective over the original ring. -/
private theorem moduleProjective_of_finite_of_projective_completion
    {R : Type uR} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R (AdicCompletion I M)] :
    Module.Projective R M := by
  let : Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ I) _
  let : IsPrecomplete I M := IsPrecomplete.of_finite_quotient I M
  let p : M →ₗ[R] AdicCompletion I M := AdicCompletion.of I M
  have hsurj : Function.Surjective p := AdicCompletion.of_surjective I M
  obtain ⟨j, hj⟩ := Module.projective_lifting_property p
    (LinearMap.id : AdicCompletion I M →ₗ[R] AdicCompletion I M) hsurj
  let δ : M →ₗ[R] M := LinearMap.id - j.comp p
  have hker : p.ker = δ.range := LinearMap.ker_eq_range_of_comp_eq_id hj
  -- The kernel is finite as an image of the finite original module.
  have hfg : p.ker.FG := by
    rw [hker]
    exact Submodule.fg_range δ
  have hker_le : p.ker ≤ I • (⊤ : Submodule R M) := by
    simpa only [p, AdicCompletion.eval_comp_of, Submodule.ker_mkQ, pow_one] using
      (LinearMap.ker_le_ker_comp p (AdicCompletion.eval I M 1))
  have hδ (x : M) (hx : x ∈ p.ker) : δ x = x := by
    have hpx : p x = 0 := LinearMap.mem_ker.mp hx
    simp only [δ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      hpx, map_zero, sub_zero]
  have hmap : (I • (⊤ : Submodule R M)).map δ = I • p.ker := by
    rw [Submodule.map_smul'', Submodule.map_top, ← hker]
  -- Applying the split projection upgrades ker(p) ≤ I M to ker(p) ≤ I ker(p).
  have hle : p.ker ≤ I • p.ker := by
    intro x hx
    rw [← hmap]
    exact ⟨x, hker_le hx, hδ x hx⟩
  have hbot : p.ker = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I p.ker hfg hle
      (IsAdicComplete.le_jacobson_bot I)
  let e : M ≃ₗ[R] AdicCompletion I M :=
    LinearEquiv.ofBijective p ⟨LinearMap.ker_eq_bot.mp hbot, hsurj⟩
  exact Module.Projective.of_equiv' e.symm

end IsAdicComplete

/-- Over an adically complete commutative ring, a Hausdorff module with finite projective
first quotient and flat positive power quotients is projective over the original ring. -/
theorem IsAdicComplete.moduleProjective_of_isHausdorff_of_flat_pow_quotients
    {R : Type uR} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type uM) [AddCommGroup M] [Module R M]
    [IsHausdorff I M]
    [Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    (hflat : ∀ k : ℕ, 0 < k →
      Module.Flat (R ⧸ I ^ k) (M ⧸ (I ^ k • (⊤ : Submodule R M)))) :
    Module.Projective R M := by
  let : Module.Projective (AdicCompletion I R) (AdicCompletion I M) :=
    AdicCompletion.moduleProjective_of_flat_pow_quotients I M hflat
  let : Module.Projective R (AdicCompletion I M) :=
    AdicCompletion.moduleProjective_restrictScalars I M
  let : IsAdicComplete I M :=
    { toIsHausdorff := inferInstance
      toIsPrecomplete := IsPrecomplete.of_finite_quotient I M }
  exact Module.Projective.of_equiv' (AdicCompletion.ofLinearEquiv I M).symm

/-- Over an adically complete commutative ring, a finite module with projective first
quotient and flat positive power quotients is projective. Hausdorffness of the original
module is not assumed: a split completion kernel is killed by finite Nakayama. -/
theorem IsAdicComplete.moduleProjective_of_finite_of_flat_pow_quotients
    {R : Type uR} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    (hflat : ∀ k : ℕ, 0 < k →
      Module.Flat (R ⧸ I ^ k) (M ⧸ (I ^ k • (⊤ : Submodule R M)))) :
    Module.Projective R M := by
  let : Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ I) _
  let : Module.Projective (AdicCompletion I R) (AdicCompletion I M) :=
    AdicCompletion.moduleProjective_of_flat_pow_quotients I M hflat
  let : Module.Projective R (AdicCompletion I M) :=
    AdicCompletion.moduleProjective_restrictScalars I M
  exact IsAdicComplete.moduleProjective_of_finite_of_projective_completion I M

/-- A finite flat module over an adically complete commutative ring is projective
if its first quotient is projective. No finite generation of the ideal is required. -/
theorem IsAdicComplete.moduleProjective_of_finite_of_flat_of_projective_quotient
    {R : Type uR} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Projective R M := by
  apply IsAdicComplete.moduleProjective_of_finite_of_flat_pow_quotients I M
  intro k _
  exact Module.Flat.of_linearEquiv
    ((TensorProduct.quotTensorEquivQuotSMul M (I ^ k)).extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective :
        Function.Surjective (algebraMap R (R ⧸ I ^ k)))).symm

/-- An ideal of an adically complete commutative ring is finitely generated exactly
when its canonical conormal module is finite over the residue ring. -/
theorem Ideal.fg_iff_finite_cotangent
    {R : Type uR} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    I.FG ↔ Module.Finite (R ⧸ I) I.Cotangent := by
  constructor
  · exact Ideal.finite_cotangent_of_fg I
  · intro hI
    -- Compare the conormal and first quotient through their canonical scalar towers.
    let e : I.Cotangent ≃ₗ[R] (I ⧸ (I • (⊤ : Submodule R I))) :=
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let : Module.Finite (R ⧸ I) (I ⧸ (I • (⊤ : Submodule R I))) :=
      (Module.Finite.equiv_iff (e.extendScalarsOfSurjective
        (Ideal.Quotient.mk_surjective :
          Function.Surjective (algebraMap R (R ⧸ I))))).mp hI
    let : IsHausdorff I I :=
      IsHausdorff.of_injective I I.subtype (Submodule.injective_subtype I)
    exact Module.Finite.iff_fg.mp
      (IsPrecomplete.moduleFinite_of_isHausdorff_of_finite_quotient I I)

/-- An adically complete commutative ring is Noetherian exactly when its residue ring
is Noetherian and its conormal module is finite over that residue ring. The reverse
implication uses the finitely generated ideal criterion of Fujiwara–Kato,
*Foundations of Rigid Geometry I*, after deriving finite generation from the conormal. -/
theorem IsAdicComplete.isNoetherianRing_iff_quotient_and_finite_cotangent
    {R : Type uR} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    IsNoetherianRing R ↔
      IsNoetherianRing (R ⧸ I) ∧ Module.Finite (R ⧸ I) I.Cotangent := by
  constructor
  · intro hR
    let : IsNoetherianRing R := hR
    exact ⟨inferInstance,
      (Ideal.fg_iff_finite_cotangent I).mp (Ideal.fg_of_isNoetherianRing I)⟩
  · rintro ⟨hquot, hcot⟩
    let : IsNoetherianRing (R ⧸ I) := hquot
    exact IsAdicComplete.isNoetherianRing_of_fg I
      ((Ideal.fg_iff_finite_cotangent I).mpr hcot)
