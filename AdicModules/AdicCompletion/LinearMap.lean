/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Linear maps from an adic completion

`AdicCompletion.extend` sends an `R`-linear map to an adically complete module to its
canonical extension. It uses Mathlib's completed map, restricts its scalars from
`AdicCompletion I R` to `R`, and then applies the inverse of `ofLinearEquiv`.
In particular, the two scalar rings in this construction are not identified.

The characteristic laws describe restriction to the original module, reduction at
every quotient, and agreement with `IsAdicComplete.lift`. Extension is natural in
both modules and is `R`-linear in the map being extended. These laws require no
finite generation assumption on the ideal.

For a finitely generated ideal, `ext_of` gives uniqueness for a Hausdorff target,
without assuming target completeness. For a complete target,
`precompOfLinearEquiv` packages restriction along `of I M` and extension as an
`R`-linear equivalence of Hom modules. Finite generation is a sufficient
hypothesis for uniqueness; no necessity assertion is made.

The extension reuses Mathlib's `map` and `ofLinearEquiv`, and agrees with
`IsAdicComplete.lift`. Uniqueness uses Mathlib's description of the kernels of
evaluation for a finitely generated ideal. There is no new inverse-limit
construction, topology, or scalar action.
-/

@[expose] public section

noncomputable section

universe u v w x y

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Extend a linear map to an adically complete target using the completed map.
The completed-ring-linear inner map is explicitly restricted to `R`-scalars. -/
noncomputable def extend [IsAdicComplete I N] (f : M →ₗ[R] N) :
    AdicCompletion I M →ₗ[R] N :=
  (ofLinearEquiv I N).symm.toLinearMap.comp ((map I f).restrictScalars R)

/-- The value of the canonical extension, expressed using Mathlib's completion maps. -/
theorem extend_apply [IsAdicComplete I N] (f : M →ₗ[R] N) (z : AdicCompletion I M) :
    extend I f z = (ofLinearEquiv I N).symm (map I f z) :=
  rfl

/-- The extension agrees with the original map on the canonical image. -/
@[simp]
theorem extend_of [IsAdicComplete I N] (f : M →ₗ[R] N) (m : M) :
    extend I f (of I M m) = f m := by
  rw [extend_apply, map_of, ofLinearEquiv_symm_of]

/-- Precomposing the extension with the canonical map recovers the original map. -/
@[simp]
theorem extend_comp_of [IsAdicComplete I N] (f : M →ₗ[R] N) :
    (extend I f).comp (of I M) = f := by
  apply LinearMap.ext
  intro m
  exact extend_of I f m

/-- Applying the canonical map to an extension recovers the completed map. -/
@[simp]
theorem of_extend [IsAdicComplete I N] (f : M →ₗ[R] N) (z : AdicCompletion I M) :
    of I N (extend I f z) = map I f z := by
  rw [extend_apply, of_ofLinearEquiv_symm]

/-- Reduction of the extension at any level is induced by the original map. -/
theorem mkQ_comp_extend [IsAdicComplete I N] (f : M →ₗ[R] N) (n : ℕ) :
    (Submodule.mkQ (I ^ n • ⊤ : Submodule R N)).comp (extend I f) =
      ((f.reduceModIdeal (I ^ n)).restrictScalars R).comp (eval I M n) := by
  apply LinearMap.ext
  intro z
  change eval I N n (of I N (extend I f z)) =
    f.reduceModIdeal (I ^ n) (eval I M n z)
  rw [of_extend]
  rfl

/-- Extension commutes with precomposition, using the induced map on completions. -/
theorem extend_comp [IsAdicComplete I N]
    {L : Type x} [AddCommGroup L] [Module R L]
    (g : L →ₗ[R] M) (f : M →ₗ[R] N) :
    extend I (f.comp g) = (extend I f).comp ((map I g).restrictScalars R) := by
  apply LinearMap.ext
  intro z
  exact congrArg (ofLinearEquiv I N).symm (map_comp_apply I g f z).symm

/-- Extension commutes with postcomposition between adically complete targets. -/
theorem comp_extend [IsAdicComplete I N]
    {P : Type y} [AddCommGroup P] [Module R P] [IsAdicComplete I P]
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    g.comp (extend I f) = extend I (g.comp f) := by
  apply LinearMap.ext
  intro z
  apply (ofLinearEquiv I P).injective
  change of I P (g (extend I f z)) = of I P (extend I (g.comp f) z)
  rw [of_extend, ← map_of, of_extend, map_comp_apply]

/-- The extension of the zero map is zero. -/
@[simp]
theorem extend_zero [IsAdicComplete I N] : extend I (0 : M →ₗ[R] N) = 0 := by
  apply LinearMap.ext
  intro z
  simp [extend_apply]

/-- Extension preserves addition of linear maps. -/
@[simp]
theorem extend_add [IsAdicComplete I N] (f g : M →ₗ[R] N) :
    extend I (f + g) = extend I f + extend I g := by
  apply LinearMap.ext
  intro z
  simp [extend_apply]

/-- Extension preserves scalar multiplication of linear maps. -/
@[simp]
theorem extend_smul [IsAdicComplete I N] (r : R) (f : M →ₗ[R] N) :
    extend I (r • f) = r • extend I f := by
  apply LinearMap.ext
  intro z
  simp [extend_apply]

private theorem eval_map_compatible (f : M →ₗ[R] N) {m n : ℕ} (hmn : m ≤ n) :
    (transitionMap I N hmn).comp ((eval I N n).comp ((map I f).restrictScalars R)) =
      (eval I N m).comp ((map I f).restrictScalars R) := by
  rw [← LinearMap.comp_assoc, transitionMap_comp_eval]

/-- The extension agrees with the lift of its compatible quotient maps. -/
theorem extend_eq_lift [IsAdicComplete I N] (f : M →ₗ[R] N) :
    extend I f = IsAdicComplete.lift I
      (fun n ↦ (eval I N n).comp ((map I f).restrictScalars R))
      (fun hmn ↦ by rw [← LinearMap.comp_assoc, transitionMap_comp_eval]) := by
  apply IsAdicComplete.eq_lift I (fun hmn ↦ eval_map_compatible I f hmn)
  intro n
  apply LinearMap.ext
  intro z
  change eval I N n (of I N (extend I f z)) = eval I N n (map I f z)
  rw [of_extend]

/-- Linear maps from the completion to a Hausdorff module agree if they agree
on the canonical image, when the ideal is finitely generated. -/
theorem ext_of (hI : I.FG) [IsHausdorff I N]
    (F G : AdicCompletion I M →ₗ[R] N)
    (h : ∀ m : M, F (of I M m) = G (of I M m)) : F = G := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext I
  intro n z
  obtain ⟨m, hm⟩ :=
    Submodule.mkQ_surjective (I ^ n • ⊤ : Submodule R M) (eval I M n z)
  have hz : z - of I M m ∈
      (I ^ n • ⊤ : Submodule R (AdicCompletion I M)) := by
    rw [pow_smul_top_eq_ker_eval (I := I) (M := M) (n := n) hI,
      LinearMap.mem_ker, (eval I M n).map_sub, eval_of, hm, sub_self]
  have hmap (L : AdicCompletion I M →ₗ[R] N) :
      L z ≡ L (of I M m) [SMOD (I ^ n • ⊤ : Submodule R N)] := by
    apply SModEq.sub_mem.mpr
    rw [← L.map_sub]
    exact Submodule.smul_top_le_comap_smul_top (I ^ n) L hz
  have hF := hmap F
  rw [h m] at hF
  exact hF.trans (hmap G).symm

/-- A map to a complete target is recovered by extending its restriction to the
original module, when the ideal is finitely generated. -/
@[simp]
theorem extend_precomp_of [IsAdicComplete I N] (hI : I.FG)
    (F : AdicCompletion I M →ₗ[R] N) :
    extend I (F.comp (of I M)) = F := by
  apply ext_of I hI
  intro m
  exact extend_of I (F.comp (of I M)) m

/-- Restriction along the canonical map is an `R`-linear equivalence of Hom
modules for a finitely generated ideal and a complete target. Its inverse is
canonical extension. -/
noncomputable def precompOfLinearEquiv [IsAdicComplete I N] (hI : I.FG) :
    (AdicCompletion I M →ₗ[R] N) ≃ₗ[R] (M →ₗ[R] N) where
  toLinearMap := LinearMap.lcomp R N (of I M)
  invFun := extend I
  left_inv F := extend_precomp_of I hI F
  right_inv f := extend_comp_of I f

/-- The linear map underlying the Hom equivalence is precomposition with `of`. -/
@[simp]
theorem precompOfLinearEquiv_toLinearMap [IsAdicComplete I N] (hI : I.FG) :
    (precompOfLinearEquiv I (M := M) (N := N) hI).toLinearMap =
      LinearMap.lcomp R N (of I M) :=
  rfl

/-- The forward Hom equivalence restricts a map to the original module. -/
@[simp]
theorem precompOfLinearEquiv_apply [IsAdicComplete I N] (hI : I.FG)
    (F : AdicCompletion I M →ₗ[R] N) :
    precompOfLinearEquiv I hI F = F.comp (of I M) :=
  rfl

/-- The inverse Hom equivalence is canonical extension. -/
@[simp]
theorem precompOfLinearEquiv_symm_apply [IsAdicComplete I N] (hI : I.FG)
    (f : M →ₗ[R] N) :
    (precompOfLinearEquiv I hI).symm f = extend I f :=
  rfl

/-- On the canonical image, the inverse Hom equivalence evaluates the original map. -/
theorem precompOfLinearEquiv_symm_apply_of [IsAdicComplete I N] (hI : I.FG)
    (f : M →ₗ[R] N) (m : M) :
    (precompOfLinearEquiv I hI).symm f (of I M m) = f m := by
  rw [precompOfLinearEquiv_symm_apply, extend_of]

end AdicCompletion
