/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Completeness
public import AdicModules.AdicCompletion.Kernel

/-!
# Linear maps and adic completion

For any ideal `I` of a commutative ring `R` and additive commutative group
`R`-modules, completion distinguishes linear maps to an `I`-Hausdorff original
target and reflects injectivity from an `I`-Hausdorff original source. A completed
right-inverse identity for two given original maps implies their right-inverse
identity on an `I`-Hausdorff original target, with the same right inverse. The
opposite endpoint need not be Hausdorff, and no finite generation or completeness
is required. These laws use Mathlib's canonical completion, `of`, `map`, and the
Hausdorff injectivity criterion for `of`.

Independently of Hausdorffness, `map_injective_of_reduceModIdeal_injective`
deduces injectivity of the completed map from injectivity on every original
power quotient. It uses only coordinatewise extensionality.
`map_bijective_of_reduceModIdeal_bijective` combines this with Mathlib's
first-quotient surjectivity criterion: bijectivity at every positive original
power quotient implies bijectivity of the canonical completed map. Stage zero
is automatic, and no completeness or finite-generation hypothesis is needed.

`AdicCompletion.extend` sends an `R`-linear map to an adically complete module to its
canonical extension. It uses Mathlib's completed map, restricts its scalars from
`AdicCompletion I R` to `R`, and then applies the inverse of `ofLinearEquiv`.
In particular, the two scalar rings in this construction are not identified.

The characteristic laws describe restriction to the original module, reduction at
every quotient, and agreement with `IsAdicComplete.lift`. Extension is natural in
both modules and is `R`-linear in the map being extended. These laws require no
finite generation assumption on the ideal.

If every original-`R` ideal-power submodule of the source completion is the
corresponding evaluation kernel, `ext_of_ker_eval` gives uniqueness for a
Hausdorff target, without assuming target completeness. For a complete target,
`precompOfLinearEquivOfKernel` packages restriction along `of I M` and the existing
extension as an `R`-linear equivalence of Hom modules. The target needs no
completed-ring action. Finite generation of the image of `I M` in the original
quotient `M / I² M` supplies these source kernel identities and gives
`precompOfLinearEquivOfFGFirstLayer`, without finite generation of `I` or `M`.
A finitely generated positive ideal power also supplies the identities:
`ext_of_fg_pow`, `ext_of` and `precompOfLinearEquiv` retain the corresponding
finite-generation specializations.

For original modules with given compatible `R`- and `AdicCompletion I R`-actions,
`LinearMap.map_smul_adicCompletion_of_fg_pow` shows that an `R`-linear map
respects the completed-ring action when a given positive power `I ^ n` is
finitely generated and its target is `I`-Hausdorff. The source may be an additive
commutative monoid and need not be Hausdorff; neither module is required to be
complete, finite or projective. `restrictScalarsHomEquivOfFGPow` packages
restriction of scalars as an equivalence linear over the completed ring, with
the pointwise scalar action on the target. Its inverse preserves the original
function and additive map. `LinearMap.retraction_adicCompletion_of_fg_pow` uses
this equivalence to upgrade a specified retraction with Hausdorff target.
The corresponding finitely generated ideal APIs are the `n = 1` specializations.

The extension reuses Mathlib's `map` and `ofLinearEquiv`, and agrees with
`IsAdicComplete.lift`. Uniqueness approximates a completed source element by an
original representative at every precision, uses the source kernel identity to
control its difference, and applies Mathlib's `IsHausdorff.funext` to the target.
The first-layer and positive-power specializations reuse the public kernel
suppliers. Automatic scalar linearity applies `ext_of_fg_pow` to the scalar-orbit
maps out of the completed coefficient ring, built with Mathlib's
`LinearMap.toSpanSingleton` and scalar restriction; its hypotheses are unchanged.
All completions remain `I`-adic. There is no new inverse-limit construction,
topology, or scalar action. Finite generation of `I ^ 0` alone does not suffice
for uniform uniqueness.

## References

This file builds on the adic-completion formalizations of Kenny Lau, Judith Ludwig,
Christian Merten, Jiedong Jiang and Bingyu Xia, and on Mathlib's scalar-tower,
linear-map and span APIs.
-/

@[expose] public section

noncomputable section

universe u v w x y

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Injectivity on all original power quotients implies injectivity of completion. -/
theorem map_injective_of_reduceModIdeal_injective (f : M →ₗ[R] N)
    (hf : ∀ n : ℕ, Function.Injective (f.reduceModIdeal (I ^ n))) :
    Function.Injective (AdicCompletion.map I f) := by
  intro x y hxy
  apply AdicCompletion.ext
  intro n
  apply hf n
  simpa only [AdicCompletion.map_val_apply] using
    congrArg (fun z : AdicCompletion I N ↦ z.val n) hxy

/-- Bijectivity on every positive original power quotient implies bijectivity
of the canonical completed map. Stage zero is automatically a singleton quotient. -/
theorem map_bijective_of_reduceModIdeal_bijective (f : M →ₗ[R] N)
    (hf : ∀ n : ℕ, 0 < n → Function.Bijective (f.reduceModIdeal (I ^ n))) :
    Function.Bijective (AdicCompletion.map I f) := by
  constructor
  · apply map_injective_of_reduceModIdeal_injective I f
    intro n
    by_cases hn : n = 0
    · subst n
      let : Subsingleton (M ⧸ (I ^ 0 • (⊤ : Submodule R M))) :=
        Submodule.Quotient.subsingleton_iff.mpr (by simp)
      exact fun _ _ _ ↦ Subsingleton.elim _ _
    · exact (hf n (Nat.pos_of_ne_zero hn)).1
  · apply map_surjective_of_mkQ_comp_surjective
    intro y
    have hf1 : Function.Bijective (f.reduceModIdeal I) := by
      have h := hf 1 Nat.zero_lt_one
      rw [pow_one] at h
      exact h
    obtain ⟨x, hx⟩ := hf1.2 y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) x
    exact ⟨x, hx⟩

/-- Completion distinguishes original linear maps to an I-Hausdorff target. -/
theorem map_injective_of_isHausdorff [IsHausdorff I N] :
    Function.Injective
      (AdicCompletion.map (R := R) (I := I) (M := M) (N := N) :
        (M →ₗ[R] N) →
          (AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N)) := by
  intro f g hfg
  apply LinearMap.ext
  intro x
  apply AdicCompletion.of_injective (R := R) (I := I) (M := N)
  simpa only [AdicCompletion.map_of] using
    DFunLike.congr_fun hfg (AdicCompletion.of (R := R) (I := I) (M := M) x)

/-- An injective completed map has an injective original map when its source is I-Hausdorff. -/
theorem injective_of_map_injective [IsHausdorff I M] (f : M →ₗ[R] N)
    (hf : Function.Injective
      (AdicCompletion.map (R := R) (I := I) (M := M) (N := N) f)) :
    Function.Injective f := by
  intro x y hxy
  apply AdicCompletion.of_injective (R := R) (I := I) (M := M)
  apply hf
  simpa only [AdicCompletion.map_of] using
    congrArg (AdicCompletion.of (R := R) (I := I) (M := N)) hxy

/-- A completed right-inverse identity reflects the identity for the given original maps. -/
theorem comp_eq_id_of_map_comp_eq_id [IsHausdorff I N]
    (f : M →ₗ[R] N) (r : N →ₗ[R] M)
    (hfr :
      (AdicCompletion.map (R := R) (I := I) (M := M) (N := N) f).comp
        (AdicCompletion.map (R := R) (I := I) (M := N) (N := M) r) =
      LinearMap.id (R := AdicCompletion I R) (M := AdicCompletion I N)) :
    f.comp r = LinearMap.id (R := R) (M := N) := by
  apply AdicCompletion.map_injective_of_isHausdorff
    (R := R) (I := I) (M := N) (N := N)
  rw [← AdicCompletion.map_comp (R := R) (I := I)
      (M := N) (N := M) (P := N) (f := r) (g := f),
    AdicCompletion.map_id (R := R) (I := I) (M := N)]
  exact hfr

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

/-- Linear maps from the completion to a Hausdorff module agree on the whole
completion if they agree on the canonical image and every source ideal-power
submodule is an evaluation kernel. -/
theorem ext_of_ker_eval
    (hM : ∀ n : ℕ, I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker)
    [IsHausdorff I N] (F G : AdicCompletion I M →ₗ[R] N)
    (h : ∀ m : M, F (of I M m) = G (of I M m)) : F = G := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext I
  intro n z
  obtain ⟨m, hm⟩ :=
    Submodule.mkQ_surjective (I ^ n • ⊤ : Submodule R M) (eval I M n z)
  have hz : z - of I M m ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I M)) := by
    rw [hM n, LinearMap.mem_ker, (eval I M n).map_sub, eval_of, hm, sub_self]
  have hmap (L : AdicCompletion I M →ₗ[R] N) :
      L z ≡ L (of I M m) [SMOD (I ^ n • ⊤ : Submodule R N)] := by
    apply SModEq.sub_mem.mpr
    rw [← L.map_sub]
    exact Submodule.smul_top_le_comap_smul_top (I ^ n) L hz
  have hF := hmap F
  rw [h m] at hF
  exact hF.trans (hmap G).symm

/-- Linear maps from the completion to a Hausdorff module agree if they agree
on the canonical image, when a given positive power of the ideal is finitely generated. -/
theorem ext_of_fg_pow {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) [IsHausdorff I N]
    (F G : AdicCompletion I M →ₗ[R] N)
    (h : ∀ m : M, F (of I M m) = G (of I M m)) : F = G :=
  ext_of_ker_eval I (pow_smul_top_eq_ker_eval_of_fg_pos_pow (I := I) (M := M) hn hI)
    F G h

/-- Linear maps from the completion to a Hausdorff module agree if they agree
on the canonical image, when the ideal is finitely generated. -/
theorem ext_of (hI : I.FG) [IsHausdorff I N]
    (F G : AdicCompletion I M →ₗ[R] N)
    (h : ∀ m : M, F (of I M m) = G (of I M m)) : F = G := by
  exact ext_of_fg_pow I (n := 1) Nat.zero_lt_one (by simpa only [pow_one] using hI) F G h

/-- A map to a complete target is recovered by extending its restriction when
all source ideal-power submodules are evaluation kernels. -/
theorem extend_precomp_of_ker_eval [IsAdicComplete I N]
    (hM : ∀ n : ℕ, I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker)
    (F : AdicCompletion I M →ₗ[R] N) :
    extend I (F.comp (of I M)) = F := by
  apply ext_of_ker_eval I hM
  intro m
  exact extend_of I (F.comp (of I M)) m

/-- Restriction along the canonical map is an `R`-linear equivalence of Hom modules
when every source ideal-power submodule is an evaluation kernel and the target is
adically complete. Its inverse is the canonical extension `extend`. -/
noncomputable def precompOfLinearEquivOfKernel [IsAdicComplete I N]
    (hM : ∀ n : ℕ, I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker) :
    (AdicCompletion I M →ₗ[R] N) ≃ₗ[R] (M →ₗ[R] N) where
  toLinearMap := LinearMap.lcomp R N (of I M)
  invFun := extend I
  left_inv F := extend_precomp_of_ker_eval I hM F
  right_inv f := extend_comp_of I f

/-- The linear map underlying the source-kernel Hom equivalence is precomposition
with the canonical map. -/
@[simp]
theorem precompOfLinearEquivOfKernel_toLinearMap [IsAdicComplete I N]
    (hM : ∀ n : ℕ, I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker) :
    (precompOfLinearEquivOfKernel I (N := N) hM).toLinearMap =
      LinearMap.lcomp R N (of I M) :=
  rfl

/-- The source-kernel Hom equivalence restricts a map to the original module. -/
@[simp]
theorem precompOfLinearEquivOfKernel_apply [IsAdicComplete I N]
    (hM : ∀ n : ℕ, I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker)
    (F : AdicCompletion I M →ₗ[R] N) :
    precompOfLinearEquivOfKernel I hM F = F.comp (of I M) :=
  rfl

/-- The inverse source-kernel Hom equivalence is canonical extension. -/
@[simp]
theorem precompOfLinearEquivOfKernel_symm_apply [IsAdicComplete I N]
    (hM : ∀ n : ℕ, I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker)
    (f : M →ₗ[R] N) :
    (precompOfLinearEquivOfKernel I hM).symm f = extend I f :=
  rfl

/-- On the canonical image, the inverse source-kernel Hom equivalence evaluates
the original map. -/
theorem precompOfLinearEquivOfKernel_symm_apply_of [IsAdicComplete I N]
    (hM : ∀ n : ℕ, I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker)
    (f : M →ₗ[R] N) (m : M) :
    (precompOfLinearEquivOfKernel I hM).symm f (of I M m) = f m := by
  rw [precompOfLinearEquivOfKernel_symm_apply, extend_of]

/-- Restriction and canonical extension give a Hom equivalence for a complete target
if the image of `I M` in the original quotient `M / I² M` is finitely generated.
No finite generation of the ideal or of the original module is required. -/
noncomputable def precompOfLinearEquivOfFGFirstLayer [IsAdicComplete I N]
    (h : ((I • (⊤ : Submodule R M)).map (I ^ 2 • (⊤ : Submodule R M)).mkQ).FG) :
    (AdicCompletion I M →ₗ[R] N) ≃ₗ[R] (M →ₗ[R] N) :=
  precompOfLinearEquivOfKernel I (pow_smul_top_eq_ker_eval_of_fg_first_layer I M h)

/-- The linear map underlying the first-layer Hom equivalence is precomposition
with the canonical map. -/
@[simp]
theorem precompOfLinearEquivOfFGFirstLayer_toLinearMap [IsAdicComplete I N]
    (h : ((I • (⊤ : Submodule R M)).map (I ^ 2 • (⊤ : Submodule R M)).mkQ).FG) :
    (precompOfLinearEquivOfFGFirstLayer I (N := N) h).toLinearMap =
      LinearMap.lcomp R N (of I M) :=
  rfl

/-- The first-layer Hom equivalence restricts a map to the original module. -/
@[simp]
theorem precompOfLinearEquivOfFGFirstLayer_apply [IsAdicComplete I N]
    (h : ((I • (⊤ : Submodule R M)).map (I ^ 2 • (⊤ : Submodule R M)).mkQ).FG)
    (F : AdicCompletion I M →ₗ[R] N) :
    precompOfLinearEquivOfFGFirstLayer I h F = F.comp (of I M) :=
  rfl

/-- The inverse first-layer Hom equivalence is canonical extension. -/
@[simp]
theorem precompOfLinearEquivOfFGFirstLayer_symm_apply [IsAdicComplete I N]
    (h : ((I • (⊤ : Submodule R M)).map (I ^ 2 • (⊤ : Submodule R M)).mkQ).FG)
    (f : M →ₗ[R] N) :
    (precompOfLinearEquivOfFGFirstLayer I h).symm f = extend I f :=
  rfl

/-- On the canonical image, the inverse first-layer Hom equivalence evaluates
the original map. -/
theorem precompOfLinearEquivOfFGFirstLayer_symm_apply_of [IsAdicComplete I N]
    (h : ((I • (⊤ : Submodule R M)).map (I ^ 2 • (⊤ : Submodule R M)).mkQ).FG)
    (f : M →ₗ[R] N) (m : M) :
    (precompOfLinearEquivOfFGFirstLayer I h).symm f (of I M m) = f m := by
  rw [precompOfLinearEquivOfFGFirstLayer_symm_apply, extend_of]

/-- A map to a complete target is recovered by extending its restriction to the
original module, when the ideal is finitely generated. -/
@[simp]
theorem extend_precomp_of [IsAdicComplete I N] (hI : I.FG)
    (F : AdicCompletion I M →ₗ[R] N) :
    extend I (F.comp (of I M)) = F :=
  extend_precomp_of_ker_eval I
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow (I := I) (M := M) (n := 1) Nat.zero_lt_one
      (by simpa only [pow_one] using hI)) F

/-- Restriction along the canonical map is an `R`-linear equivalence of Hom
modules for a finitely generated ideal and a complete target. Its inverse is
canonical extension. -/
noncomputable def precompOfLinearEquiv [IsAdicComplete I N] (hI : I.FG) :
    (AdicCompletion I M →ₗ[R] N) ≃ₗ[R] (M →ₗ[R] N) :=
  precompOfLinearEquivOfKernel I
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow (I := I) (M := M) (n := 1) Nat.zero_lt_one
      (by simpa only [pow_one] using hI))

/-- The finitely generated ideal Hom equivalence agrees with the source-kernel
Hom equivalence for any proof of the source kernel identities. -/
theorem precompOfLinearEquiv_eq_precompOfLinearEquivOfKernel [IsAdicComplete I N]
    (hI : I.FG)
    (hM : ∀ n : ℕ, I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker) :
    precompOfLinearEquiv I (N := N) hI = precompOfLinearEquivOfKernel I hM :=
  rfl

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

section CompletedScalars

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {P : Type v} [AddCommMonoid P]
  [Module R P] [Module (AdicCompletion I R) P] [IsScalarTower R (AdicCompletion I R) P]
variable {T : Type w} [AddCommGroup T]
  [Module R T] [Module (AdicCompletion I R) T] [IsScalarTower R (AdicCompletion I R) T]
  [IsHausdorff I T]

namespace LinearMap

/-- An `R`-linear map between modules with given compatible completed-ring actions
respects those actions if a positive ideal power is finitely generated and the target
is Hausdorff. -/
theorem map_smul_adicCompletion_of_fg_pow {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    (F : P →ₗ[R] T) (a : AdicCompletion I R) (p : P) : F (a • p) = a • F p := by
  have h :
      F.comp ((toSpanSingleton (AdicCompletion I R) P p).restrictScalars R) =
        (toSpanSingleton (AdicCompletion I R) T (F p)).restrictScalars R := by
    apply AdicCompletion.ext_of_fg_pow I (M := R) (N := T) hn hI
    intro r
    change F (AdicCompletion.of I R r • p) = AdicCompletion.of I R r • F p
    have hof : AdicCompletion.of I R r = algebraMap R (AdicCompletion I R) r := by
      simp only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    simp only [hof, algebraMap_smul, F.map_smul]
  exact LinearMap.congr_fun h a

/-- An `R`-linear map between modules with given compatible completed-ring actions
respects those actions if the ideal is finitely generated and the target is Hausdorff. -/
theorem map_smul_adicCompletion (hI : I.FG) (F : P →ₗ[R] T)
    (a : AdicCompletion I R) (p : P) : F (a • p) = a • F p := by
  exact map_smul_adicCompletion_of_fg_pow I (n := 1) Nat.zero_lt_one
    (by simpa only [pow_one] using hI) F a p

end LinearMap

namespace AdicCompletion

/-- Restriction of scalars is an equivalence linear over the completed ring for
modules with given compatible actions, a finitely generated positive ideal
power, and a Hausdorff target. Both Hom modules have the pointwise completed-ring
action on the target; the inverse keeps the original function and additive map. -/
def restrictScalarsHomEquivOfFGPow {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) :
    (P →ₗ[AdicCompletion I R] T) ≃ₗ[AdicCompletion I R] (P →ₗ[R] T) where
  toLinearMap :=
    LinearMap.restrictScalarsₗ (R := R) (S := AdicCompletion I R) (M := P) (N := T)
      (R₁ := AdicCompletion I R)
  invFun F :=
    { F.toAddHom with
      map_smul' := LinearMap.map_smul_adicCompletion_of_fg_pow I hn hI F }
  left_inv G := by
    apply LinearMap.ext
    intro p
    rfl
  right_inv F := by
    apply LinearMap.ext
    intro p
    rfl

/-- The forward linear map is Mathlib's restriction-of-scalars map. -/
theorem restrictScalarsHomEquivOfFGPow_toLinearMap {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) :
    (restrictScalarsHomEquivOfFGPow I (P := P) (T := T) hn hI).toLinearMap =
      LinearMap.restrictScalarsₗ (R := R) (S := AdicCompletion I R) (M := P) (N := T)
        (R₁ := AdicCompletion I R) :=
  rfl

/-- The forward equivalence restricts scalars to the original ring. -/
@[simp]
theorem restrictScalarsHomEquivOfFGPow_apply {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    (G : P →ₗ[AdicCompletion I R] T) :
    restrictScalarsHomEquivOfFGPow I hn hI G = G.restrictScalars R :=
  rfl

/-- The inverse equivalence evaluates as the original map. -/
@[simp]
theorem restrictScalarsHomEquivOfFGPow_symm_apply {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    (F : P →ₗ[R] T) (p : P) :
    (restrictScalarsHomEquivOfFGPow I hn hI).symm F p = F p :=
  rfl

/-- Restricting the inverse equivalence recovers the original linear map. -/
@[simp]
theorem restrictScalarsHomEquivOfFGPow_symm_apply_restrictScalars
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (F : P →ₗ[R] T) :
    ((restrictScalarsHomEquivOfFGPow I hn hI).symm F).restrictScalars R = F := by
  apply LinearMap.ext
  intro p
  rfl

/-- The inverse equivalence recovers a completed-ring-linear map from its restriction. -/
@[simp]
theorem restrictScalarsHomEquivOfFGPow_symm_restrictScalars {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    (G : P →ₗ[AdicCompletion I R] T) :
    (restrictScalarsHomEquivOfFGPow I hn hI).symm (G.restrictScalars R) = G := by
  apply LinearMap.ext
  intro p
  rfl

/-- Restriction of scalars is an equivalence linear over the completed ring for
modules with given compatible actions, a finitely generated ideal, and a Hausdorff
target. Both Hom modules have the pointwise completed-ring action on the target;
the inverse keeps the original function and additive map. -/
def restrictScalarsHomEquiv (hI : I.FG) :
    (P →ₗ[AdicCompletion I R] T) ≃ₗ[AdicCompletion I R] (P →ₗ[R] T) :=
  restrictScalarsHomEquivOfFGPow I (n := 1) Nat.zero_lt_one (by simpa only [pow_one] using hI)

/-- The forward linear map is Mathlib's restriction-of-scalars map. -/
theorem restrictScalarsHomEquiv_toLinearMap (hI : I.FG) :
    (restrictScalarsHomEquiv I (P := P) (T := T) hI).toLinearMap =
      LinearMap.restrictScalarsₗ (R := R) (S := AdicCompletion I R) (M := P) (N := T)
        (R₁ := AdicCompletion I R) := by
  exact restrictScalarsHomEquivOfFGPow_toLinearMap I (n := 1)
    Nat.zero_lt_one (by simpa only [pow_one] using hI)

/-- The forward equivalence restricts scalars to the original ring. -/
@[simp]
theorem restrictScalarsHomEquiv_apply (hI : I.FG)
    (G : P →ₗ[AdicCompletion I R] T) :
    restrictScalarsHomEquiv I hI G = G.restrictScalars R := by
  exact restrictScalarsHomEquivOfFGPow_apply I (n := 1)
    Nat.zero_lt_one (by simpa only [pow_one] using hI) G

/-- The inverse equivalence evaluates as the original map. -/
@[simp]
theorem restrictScalarsHomEquiv_symm_apply (hI : I.FG) (F : P →ₗ[R] T) (p : P) :
    (restrictScalarsHomEquiv I hI).symm F p = F p := by
  exact restrictScalarsHomEquivOfFGPow_symm_apply I (n := 1)
    Nat.zero_lt_one (by simpa only [pow_one] using hI) F p

/-- Restricting the inverse equivalence recovers the original linear map. -/
@[simp]
theorem restrictScalarsHomEquiv_symm_apply_restrictScalars (hI : I.FG) (F : P →ₗ[R] T) :
    ((restrictScalarsHomEquiv I hI).symm F).restrictScalars R = F := by
  exact restrictScalarsHomEquivOfFGPow_symm_apply_restrictScalars I (n := 1)
    Nat.zero_lt_one (by simpa only [pow_one] using hI) F

/-- The inverse equivalence recovers a completed-ring-linear map from its restriction. -/
@[simp]
theorem restrictScalarsHomEquiv_symm_restrictScalars (hI : I.FG)
    (G : P →ₗ[AdicCompletion I R] T) :
    (restrictScalarsHomEquiv I hI).symm (G.restrictScalars R) = G := by
  exact restrictScalarsHomEquivOfFGPow_symm_restrictScalars I (n := 1)
    Nat.zero_lt_one (by simpa only [pow_one] using hI) G

end AdicCompletion

end CompletedScalars

section Retraction

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {P : Type v} [AddCommGroup P]
  [Module R P] [Module (AdicCompletion I R) P] [IsScalarTower R (AdicCompletion I R) P]
  [IsHausdorff I P]
variable {Q : Type w} [AddCommMonoid Q]
  [Module R Q] [Module (AdicCompletion I R) Q] [IsScalarTower R (AdicCompletion I R) Q]

namespace LinearMap

/-- A specified `R`-linear retraction of a completed-ring-linear map remains a
retraction after upgrading the same function to completed-ring linearity, for a
finitely generated positive ideal power and a Hausdorff target of the retraction. -/
theorem retraction_adicCompletion_of_fg_pow {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    (f : P →ₗ[AdicCompletion I R] Q) (r : Q →ₗ[R] P)
    (hr : r.comp (f.restrictScalars R) = LinearMap.id) :
    ((AdicCompletion.restrictScalarsHomEquivOfFGPow I (P := Q) (T := P) hn hI).symm r).comp f =
      LinearMap.id := by
  apply LinearMap.restrictScalars_injective R
  rw [LinearMap.restrictScalars_comp,
    AdicCompletion.restrictScalarsHomEquivOfFGPow_symm_apply_restrictScalars,
    LinearMap.restrictScalars_id]
  exact hr

/-- A specified `R`-linear retraction of a completed-ring-linear map remains a
retraction after upgrading the same function to completed-ring linearity, for a
finitely generated ideal and a Hausdorff target of the retraction. -/
theorem retraction_adicCompletion (hI : I.FG)
    (f : P →ₗ[AdicCompletion I R] Q) (r : Q →ₗ[R] P)
    (hr : r.comp (f.restrictScalars R) = LinearMap.id) :
    ((AdicCompletion.restrictScalarsHomEquiv I (P := Q) (T := P) hI).symm r).comp f =
      LinearMap.id := by
  exact retraction_adicCompletion_of_fg_pow I (n := 1) Nat.zero_lt_one
    (by simpa only [pow_one] using hI) f r hr

end LinearMap

end Retraction
