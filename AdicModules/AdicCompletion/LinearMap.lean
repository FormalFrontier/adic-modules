/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Exactness
public import AdicModules.AdicCompletion.Kernel

/-!
# Linear maps and adic completion

For every ideal and original linear map `f`, `range_map_range_subtype` identifies
the range of the completed original range inclusion with the range of `map I f`,
as submodules over `AdicCompletion I R`. This uses only the original range
factorization and Mathlib's preservation of surjectivity, with no Noetherian,
finiteness, injectivity, separation or completeness hypothesis.

`map_subtype_injective_of_cofinal` proves injectivity of the completed submodule
inclusion when the induced ideal-power filtration is pointwise cofinal with the
intrinsic one. There is no finiteness or Noetherian hypothesis on the ring, ideal,
submodule or ambient module. `rangeEquivOfRangeCofinal` then identifies completion
of the original range with the range of the completed map over `AdicCompletion I R`.
Its forward map is the completed original range inclusion with its codomain
restricted to that range. The whole forward and inverse maps, their uniqueness,
and the completed range-factorization square characterize the comparison.
`rangeEquivOfRangeCofinal_existsUnique` gives its mapping-in universal property
for any module over the completed ring.

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

For canonical raw completions, `LinearMap.map_smul_adicCompletion_of_ker_eval`
requires only the source kernel identities to upgrade every original-ring-linear map
to completed-ring linearity. The original target is arbitrary: no intrinsic completeness,
target or coefficient kernel equality, or finite-generation hypothesis is needed.
`restrictScalarsHomEquivOfKernel` packages restriction as a completed-ring-linear Hom
equivalence with a same-function inverse, and agrees with the positive-power equivalence
on canonical raw modules whenever a positive ideal power is finitely generated.

The extension reuses Mathlib's `map` and `ofLinearEquiv`, and agrees with
`IsAdicComplete.lift`. Uniqueness approximates a completed source element by an
original representative at every precision, uses the source kernel identity to
control its difference, and applies Mathlib's `IsHausdorff.funext` to the target.
The first-layer and positive-power specializations reuse the public kernel
suppliers. Automatic scalar linearity applies `ext_of_fg_pow` to the scalar-orbit
maps out of the completed coefficient ring, built with Mathlib's
`LinearMap.toSpanSingleton` and scalar restriction; its hypotheses are unchanged.
The canonical raw-target theorem first compares coordinates on original source elements
using coefficient representatives and unconditional target power-to-kernel containment,
then applies `ext_of_ker_eval` to the fixed-scalar orbit maps out of the source completion.
All completions remain `I`-adic. There is no new inverse-limit construction,
topology, or scalar action. Finite generation of `I ^ 0` alone does not suffice
for uniform uniqueness.

## References

This file builds on the adic-completion formalizations of Kenny Lau, Judith Ludwig,
Christian Merten, Jiedong Jiang and Bingyu Xia, and on Mathlib's scalar-tower,
linear-map and span APIs. The pointwise-cofinal criterion uses Mathlib's quotient
coordinates, transition maps and ideal-smul/submodule interfaces. The range comparison
uses Ludwig and Merten's all-ideal `AdicCompletion.map_surjective` in
`Mathlib.RingTheory.AdicCompletion.Exactness` and Mathlib's generic range-factorization API.
-/

@[expose] public section

noncomputable section

universe u v w x y
universe uR uM uN uP uX

namespace AdicCompletion

/-- The completed inclusion of the original range and the completed original map
have the same range, over the completed coefficient ring, for every ideal. -/
theorem range_map_range_subtype
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    LinearMap.range (AdicCompletion.map I f.range.subtype) =
      LinearMap.range (AdicCompletion.map I f) := by
  have hq : LinearMap.range (AdicCompletion.map I f.rangeRestrict) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (AdicCompletion.map_surjective I f.surjective_rangeRestrict)
  simpa only [AdicCompletion.map_comp, LinearMap.subtype_comp_rangeRestrict] using
    (LinearMap.range_comp_of_range_eq_top
      (AdicCompletion.map I f.range.subtype) hq).symm

/-- Pointwise cofinality of the induced and intrinsic ideal-power filtrations
makes completion of the submodule inclusion injective. -/
theorem map_subtype_injective_of_cofinal
    {R : Type uR} [CommRing R] (I : Ideal R)
    {P : Type uP} [AddCommGroup P] [Module R P]
    (K : Submodule R P)
    (hcofinal : ∀ n : ℕ, ∃ m : ℕ,
      K ⊓ (I ^ m • (⊤ : Submodule R P)) ≤ I ^ n • K) :
    Function.Injective (AdicCompletion.map I K.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  apply AdicCompletion.ext
  intro n
  change z.val n = 0
  obtain ⟨m, hm⟩ := hcofinal n
  -- A representative at a common deeper stage controls intrinsic precision `n`.
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective
    (I ^ (max n m) • (⊤ : Submodule R K)) (z.val (max n m))
  have haP : (a : P) ∈ I ^ (max n m) • (⊤ : Submodule R P) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have hz' := congrArg (fun w : AdicCompletion I P ↦ w.val (max n m)) hz
    rw [map_val_apply, ← ha] at hz'
    exact hz'
  have han : a ∈ I ^ n • (⊤ : Submodule R K) := by
    apply (Submodule.mem_smul_top_iff (I := I ^ n) K a).mpr
    exact hm ⟨a.property,
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_max_right n m)) haP⟩
  calc
    z.val n = transitionMap I K (Nat.le_max_left n m) (z.val (max n m)) :=
      (transitionMap_comp_eval_apply I K (Nat.le_max_left n m) z).symm
    _ = (I ^ n • (⊤ : Submodule R K)).mkQ a :=
      (congrArg (transitionMap I K (Nat.le_max_left n m)) ha).symm.trans
        (Submodule.factor_mk _ a)
    _ = 0 := (Submodule.Quotient.mk_eq_zero _).mpr han

/-- Completion of the original range is the range of the completed map when
its induced ideal-power filtration is pointwise cofinal with its intrinsic one.
The forward map is completion of the original range inclusion. -/
noncomputable def rangeEquivOfRangeCofinal
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {P : Type uP} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] P)
    (hcofinal : ∀ n : ℕ, ∃ m : ℕ,
      f.range ⊓ (I ^ m • (⊤ : Submodule R P)) ≤ I ^ n • f.range) :
    AdicCompletion I (LinearMap.range f) ≃ₗ[AdicCompletion I R]
      LinearMap.range (AdicCompletion.map I f) :=
  LinearEquiv.ofBijective
    ((AdicCompletion.map I f.range.subtype).codRestrict
      (LinearMap.range (AdicCompletion.map I f))
      (fun z ↦ (AdicCompletion.range_map_range_subtype I f).le
        (LinearMap.mem_range_self _ z)))
    (by
      constructor
      · intro x y hxy
        apply map_subtype_injective_of_cofinal I f.range hcofinal
        exact congrArg Subtype.val hxy
      · intro y
        have hy : (y : AdicCompletion I P) ∈
            LinearMap.range (AdicCompletion.map I f.range.subtype) :=
          (AdicCompletion.range_map_range_subtype I f).ge y.property
        obtain ⟨x, hx⟩ := hy
        exact ⟨x, Subtype.ext hx⟩)

section RangeCofinal

variable {R : Type uR} [CommRing R] (I : Ideal R)
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {P : Type uP} [AddCommGroup P] [Module R P]
variable (f : M →ₗ[R] P)
variable (hcofinal : ∀ n : ℕ, ∃ m : ℕ,
  f.range ⊓ (I ^ m • (⊤ : Submodule R P)) ≤ I ^ n • f.range)

/-- The whole ambient forward map is the completed original range inclusion. -/
theorem subtype_comp_rangeEquivOfRangeCofinal :
    (LinearMap.range (map I f)).subtype.comp
      (rangeEquivOfRangeCofinal I f hcofinal).toLinearMap =
      map I f.range.subtype :=
  rfl

/-- The forward linear map is the canonical codomain restriction, independently
of the proof of range membership. -/
theorem rangeEquivOfRangeCofinal_toLinearMap_eq_codRestrict
    (hmem : ∀ z : AdicCompletion I (LinearMap.range f),
      map I f.range.subtype z ∈ LinearMap.range (map I f)) :
    (rangeEquivOfRangeCofinal I f hcofinal).toLinearMap =
      (map I f.range.subtype).codRestrict (LinearMap.range (map I f)) hmem := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun (subtype_comp_rangeEquivOfRangeCofinal I f hcofinal) z

/-- Coercing the image comparison to the ambient completion gives the
completed original range inclusion. -/
@[simp]
theorem coe_rangeEquivOfRangeCofinal_apply
    (z : AdicCompletion I (LinearMap.range f)) :
    (rangeEquivOfRangeCofinal I f hcofinal z : AdicCompletion I P) =
      map I f.range.subtype z :=
  LinearMap.congr_fun (subtype_comp_rangeEquivOfRangeCofinal I f hcofinal) z

/-- An original range element maps to its canonical image in the ambient completion. -/
theorem coe_rangeEquivOfRangeCofinal_apply_of (y : LinearMap.range f) :
    (rangeEquivOfRangeCofinal I f hcofinal
      (of I (LinearMap.range f) y) : AdicCompletion I P) =
      of I P (y : P) := by
  rw [coe_rangeEquivOfRangeCofinal_apply, map_of]
  rfl

/-- The comparison identifies the two completed range factorizations. -/
@[simp]
theorem rangeEquivOfRangeCofinal_map_rangeRestrict (x : AdicCompletion I M) :
    rangeEquivOfRangeCofinal I f hcofinal (map I f.rangeRestrict x) =
      (map I f).rangeRestrict x := by
  apply Subtype.ext
  rw [coe_rangeEquivOfRangeCofinal_apply, map_comp_apply,
    LinearMap.subtype_comp_rangeRestrict]
  rfl

/-- The inverse comparison recovers the completed original range preimage. -/
@[simp]
theorem map_range_subtype_rangeEquivOfRangeCofinal_symm_apply
    (y : LinearMap.range (map I f)) :
    map I f.range.subtype ((rangeEquivOfRangeCofinal I f hcofinal).symm y) =
      (y : AdicCompletion I P) := by
  rw [← coe_rangeEquivOfRangeCofinal_apply I f hcofinal, LinearEquiv.apply_symm_apply]

/-- The whole inverse is a right inverse to the completed range inclusion
on the range of the completed map. -/
theorem map_range_subtype_comp_rangeEquivOfRangeCofinal_symm :
    (map I f.range.subtype).comp
      (rangeEquivOfRangeCofinal I f hcofinal).symm.toLinearMap =
      (LinearMap.range (map I f)).subtype := by
  apply LinearMap.ext
  intro y
  exact map_range_subtype_rangeEquivOfRangeCofinal_symm_apply I f hcofinal y

/-- The inverse is uniquely characterized by its ambient inclusion equation. -/
theorem rangeEquivOfRangeCofinal_symm_toLinearMap_eq_iff
    (v : LinearMap.range (map I f) →ₗ[AdicCompletion I R]
      AdicCompletion I (LinearMap.range f)) :
    v = (rangeEquivOfRangeCofinal I f hcofinal).symm.toLinearMap ↔
      (map I f.range.subtype).comp v =
        (LinearMap.range (map I f)).subtype := by
  constructor
  · rintro rfl
    exact map_range_subtype_comp_rangeEquivOfRangeCofinal_symm I f hcofinal
  · intro hv
    apply LinearMap.ext
    intro y
    apply (rangeEquivOfRangeCofinal I f hcofinal).injective
    apply Subtype.ext
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      coe_rangeEquivOfRangeCofinal_apply]
    exact LinearMap.congr_fun hv y

/-- The image comparison is uniquely characterized by its whole ambient forward map. -/
theorem rangeEquivOfRangeCofinal_eq_iff
    (e : AdicCompletion I (LinearMap.range f) ≃ₗ[AdicCompletion I R]
      LinearMap.range (map I f)) :
    e = rangeEquivOfRangeCofinal I f hcofinal ↔
      (LinearMap.range (map I f)).subtype.comp e.toLinearMap =
        map I f.range.subtype := by
  constructor
  · rintro rfl
    exact subtype_comp_rangeEquivOfRangeCofinal I f hcofinal
  · intro he
    apply LinearEquiv.ext
    intro z
    apply Subtype.ext
    calc
      (e z : AdicCompletion I P) = map I f.range.subtype z :=
        LinearMap.congr_fun he z
      _ = (rangeEquivOfRangeCofinal I f hcofinal z : AdicCompletion I P) :=
        (coe_rangeEquivOfRangeCofinal_apply I f hcofinal z).symm

include hcofinal

/-- Every completed-ring-linear map into the completed image factors uniquely
through completion of the original range. The factor is the inverse comparison
composed with the stock codomain restriction, for any module over the completed ring. -/
theorem rangeEquivOfRangeCofinal_existsUnique
    {X : Type uX} [AddCommMonoid X] [Module (AdicCompletion I R) X]
    (u : X →ₗ[AdicCompletion I R] AdicCompletion I P)
    (hu : LinearMap.range u ≤ LinearMap.range (map I f)) :
    ∃! v : X →ₗ[AdicCompletion I R] AdicCompletion I (LinearMap.range f),
      (map I f.range.subtype).comp v = u := by
  refine ⟨(rangeEquivOfRangeCofinal I f hcofinal).symm.toLinearMap.comp
    (u.codRestrict (LinearMap.range (map I f))
      (fun x ↦ hu (LinearMap.mem_range_self u x))), ?_, ?_⟩
  · change (map I f.range.subtype).comp
        ((rangeEquivOfRangeCofinal I f hcofinal).symm.toLinearMap.comp
          (u.codRestrict (LinearMap.range (map I f))
            (fun x ↦ hu (LinearMap.mem_range_self u x)))) = u
    rw [← LinearMap.comp_assoc, map_range_subtype_comp_rangeEquivOfRangeCofinal_symm,
      LinearMap.subtype_comp_codRestrict]
  · intro v hv
    apply LinearMap.ext
    intro x
    apply (rangeEquivOfRangeCofinal I f hcofinal).injective
    apply Subtype.ext
    calc
      (rangeEquivOfRangeCofinal I f hcofinal (v x) : AdicCompletion I P) =
          map I f.range.subtype (v x) :=
        coe_rangeEquivOfRangeCofinal_apply I f hcofinal (v x)
      _ = u x := LinearMap.congr_fun hv x
      _ = (rangeEquivOfRangeCofinal I f hcofinal
          (((rangeEquivOfRangeCofinal I f hcofinal).symm.toLinearMap.comp
            (u.codRestrict (LinearMap.range (map I f))
              (fun x ↦ hu (LinearMap.mem_range_self u x)))) x) :
            AdicCompletion I P) := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply]

end RangeCofinal

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

section CanonicalRawScalars

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

namespace AdicCompletion

private theorem eval_smul_eq_of_mk_eq (n : ℕ) (a : AdicCompletion I R) (r : R)
    (hr : Ideal.Quotient.mk (I ^ n) r = evalₐ I n a) (x : AdicCompletion I M) :
    eval I M n (a • x) = r • eval I M n x := by
  calc
    eval I M n (a • x) = a.val n • eval I M n x := smul_eval I n a x
    _ = evalₐ I n a • eval I M n x := val_smul_eq_evalₐ_smul I n a _
    _ = Ideal.Quotient.mk (I ^ n) r • eval I M n x := by rw [hr]
    _ = r • eval I M n x := algebraMap_smul (R ⧸ I ^ n) r _

end AdicCompletion

namespace LinearMap

/-- Every original-ring-linear map between canonical raw completions respects the
canonical completed-ring actions when all source ideal-power submodules are evaluation
kernels. The original target is arbitrary; neither its intrinsic completeness nor
any target or coefficient kernel equality is required. -/
theorem map_smul_adicCompletion_of_ker_eval
    (hM : ∀ n : ℕ,
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (AdicCompletion.eval I M n).ker)
    (F : AdicCompletion I M →ₗ[R] AdicCompletion I N)
    (a : AdicCompletion I R) (x : AdicCompletion I M) : F (a • x) = a • F x := by
  have h :
      F.comp (DistribSMul.toLinearMap R (AdicCompletion I M) a) =
        (DistribSMul.toLinearMap R (AdicCompletion I N) a).comp F := by
    apply AdicCompletion.ext_of_ker_eval I hM
    intro m
    apply AdicCompletion.ext
    intro n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n a)
    have hsource : a • AdicCompletion.of I M m - AdicCompletion.of I M (r • m) ∈
        (I ^ n • ⊤ : Submodule R (AdicCompletion I M)) := by
      rw [hM n, LinearMap.mem_ker, map_sub,
        AdicCompletion.eval_smul_eq_of_mk_eq I n a r hr]
      simp only [map_smul, sub_self]
    have htarget : F (a • AdicCompletion.of I M m) - F (AdicCompletion.of I M (r • m)) ∈
        (AdicCompletion.eval I N n).ker := by
      rw [← F.map_sub]
      exact AdicCompletion.pow_smul_top_le_ker_eval I (M := N) n
        (Submodule.smul_top_le_comap_smul_top (I ^ n) F hsource)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at htarget
    calc
      AdicCompletion.eval I N n (F (a • AdicCompletion.of I M m)) =
          AdicCompletion.eval I N n (F (AdicCompletion.of I M (r • m))) := htarget
      _ = r • AdicCompletion.eval I N n (F (AdicCompletion.of I M m)) := by
        simp only [map_smul]
      _ = AdicCompletion.eval I N n (a • F (AdicCompletion.of I M m)) :=
        (AdicCompletion.eval_smul_eq_of_mk_eq I n a r hr _).symm
  exact LinearMap.congr_fun h x

end LinearMap

namespace AdicCompletion

/-- Restriction of scalars between canonical raw completions is an equivalence
linear over the completed ring when all source ideal-power submodules are evaluation
kernels. Its inverse keeps the original function and additive map. Both Hom modules
have the pointwise completed-ring action on the target; the original target is arbitrary. -/
def restrictScalarsHomEquivOfKernel
    (hM : ∀ n : ℕ,
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker) :
    (AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N) ≃ₗ[AdicCompletion I R]
      (AdicCompletion I M →ₗ[R] AdicCompletion I N) where
  toLinearMap :=
    LinearMap.restrictScalarsₗ (R := R) (S := AdicCompletion I R)
      (M := AdicCompletion I M) (N := AdicCompletion I N) (R₁ := AdicCompletion I R)
  invFun F :=
    { F.toAddHom with
      map_smul' := LinearMap.map_smul_adicCompletion_of_ker_eval I hM F }
  left_inv G := by
    apply LinearMap.ext
    intro x
    rfl
  right_inv F := by
    apply LinearMap.ext
    intro x
    rfl

/-- The forward linear map is Mathlib's canonical restriction-of-scalars map. -/
@[simp]
theorem restrictScalarsHomEquivOfKernel_toLinearMap
    (hM : ∀ n : ℕ,
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker) :
    (restrictScalarsHomEquivOfKernel I (N := N) hM).toLinearMap =
      LinearMap.restrictScalarsₗ (R := R) (S := AdicCompletion I R)
        (M := AdicCompletion I M) (N := AdicCompletion I N) (R₁ := AdicCompletion I R) :=
  rfl

/-- The source-kernel equivalence restricts scalars to the original ring. -/
@[simp]
theorem restrictScalarsHomEquivOfKernel_apply
    (hM : ∀ n : ℕ,
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker)
    (G : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N) :
    restrictScalarsHomEquivOfKernel I hM G = G.restrictScalars R :=
  rfl

/-- The inverse source-kernel equivalence evaluates as the original map. -/
@[simp]
theorem restrictScalarsHomEquivOfKernel_symm_apply
    (hM : ∀ n : ℕ,
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker)
    (F : AdicCompletion I M →ₗ[R] AdicCompletion I N) (x : AdicCompletion I M) :
    (restrictScalarsHomEquivOfKernel I hM).symm F x = F x :=
  rfl

/-- Restricting the inverse source-kernel equivalence recovers the original linear map. -/
@[simp]
theorem restrictScalarsHomEquivOfKernel_symm_apply_restrictScalars
    (hM : ∀ n : ℕ,
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker)
    (F : AdicCompletion I M →ₗ[R] AdicCompletion I N) :
    ((restrictScalarsHomEquivOfKernel I hM).symm F).restrictScalars R = F := by
  apply LinearMap.ext
  intro x
  rfl

/-- The inverse source-kernel equivalence recovers a completed-ring-linear map
from its restriction. -/
@[simp]
theorem restrictScalarsHomEquivOfKernel_symm_restrictScalars
    (hM : ∀ n : ℕ,
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker)
    (G : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N) :
    (restrictScalarsHomEquivOfKernel I hM).symm (G.restrictScalars R) = G := by
  apply LinearMap.ext
  intro x
  rfl

/-- On canonical raw completions, the positive-finitely-generated-power equivalence
agrees with the source-kernel equivalence for any proof of the source kernel identities. -/
theorem restrictScalarsHomEquivOfFGPow_eq_restrictScalarsHomEquivOfKernel
    {p : ℕ} (hp : 0 < p) (hI : (I ^ p).FG)
    (hM : ∀ n : ℕ,
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker) :
    restrictScalarsHomEquivOfFGPow I (P := AdicCompletion I M) (T := AdicCompletion I N) hp hI =
      restrictScalarsHomEquivOfKernel I hM := by
  apply LinearEquiv.ext
  intro G
  rfl

end AdicCompletion

end CanonicalRawScalars

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
