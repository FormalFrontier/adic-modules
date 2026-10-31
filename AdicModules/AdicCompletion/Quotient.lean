/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import AdicModules.AdicCompletion.Kernel
public import AdicModules.AdicCompletion.RestrictScalars
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic

import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import AdicModules.LinearAlgebra.Descent
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Quotients of adic completions

The coordinate projections are semilinear over the corresponding coefficient
evaluations, including the normalized first projection to the residue quotient.
For every `m ≤ n`, the original two-stage quotient `I^m M / I^n M` is canonically
isomorphic to the quotient of the evaluation kernels at `m` and `n`. This comparison
is induced by the original map to the completion and needs no finiteness assumption.
It also supplies original representatives for the unconditional scalar law: the
`p`th coefficient evaluation kernel times the `q`th module evaluation kernel lies
in the `(p + q)`th module evaluation kernel. The comparisons preserve leading
scalar products of original representatives, requiring only next-precision agreement
for each factor. No evaluation kernel is identified with an intrinsic ideal-power
submodule of the completion here.

Let `I` be an ideal of a commutative ring `R`, put `S = AdicCompletion I R`,
and let `J` be the extension of `I` to `S`. If `I.Cotangent` is finite over `R ⧸ I`,
evaluation gives an algebra equivalence `S ⧸ J ^ n ≃ₐ[R] R ⧸ I ^ n` at every degree.
For every original `R`-module `M`, it also gives an equivalence from
`AdicCompletion I M ⧸ J ^ n • ⊤` to `M ⧸ I ^ n • ⊤`, semilinear over that
coefficient equivalence. Both quotients have their canonical quotient-coefficient
actions; no `S`-action on the original module is required. Semilinear maps from
`M` with coefficients reduced modulo `I ^ n` extend uniquely to this completed quotient.

Independently, finite generation of one specified positive power of `I` identifies
every original-`R` ideal-power quotient of the completion with the corresponding
quotient of the original module, linearly over `R`. For coefficients this gives
an algebra equivalence from the quotient by `J ^ n` to `R ⧸ I ^ n`. The fixed-stage
coefficient comparison needs only finite generation of that stage's ideal power.
Finite cotangent and finite generation of a positive original power are separate
sufficient conditions, with no implication required in either direction. The
comparisons agree wherever both hypotheses hold, after the class-preserving
restriction-of-scalars and ideal/submodule quotient identifications.

The forward maps are induced by evaluation; their inverses are induced by the
original maps to the completion. The comparisons are natural in original linear
maps and compatible with precision transitions. Degree zero, trivial rings and
independent ring and module universes are included, without finiteness, separation
or completeness assumptions on the original module.

For an arbitrary ideal, flatness, projectivity or finite presentation of the raw
completion over its completed coefficient ring descends to every original ideal-power
quotient over its coefficient quotient, including degree zero. The original quotient
is a retract of scalar extension of the completed module along evaluation. Only this
one-sided retraction is used; no identification of evaluation kernels with extended
ideal powers is required.

## References

The semilinear projections bundle the coordinate evaluation and completed-module
scalar laws from Mathlib's `RingTheory/AdicCompletion/Basic.lean` and `Algebra.lean`,
by Kenny Lau, Judith Ludwig, Christian Merten and Jiedong Jiang. Their targets use
the quotient module action from Pierre-Alexandre Bazin's
`Algebra/Module/Torsion/Basic.lean`.

The construction uses Mathlib's quotient equivalence for equal ideals and its
first isomorphism theorems for linear maps and algebras. The inverses are
described using Mathlib's
algebra homomorphism induced on ideal quotients. The finite-cotangent kernel
input uses Andrew Yang's ideal cotangent formalization. The module comparison
uses the restriction-of-scalars equivalence in this library. Its specialized
inverse-pair proofs follow this library's semilinear Chinese remainder pattern,
using Mathlib's inverse-pair and semilinear-equivalence APIs by Nathaniel Thomas,
Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen, Frédéric Dupuis and
Heather Macbeth. Extension from original residues uses this library's descent
along surjective semilinear maps. Detailed quotient and first-isomorphism credits
are in `docs/CREDITS.md`.
The descent statements use
Christian Merten's flat base-change and retract results in Mathlib, Kevin Buzzard
and Antoine Labelle's projective tensor and splitting results, and the quotient–tensor
equivalence of Antoine Chambert-Loir and Jujian Zhang. Scalar extension of maps uses
Mathlib's `LinearMap.liftBaseChange`. Finite-presentation descent uses Andrew Yang's
base-change and surjective-image results in `Algebra/Module/FinitePresentation.lean`,
together with Mathlib's split kernel/range identity and finite-range theorem.
-/

@[expose] public section

universe u v w uR uM

open TensorProduct

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- Evaluation at precision `n`, semilinear over the canonical coefficient evaluation. -/
noncomputable def evalₛₗ (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    AdicCompletion I M →ₛₗ[(evalₐ I n).toRingHom]
      M ⧸ (I ^ n • (⊤ : Submodule R M)) where
  toFun := eval I M n
  map_add' := (eval I M n).map_add
  map_smul' s x := val_smul_eq_evalₐ_smul I n s (x.val n)

/-- The semilinear projection has the original-ring-linear evaluation as its
underlying function. -/
@[simp]
theorem evalₛₗ_apply (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (x : AdicCompletion I M) :
    evalₛₗ I M n x = eval I M n x := rfl

/-- The projection sends an original element to its residue class. -/
@[simp]
theorem evalₛₗ_of (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (m : M) :
    evalₛₗ I M n (of I M m) = (I ^ n • (⊤ : Submodule R M)).mkQ m :=
  eval_of I M n m

/-- Every stage projection is surjective. -/
theorem evalₛₗ_surjective (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) :
    Function.Surjective (evalₛₗ I M n) := eval_surjective I M n

/-- The semilinear projections commute with the precision transitions. -/
theorem transitionMap_evalₛₗ (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I M) :
    transitionMap I M hmn (evalₛₗ I M n x) = evalₛₗ I M m x :=
  transitionMap_comp_eval_apply I M hmn x

/-- First evaluation with codomain the original first quotient and coefficient
map to the residue ring `R ⧸ I`. -/
noncomputable def evalOneₛₗ (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    AdicCompletion I M →ₛₗ[(evalOneₐ I).toRingHom]
      M ⧸ (I • (⊤ : Submodule R M)) where
  toFun x :=
    Submodule.factor
      (show (I ^ 1 • (⊤ : Submodule R M)) ≤ I • (⊤ : Submodule R M) by simp)
      (evalₛₗ I M 1 x)
  map_add' x y := by simp only [map_add]
  map_smul' s x := by
    induction s using induction_on I R with | _ s =>
    induction x using induction_on I M with | _ x =>
    rfl

/-- First semilinear evaluation agrees with original-ring-linear evaluation,
followed by the canonical first-quotient factor. -/
@[simp]
theorem evalOneₛₗ_apply (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (x : AdicCompletion I M) :
    evalOneₛₗ I M x =
      Submodule.factor
        (show (I ^ 1 • (⊤ : Submodule R M)) ≤ I • (⊤ : Submodule R M) by simp)
        (eval I M 1 x) := rfl

/-- The normalized projection takes an original element to its first residue. -/
@[simp]
theorem evalOneₛₗ_of (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (m : M) :
    evalOneₛₗ I M (of I M m) = (I • (⊤ : Submodule R M)).mkQ m := rfl

/-- Normalization to the first quotient preserves surjectivity. -/
theorem evalOneₛₗ_surjective (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    Function.Surjective (evalOneₛₗ I M) := by
  intro q
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) q
  exact ⟨of I M m, evalOneₛₗ_of I M m⟩

/-- For the coefficient module, normalized semilinear evaluation is the canonical
algebra evaluation after the class-preserving ideal quotient factor. -/
theorem factor_evalOneₛₗ_eq_evalOneₐ (I : Ideal R) (x : AdicCompletion I R) :
    Ideal.Quotient.factor (show (I • ⊤ : Ideal R) ≤ I by simp)
      (evalOneₛₗ I R x) = evalOneₐ I x := by
  rw [evalOneₛₗ_apply, ← factorₐ_evalₐ_one,
    ← factor_eval_eq_evalₐ I x (le_of_eq (Ideal.mul_top _))]
  exact Quotient.inductionOn' (eval I R 1 x) (fun _ ↦ rfl)

private noncomputable def powToKerEvalQuotient (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (m n : ℕ) :
    ↥(I ^ m • (⊤ : Submodule R M)) →ₗ[R]
      (eval I M m).ker ⧸ ((eval I M n).ker).comap ((eval I M m).ker).subtype :=
  (((eval I M n).ker).comap ((eval I M m).ker).subtype).mkQ.comp
    (((of I M).comp (I ^ m • (⊤ : Submodule R M)).subtype).codRestrict
      (eval I M m).ker (fun a => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, eval_of]
        exact (Submodule.Quotient.mk_eq_zero _).mpr a.property))

private theorem ker_powToKerEvalQuotient (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (m n : ℕ) :
    (powToKerEvalQuotient I M m n).ker =
      (I ^ n • (⊤ : Submodule R M)).comap
        (I ^ m • (⊤ : Submodule R M)).subtype := by
  rw [powToKerEvalQuotient, LinearMap.ker_comp, Submodule.ker_mkQ]
  ext a
  change eval I M n (of I M (a : M)) = 0 ↔ (a : M) ∈ I ^ n • (⊤ : Submodule R M)
  rw [eval_of]
  exact Submodule.Quotient.mk_eq_zero _

private theorem exists_pow_representative (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (hmn : m ≤ n)
    (x : (eval I M m).ker) :
    ∃ a : ↥(I ^ m • (⊤ : Submodule R M)),
      (I ^ n • (⊤ : Submodule R M)).mkQ (a : M) = eval I M n (x : AdicCompletion I M) := by
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective
    (I ^ n • (⊤ : Submodule R M)) (eval I M n (x : AdicCompletion I M))
  have ham : (I ^ m • (⊤ : Submodule R M)).mkQ a = 0 := by
    calc
      _ = transitionMap I M hmn ((I ^ n • (⊤ : Submodule R M)).mkQ a) :=
        (Submodule.factor_mk (Submodule.pow_smul_top_le I M hmn) a).symm
      _ = eval I M m (x : AdicCompletion I M) := by
        rw [ha]
        exact transitionMap_comp_eval_apply I M hmn (x : AdicCompletion I M)
      _ = 0 := x.property
  exact ⟨⟨a, (Submodule.Quotient.mk_eq_zero _).mp ham⟩, ha⟩

private theorem surjective_powToKerEvalQuotient (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (powToKerEvalQuotient I M m n) := by
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨a, ha⟩ := exists_pow_representative I M hmn x
  refine ⟨a, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  change eval I M n (of I M (a : M) - (x : AdicCompletion I M)) = 0
  rw [map_sub, eval_of, ha, sub_self]

/-- The original two-stage ideal-power quotient is the quotient of the corresponding
completion evaluation kernels. The forward map is induced by `of`, with no finite-generation,
separation or completeness assumption on the original module. -/
noncomputable def powQuotientEquivKerEvalQuotient (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (hmn : m ≤ n) :
    (↥(I ^ m • (⊤ : Submodule R M)) ⧸
      (I ^ n • (⊤ : Submodule R M)).comap
        (I ^ m • (⊤ : Submodule R M)).subtype) ≃ₗ[R]
    ((eval I M m).ker ⧸
      ((eval I M n).ker).comap ((eval I M m).ker).subtype) :=
  private_decl% ((Submodule.quotEquivOfEq _ _
    (ker_powToKerEvalQuotient I M m n).symm).trans
      ((powToKerEvalQuotient I M m n).quotKerEquivOfSurjective
        (surjective_powToKerEvalQuotient I M hmn)))

/-- The kernel-quotient comparison takes an original representative to its canonical
image in the completion. -/
@[simp]
theorem powQuotientEquivKerEvalQuotient_mk (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (hmn : m ≤ n)
    (a : ↥(I ^ m • (⊤ : Submodule R M))) :
    powQuotientEquivKerEvalQuotient I M hmn (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (⟨of I M (a : M), by
        rw [LinearMap.mem_ker, eval_of]
        exact (Submodule.Quotient.mk_eq_zero _).mpr a.property⟩ : (eval I M m).ker) := by
  simp only [powQuotientEquivKerEvalQuotient]
  rfl

/-- An original representative of the higher evaluation computes the inverse comparison. -/
theorem powQuotientEquivKerEvalQuotient_symm_mk (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (hmn : m ≤ n)
    (x : (eval I M m).ker) (a : ↥(I ^ m • (⊤ : Submodule R M)))
    (ha : (I ^ n • (⊤ : Submodule R M)).mkQ (a : M) =
      eval I M n (x : AdicCompletion I M)) :
    (powQuotientEquivKerEvalQuotient I M hmn).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk a := by
  apply (powQuotientEquivKerEvalQuotient I M hmn).injective
  rw [LinearEquiv.apply_symm_apply, powQuotientEquivKerEvalQuotient_mk]
  apply (Submodule.Quotient.eq _).mpr
  change eval I M n ((x : AdicCompletion I M) - of I M (a : M)) = 0
  rw [map_sub, eval_of, ha, sub_self]

/-- The inverse comparison followed by the original quotient inclusion agrees with
higher evaluation on the whole lower evaluation kernel. -/
theorem mapQ_comp_powQuotientEquivKerEvalQuotient_symm (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (hmn : m ≤ n) :
    (((I ^ n • (⊤ : Submodule R M)).comap
        (I ^ m • (⊤ : Submodule R M)).subtype).mapQ
      (I ^ n • (⊤ : Submodule R M)) (I ^ m • (⊤ : Submodule R M)).subtype le_rfl).comp
      ((powQuotientEquivKerEvalQuotient I M hmn).symm.toLinearMap.comp
        (((eval I M n).ker).comap ((eval I M m).ker).subtype).mkQ) =
      (eval I M n).comp ((eval I M m).ker).subtype := by
  ext x
  obtain ⟨a, ha⟩ := exists_pow_representative I M hmn x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
    powQuotientEquivKerEvalQuotient_symm_mk I M hmn x a ha,
    Submodule.mapQ_apply, Submodule.coe_subtype] using ha

/-- A coefficient in the `p`th evaluation kernel takes the `q`th module evaluation
kernel into the `(p + q)`th kernel, unconditionally for the canonical completed action.
Original representatives are supplied by the two-stage quotient comparison. -/
theorem smul_mem_ker_eval_add (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] {p q : ℕ}
    {s : AdicCompletion I R} {x : AdicCompletion I M}
    (hs : s ∈ (eval I R p).ker) (hx : x ∈ (eval I M q).ker) :
    s • x ∈ (eval I M (p + q)).ker := by
  let es := powQuotientEquivKerEvalQuotient I R (Nat.le_add_right p q)
  let ex := powQuotientEquivKerEvalQuotient I M (Nat.le_add_left q p)
  obtain ⟨r, hr⟩ := Submodule.mkQ_surjective _
    (es.symm (Submodule.Quotient.mk (⟨s, hs⟩ : (eval I R p).ker)))
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective _
    (ex.symm (Submodule.Quotient.mk (⟨x, hx⟩ : (eval I M q).ker)))
  have hrval : (I ^ (p + q) • (⊤ : Submodule R R)).mkQ (r : R) = eval I R (p + q) s := by
    have h := LinearMap.congr_fun
      (mapQ_comp_powQuotientEquivKerEvalQuotient_symm I R (Nat.le_add_right p q))
      (⟨s, hs⟩ : (eval I R p).ker)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply] at h
    rw [← hr] at h
    exact h
  have haval : (I ^ (p + q) • (⊤ : Submodule R M)).mkQ (a : M) = eval I M (p + q) x := by
    have h := LinearMap.congr_fun
      (mapQ_comp_powQuotientEquivKerEvalQuotient_symm I M (Nat.le_add_left q p))
      (⟨x, hx⟩ : (eval I M q).ker)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply] at h
    rw [← ha] at h
    exact h
  have hrpow : (r : R) ∈ I ^ p := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using r.property
  have hprod : (r : R) • (a : M) ∈ I ^ (p + q) • (⊤ : Submodule R M) := by
    rw [pow_add, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hrpow a.property
  change eval I R (p + q) s • eval I M (p + q) x = 0
  rw [← hrval, ← haval]
  change (Submodule.Quotient.mk ((r : R) • (a : M)) :
    M ⧸ (I ^ (p + q) • (⊤ : Submodule R M))) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr hprod

/-- Leading scalar products computed through the kernel-quotient comparison are the
products of original representatives. Each factor need only agree with its representative
at its own next precision. -/
theorem powQuotientEquivKerEvalQuotient_symm_mk_smul (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (p q : ℕ)
    (s : (eval I R p).ker) (x : (eval I M q).ker)
    (r : R) (hr : r ∈ I ^ p) (a : M) (ha : a ∈ I ^ q • (⊤ : Submodule R M))
    (hsr : (I ^ (p + 1) • (⊤ : Submodule R R)).mkQ r =
      eval I R (p + 1) (s : AdicCompletion I R))
    (hxa : (I ^ (q + 1) • (⊤ : Submodule R M)).mkQ a =
      eval I M (q + 1) (x : AdicCompletion I M)) :
    (powQuotientEquivKerEvalQuotient I M (Nat.le_succ (p + q))).symm
      (Submodule.Quotient.mk
        (⟨(s : AdicCompletion I R) • (x : AdicCompletion I M),
          smul_mem_ker_eval_add I M s.property x.property⟩ : (eval I M (p + q)).ker)) =
      Submodule.Quotient.mk (⟨r • a, by
        rw [pow_add, Submodule.mul_smul]
        exact Submodule.smul_mem_smul hr ha⟩ :
          ↥(I ^ (p + q) • (⊤ : Submodule R M))) := by
  have hs : (s : AdicCompletion I R) - of I R r ∈ (eval I R (p + 1)).ker := by
    rw [LinearMap.mem_ker, map_sub, eval_of, hsr, sub_self]
  have hx : (x : AdicCompletion I M) - of I M a ∈ (eval I M (q + 1)).ker := by
    rw [LinearMap.mem_ker, map_sub, eval_of, hxa, sub_self]
  have hrmem : of I R r ∈ (eval I R p).ker := by
    rw [LinearMap.mem_ker, eval_of]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hr
  have hleft : ((s : AdicCompletion I R) - of I R r) • (x : AdicCompletion I M) ∈
      (eval I M (p + q + 1)).ker := by
    exact Eq.mp (congrArg
      (fun n => ((s : AdicCompletion I R) - of I R r) • (x : AdicCompletion I M) ∈
        (eval I M n).ker) (Nat.add_right_comm p 1 q))
      (smul_mem_ker_eval_add I M hs x.property)
  have hright : of I R r • ((x : AdicCompletion I M) - of I M a) ∈
      (eval I M (p + q + 1)).ker := by
    exact Eq.mp (congrArg
      (fun n => of I R r • ((x : AdicCompletion I M) - of I M a) ∈
        (eval I M n).ker) (Nat.add_assoc p q 1).symm)
      (smul_mem_ker_eval_add I M hrmem hx)
  have hdiff : (s : AdicCompletion I R) • (x : AdicCompletion I M) -
      of I R r • of I M a ∈ (eval I M (p + q + 1)).ker := by
    simpa only [sub_smul, smul_sub, sub_add_sub_cancel] using
      (eval I M (p + q + 1)).ker.add_mem hleft hright
  apply powQuotientEquivKerEvalQuotient_symm_mk
  have h := LinearMap.mem_ker.mp hdiff
  rw [map_sub, sub_eq_zero] at h
  calc
    _ = eval I M (p + q + 1) (of I R r • of I M a) := rfl
    _ = eval I M (p + q + 1) ((s : AdicCompletion I R) • (x : AdicCompletion I M)) := h.symm

private noncomputable def quotientPowLinearEquivOfKernel
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ)
    (h : I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker) :
    (AdicCompletion I M ⧸ (I ^ n • (⊤ : Submodule R (AdicCompletion I M)))) ≃ₗ[R]
      M ⧸ (I ^ n • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _ h).trans
    ((eval I M n).quotKerEquivOfSurjective (eval_surjective I M n))

private theorem quotientPowLinearEquivOfKernel_mk
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ)
    (h : I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker)
    (x : AdicCompletion I M) :
    quotientPowLinearEquivOfKernel I M n h (Submodule.Quotient.mk x) =
      eval I M n x := by
  simp [quotientPowLinearEquivOfKernel]

private theorem quotientPowLinearEquivOfKernel_symm_mk
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ)
    (h : I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker) (m : M) :
    (quotientPowLinearEquivOfKernel I M n h).symm (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (of I M m) := by
  apply (quotientPowLinearEquivOfKernel I M n h).injective
  rw [LinearEquiv.apply_symm_apply, quotientPowLinearEquivOfKernel_mk, eval_of]
  rfl

private theorem quotientPowLinearEquivOfKernel_natural
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] (n : ℕ)
    (hM : I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker)
    (hN : I ^ n • (⊤ : Submodule R (AdicCompletion I N)) = (eval I N n).ker)
    (f : M →ₗ[R] N)
    (z : AdicCompletion I M ⧸ (I ^ n • (⊤ : Submodule R (AdicCompletion I M)))) :
    quotientPowLinearEquivOfKernel I N n hN
        ((((map I f).restrictScalars R).reduceModIdeal (I ^ n)).restrictScalars R z) =
      ((f.reduceModIdeal (I ^ n)).restrictScalars R)
        (quotientPowLinearEquivOfKernel I M n hM z) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  simpa only [LinearMap.restrictScalars_apply, LinearMap.reduceModIdeal_apply,
    Submodule.mkQ_apply, quotientPowLinearEquivOfKernel_mk, eval_apply] using map_val_apply I f x

private theorem quotientPowLinearEquivOfKernel_transitionMap
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    {m n : ℕ} (hmn : m ≤ n)
    (hm : I ^ m • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M m).ker)
    (hn : I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker)
    (z : AdicCompletion I M ⧸ (I ^ n • (⊤ : Submodule R (AdicCompletion I M)))) :
    quotientPowLinearEquivOfKernel I M m hm
        (transitionMap I (AdicCompletion I M) hmn z) =
      transitionMap I M hmn (quotientPowLinearEquivOfKernel I M n hn z) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  rw [Submodule.factor_mk, Submodule.mkQ_apply, Submodule.mkQ_apply,
    quotientPowLinearEquivOfKernel_mk, quotientPowLinearEquivOfKernel_mk]
  exact (transitionMap_comp_eval_apply I M hmn x).symm

/-- The quotient of a completed module by an ideal power is the corresponding
quotient of the original module, if one positive ideal power is finitely generated. -/
noncomputable def quotientPowLinearEquivOfFGPow (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) :
    (AdicCompletion I M ⧸ (I ^ k • (⊤ : Submodule R (AdicCompletion I M)))) ≃ₗ[R]
      M ⧸ (I ^ k • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k)).trans
      ((eval I M k).quotKerEquivOfSurjective (eval_surjective I M k))

/-- The module comparison sends every completed representative to its evaluation. -/
@[simp]
theorem quotientPowLinearEquivOfFGPow_mk (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (x : AdicCompletion I M) :
    quotientPowLinearEquivOfFGPow I M hn hI k (Submodule.Quotient.mk x) =
      eval I M k x := by
  exact quotientPowLinearEquivOfKernel_mk I M k
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k) x

/-- The module comparison preserves the residue of every original element. -/
theorem quotientPowLinearEquivOfFGPow_of (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (m : M) :
    quotientPowLinearEquivOfFGPow I M hn hI k
        (Submodule.Quotient.mk (of I M m)) = Submodule.Quotient.mk m := by
  rw [quotientPowLinearEquivOfFGPow_mk, eval_of]
  rfl

/-- The inverse module comparison is induced by the original map to the completion. -/
@[simp]
theorem quotientPowLinearEquivOfFGPow_symm_mk (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (m : M) :
    (quotientPowLinearEquivOfFGPow I M hn hI k).symm (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (of I M m) := by
  exact quotientPowLinearEquivOfKernel_symm_mk I M k
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k) m

/-- The inverse module comparison recovers the class of every completed element
from its evaluation. -/
theorem quotientPowLinearEquivOfFGPow_symm_eval (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (x : AdicCompletion I M) :
    (quotientPowLinearEquivOfFGPow I M hn hI k).symm (eval I M k x) =
      Submodule.Quotient.mk x := by
  rw [← quotientPowLinearEquivOfFGPow_mk I M hn hI k x,
    LinearEquiv.symm_apply_apply]

/-- Quotient comparisons commute with the quotient maps induced by every original
linear map. -/
theorem quotientPowLinearEquivOfFGPow_natural (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (f : M →ₗ[R] N)
    (z : AdicCompletion I M ⧸ (I ^ k • (⊤ : Submodule R (AdicCompletion I M)))) :
    quotientPowLinearEquivOfFGPow I N hn hI k
        ((((map I f).restrictScalars R).reduceModIdeal (I ^ k)).restrictScalars R z) =
      ((f.reduceModIdeal (I ^ k)).restrictScalars R)
        (quotientPowLinearEquivOfFGPow I M hn hI k z) := by
  exact quotientPowLinearEquivOfKernel_natural I M k
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k)
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k) f z

/-- Quotient comparisons commute with the intrinsic precision projections on the
completion and the precision projections on the original module. -/
theorem quotientPowLinearEquivOfFGPow_transitionMap (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) {j k : ℕ} (hjk : j ≤ k)
    (z : AdicCompletion I M ⧸ (I ^ k • (⊤ : Submodule R (AdicCompletion I M)))) :
    quotientPowLinearEquivOfFGPow I M hn hI j
        (transitionMap I (AdicCompletion I M) hjk z) =
      transitionMap I M hjk (quotientPowLinearEquivOfFGPow I M hn hI k z) := by
  exact quotientPowLinearEquivOfKernel_transitionMap I M hjk
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI j)
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k) z

/-- The linear evaluation kernel determines the coefficient evaluation kernel. -/
theorem map_pow_eq_ker_evalₐ (I : Ideal R) (n : ℕ)
    (h : (I ^ n) • (⊤ : Submodule R (AdicCompletion I R)) = (eval I R n).ker) :
    (I.map (algebraMap R (AdicCompletion I R))) ^ n =
      RingHom.ker (evalₐ I n).toRingHom := by
  have hpow :
      ((I.map (algebraMap R (AdicCompletion I R))) ^ n).restrictScalars R =
        (eval I R n).ker := by
    rw [← Ideal.map_pow, ← Ideal.smul_top_eq_map]
    exact h
  have htop : (I ^ n • ⊤ : Ideal R) = I ^ n := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  ext x
  change x ∈ ((I.map (algebraMap R (AdicCompletion I R))) ^ n).restrictScalars R ↔
    evalₐ I n x = 0
  rw [hpow, LinearMap.mem_ker]
  constructor
  · intro hx
    rw [← factor_eval_eq_evalₐ I x htop.le, hx]
    rfl
  · intro hx
    rw [← factor_evalₐ_eq_eval I x htop.ge, hx]
    rfl

private noncomputable def quotientPowAlgEquivOfKernel
    (I : Ideal R) (n : ℕ)
    (h : I ^ n • (⊤ : Submodule R (AdicCompletion I R)) = (eval I R n).ker) :
    (AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n) ≃ₐ[R]
      R ⧸ I ^ n :=
  (Ideal.quotientEquivAlgOfEq R (map_pow_eq_ker_evalₐ I n h)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n))

private theorem quotientPowAlgEquiv_mk_of_kernel (I : Ideal R) (n : ℕ)
    (h : (I ^ n) • (⊤ : Submodule R (AdicCompletion I R)) = (eval I R n).ker)
    (x : AdicCompletion I R) :
    quotientPowAlgEquivOfKernel I n h
        (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n) x) =
      evalₐ I n x := by
  change (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n))
      (Ideal.Quotient.mk (RingHom.ker (evalₐ I n).toRingHom) x) = _
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (surjective_evalₐ I n) x

private theorem quotientPowAlgEquivOfKernel_symm_mk (I : Ideal R) (n : ℕ)
    (h : I ^ n • (⊤ : Submodule R (AdicCompletion I R)) = (eval I R n).ker) (r : R) :
    (quotientPowAlgEquivOfKernel I n h).symm (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n)
        (algebraMap R (AdicCompletion I R) r) := by
  apply (quotientPowAlgEquivOfKernel I n h).injective
  simpa only [AlgEquiv.apply_symm_apply, quotientPowAlgEquiv_mk_of_kernel,
    Ideal.Quotient.algebraMap_eq] using ((evalₐ I n).commutes r).symm

private theorem quotientPowAlgEquivOfKernel_symm_toAlgHom (I : Ideal R) (n : ℕ)
    (h : I ^ n • (⊤ : Submodule R (AdicCompletion I R)) = (eval I R n).ker) :
    (quotientPowAlgEquivOfKernel I n h).symm.toAlgHom =
      Ideal.quotientMapₐ ((I.map (algebraMap R (AdicCompletion I R))) ^ n)
        (Algebra.ofId R (AdicCompletion I R))
        (by
          change I ^ n ≤
            ((I.map (algebraMap R (AdicCompletion I R))) ^ n).comap
              (algebraMap R (AdicCompletion I R))
          rw [← Ideal.map_pow (algebraMap R (AdicCompletion I R)) I n]
          exact Ideal.le_comap_map) := by
  apply AlgHom.ext
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simpa only [AlgEquiv.toAlgHom_apply, Ideal.quotient_map_mkₐ,
    Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply] using
    quotientPowAlgEquivOfKernel_symm_mk I n h r

private theorem quotientPowAlgEquivOfKernel_factor (I : Ideal R)
    {j k : ℕ} (hjk : j ≤ k)
    (hj : I ^ j • (⊤ : Submodule R (AdicCompletion I R)) = (eval I R j).ker)
    (hk : I ^ k • (⊤ : Submodule R (AdicCompletion I R)) = (eval I R k).ker)
    (z : AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ k) :
    quotientPowAlgEquivOfKernel I j hj
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hjk) z) =
      Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hjk)
        (quotientPowAlgEquivOfKernel I k hk z) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (quotientPowAlgEquivOfKernel I k hk z)
  have hz := congrArg (quotientPowAlgEquivOfKernel I k hk).symm hr
  rw [AlgEquiv.symm_apply_apply, quotientPowAlgEquivOfKernel_symm_mk] at hz
  rw [← hz]
  change quotientPowAlgEquivOfKernel I j hj
      (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ j)
        (algebraMap R (AdicCompletion I R) r)) = _
  rw [quotientPowAlgEquiv_mk_of_kernel, quotientPowAlgEquiv_mk_of_kernel,
    (evalₐ I j).commutes, (evalₐ I k).commutes]
  exact ((Ideal.Quotient.factorₐ R
    (show I ^ k ≤ I ^ j from Ideal.pow_le_pow_right hjk)).commutes r).symm

/-- Evaluation identifies the quotient of the adic completion by the `n`th power
of the extended ideal with `R ⧸ I ^ n`, assuming only that `I ^ n` is finitely
generated. -/
noncomputable def quotientPowAlgEquiv (I : Ideal R) (n : ℕ) (h : (I ^ n).FG) :
    (AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n) ≃ₐ[R]
      R ⧸ I ^ n :=
  (Ideal.quotientEquivAlgOfEq R (by
    exact map_pow_eq_ker_evalₐ I n (pow_smul_top_eq_ker_eval_of_fg_pow h))).trans
      (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n))

/-- The quotient comparison sends a completion representative to its evaluation. -/
@[simp]
theorem quotientPowAlgEquiv_mk (I : Ideal R) (n : ℕ) (h : (I ^ n).FG)
    (x : AdicCompletion I R) :
    quotientPowAlgEquiv I n h
        (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n) x) =
      evalₐ I n x := by
  exact quotientPowAlgEquiv_mk_of_kernel I n (pow_smul_top_eq_ker_eval_of_fg_pow h) x

/-- The inverse comparison sends a residue class to the class of its image in
the adic completion. -/
@[simp]
theorem quotientPowAlgEquiv_symm_mk (I : Ideal R) (n : ℕ) (h : (I ^ n).FG) (r : R) :
    (quotientPowAlgEquiv I n h).symm (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n)
        (algebraMap R (AdicCompletion I R) r) := by
  exact quotientPowAlgEquivOfKernel_symm_mk I n
    (pow_smul_top_eq_ker_eval_of_fg_pow h) r

/-- The inverse comparison is the algebra homomorphism on quotients induced by
the algebra map to the completion. -/
theorem quotientPowAlgEquiv_symm_toAlgHom (I : Ideal R) (n : ℕ) (h : (I ^ n).FG) :
    (quotientPowAlgEquiv I n h).symm.toAlgHom =
      Ideal.quotientMapₐ ((I.map (algebraMap R (AdicCompletion I R))) ^ n)
        (Algebra.ofId R (AdicCompletion I R))
        (by
          change I ^ n ≤
            ((I.map (algebraMap R (AdicCompletion I R))) ^ n).comap
              (algebraMap R (AdicCompletion I R))
          rw [← Ideal.map_pow (algebraMap R (AdicCompletion I R)) I n]
          exact Ideal.le_comap_map) := by
  exact quotientPowAlgEquivOfKernel_symm_toAlgHom I n
    (pow_smul_top_eq_ker_eval_of_fg_pow h)

/-- If one positive ideal power is finitely generated, evaluation identifies every
quotient of the completed coefficient ring with the corresponding original quotient. -/
noncomputable def quotientPowAlgEquivOfFGPow (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) :
    (AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ k) ≃ₐ[R]
      R ⧸ I ^ k :=
  (Ideal.quotientEquivAlgOfEq R (by
    exact map_pow_eq_ker_evalₐ I k (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k))).trans
      (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I k))

/-- The positive-power coefficient comparison sends every representative to its evaluation. -/
@[simp]
theorem quotientPowAlgEquivOfFGPow_mk (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (x : AdicCompletion I R) :
    quotientPowAlgEquivOfFGPow I hn hI k
        (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ k) x) =
      evalₐ I k x := by
  exact quotientPowAlgEquiv_mk_of_kernel I k
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k) x

/-- The inverse positive-power coefficient comparison is induced by the algebra map
to the completion. -/
@[simp]
theorem quotientPowAlgEquivOfFGPow_symm_mk (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (r : R) :
    (quotientPowAlgEquivOfFGPow I hn hI k).symm (Ideal.Quotient.mk (I ^ k) r) =
      Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ k)
        (algebraMap R (AdicCompletion I R) r) := by
  exact quotientPowAlgEquivOfKernel_symm_mk I k
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k) r

/-- The whole inverse of the positive-power coefficient comparison is the induced
algebra homomorphism on ideal quotients. -/
theorem quotientPowAlgEquivOfFGPow_symm_toAlgHom (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) :
    (quotientPowAlgEquivOfFGPow I hn hI k).symm.toAlgHom =
      Ideal.quotientMapₐ ((I.map (algebraMap R (AdicCompletion I R))) ^ k)
        (Algebra.ofId R (AdicCompletion I R))
        (by
          change I ^ k ≤
            ((I.map (algebraMap R (AdicCompletion I R))) ^ k).comap
              (algebraMap R (AdicCompletion I R))
          rw [← Ideal.map_pow (algebraMap R (AdicCompletion I R)) I k]
          exact Ideal.le_comap_map) := by
  exact quotientPowAlgEquivOfKernel_symm_toAlgHom I k
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k)

/-- The positive-power and fixed-stage coefficient comparisons agree wherever both
finite-generation hypotheses are available. -/
theorem quotientPowAlgEquivOfFGPow_eq (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) (h : (I ^ k).FG) :
    quotientPowAlgEquivOfFGPow I hn hI k = quotientPowAlgEquiv I k h :=
  rfl

/-- The coefficient comparisons commute with the algebra projections between
ideal-power quotients. -/
theorem quotientPowAlgEquivOfFGPow_factor (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) {j k : ℕ} (hjk : j ≤ k)
    (z : AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ k) :
    quotientPowAlgEquivOfFGPow I hn hI j
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hjk) z) =
      Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hjk)
        (quotientPowAlgEquivOfFGPow I hn hI k z) := by
  exact quotientPowAlgEquivOfKernel_factor I hjk
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI j)
    (pow_smul_top_eq_ker_eval_of_fg_pos_pow hn hI k) z

/-- The coefficient comparison agrees with the original-ring-linear module comparison
through the explicit class-preserving ideal/submodule quotient identifications. -/
theorem quotientPowAlgEquivOfFGPow_toLinearEquiv (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ)
    (z : AdicCompletion I R ⧸ (I ^ k • (⊤ : Submodule R (AdicCompletion I R)))) :
    (quotientPowAlgEquivOfFGPow I hn hI k).toLinearEquiv
        (((Submodule.quotEquivOfEq _ _ (show
            (I ^ k • (⊤ : Submodule R (AdicCompletion I R))) =
              ((I.map (algebraMap R (AdicCompletion I R))) ^ k).restrictScalars R by
            rw [← Ideal.map_pow, ← Ideal.smul_top_eq_map])).trans
          (Submodule.Quotient.restrictScalarsEquiv R
            ((I.map (algebraMap R (AdicCompletion I R))) ^ k))) z) =
      Submodule.quotEquivOfEq _ _ (show (I ^ k • ⊤ : Ideal R) = I ^ k by
        rw [Ideal.smul_eq_mul, Ideal.mul_top])
          (quotientPowLinearEquivOfFGPow I R hn hI k z) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  simp only [Submodule.mkQ_apply, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    Submodule.Quotient.restrictScalarsEquiv_mk, AlgEquiv.toLinearEquiv_apply,
    quotientPowLinearEquivOfFGPow_mk]
  change quotientPowAlgEquivOfFGPow I hn hI k
      (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ k) x) = _
  rw [quotientPowAlgEquivOfFGPow_mk]
  have htop : (I ^ k • ⊤ : Ideal R) = I ^ k := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  rw [← factor_eval_eq_evalₐ I x htop.le]
  obtain ⟨r, hr⟩ := Submodule.mkQ_surjective (I ^ k • (⊤ : Submodule R R)) (eval I R k x)
  rw [← hr]
  rfl

/-- Evaluation identifies each quotient of the completed coefficient ring by a power
of the extended ideal with the corresponding original quotient, when the original
cotangent module is finite. -/
noncomputable def quotientPowAlgEquivOfFiniteCotangent
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent] (n : ℕ) :
    (AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n) ≃ₐ[R]
      R ⧸ I ^ n :=
  private_decl% (quotientPowAlgEquivOfKernel I n
    (pow_smul_top_eq_ker_eval_of_finite_cotangent I R n))

/-- The forward and inverse coefficient quotient maps are inverse. -/
instance instRingHomInvPairQuotientPowAlgEquivOfFiniteCotangent
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent] (n : ℕ) :
    RingHomInvPair
      (quotientPowAlgEquivOfFiniteCotangent I n).toRingEquiv.toRingHom
      (quotientPowAlgEquivOfFiniteCotangent I n).toRingEquiv.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (quotientPowAlgEquivOfFiniteCotangent I n).toRingEquiv

/-- The inverse and forward coefficient quotient maps are inverse. -/
instance instRingHomInvPairQuotientPowAlgEquivOfFiniteCotangentSymm
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent] (n : ℕ) :
    RingHomInvPair
      (quotientPowAlgEquivOfFiniteCotangent I n).toRingEquiv.symm.toRingHom
      (quotientPowAlgEquivOfFiniteCotangent I n).toRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (quotientPowAlgEquivOfFiniteCotangent I n).toRingEquiv

/-- The coefficient comparison sends a completed representative to its evaluation. -/
@[simp]
theorem quotientPowAlgEquivOfFiniteCotangent_mk
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent]
    (n : ℕ) (x : AdicCompletion I R) :
    quotientPowAlgEquivOfFiniteCotangent I n
        (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n) x) =
      evalₐ I n x :=
  quotientPowAlgEquiv_mk_of_kernel I n
    (pow_smul_top_eq_ker_eval_of_finite_cotangent I R n) x

/-- The inverse coefficient comparison is induced by the canonical algebra map. -/
@[simp]
theorem quotientPowAlgEquivOfFiniteCotangent_symm_mk
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent]
    (n : ℕ) (r : R) :
    (quotientPowAlgEquivOfFiniteCotangent I n).symm (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n)
        (algebraMap R (AdicCompletion I R) r) :=
  quotientPowAlgEquivOfKernel_symm_mk I n
    (pow_smul_top_eq_ker_eval_of_finite_cotangent I R n) r

/-- Evaluation identifies each quotient of the completed module by a power of the
extended ideal with the corresponding original quotient, semilinearly over the
canonical coefficient quotient equivalence and with the quotient coefficient actions. -/
noncomputable def quotientPowSemilinearEquivOfFiniteCotangent
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent]
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    @LinearEquiv
      (AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n)
      (R ⧸ I ^ n)
      inferInstance inferInstance
      (quotientPowAlgEquivOfFiniteCotangent I n).toRingEquiv.toRingHom
      (quotientPowAlgEquivOfFiniteCotangent I n).toRingEquiv.symm.toRingHom
      (instRingHomInvPairQuotientPowAlgEquivOfFiniteCotangent I n)
      (instRingHomInvPairQuotientPowAlgEquivOfFiniteCotangentSymm I n)
      (AdicCompletion I M ⧸
        ((I.map (algebraMap R (AdicCompletion I R))) ^ n •
          (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I M))))
      (M ⧸ (I ^ n • (⊤ : Submodule R M)))
      inferInstance inferInstance
      inferInstance inferInstance := private_decl% (by
  refine
    { ((restrictScalarsLevelEquiv (S := AdicCompletion I R) I
        (AdicCompletion I M) n).trans
        (quotientPowLinearEquivOfKernel I M n
          (pow_smul_top_eq_ker_eval_of_finite_cotangent I M n))).toAddEquiv with
      map_smul' := ?_ }
  intro a z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  simp only [Submodule.mkQ_apply]
  rw [Module.Quotient.mk_smul_mk]
  change quotientPowLinearEquivOfKernel I M n
      (pow_smul_top_eq_ker_eval_of_finite_cotangent I M n)
      (restrictScalarsLevelEquiv (S := AdicCompletion I R) I
        (AdicCompletion I M) n (Submodule.Quotient.mk (a • x))) =
    quotientPowAlgEquivOfFiniteCotangent I n
        (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n) a) •
      quotientPowLinearEquivOfKernel I M n
        (pow_smul_top_eq_ker_eval_of_finite_cotangent I M n)
        (restrictScalarsLevelEquiv (S := AdicCompletion I R) I
          (AdicCompletion I M) n (Submodule.Quotient.mk x))
  have h := (evalₛₗ I M n).map_smulₛₗ a x
  simp only [evalₛₗ_apply] at h
  simpa only [restrictScalarsLevelEquiv_mk, quotientPowLinearEquivOfKernel_mk,
    quotientPowAlgEquivOfFiniteCotangent_mk,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h)

/-- The module comparison sends a completed representative to its evaluation. -/
@[simp]
theorem quotientPowSemilinearEquivOfFiniteCotangent_mk
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent]
    (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (x : AdicCompletion I M) :
    quotientPowSemilinearEquivOfFiniteCotangent I M n (Submodule.Quotient.mk x) =
      eval I M n x := by
  change quotientPowLinearEquivOfKernel I M n
      (pow_smul_top_eq_ker_eval_of_finite_cotangent I M n)
      (restrictScalarsLevelEquiv (S := AdicCompletion I R) I
        (AdicCompletion I M) n (Submodule.Quotient.mk x)) = _
  rw [restrictScalarsLevelEquiv_mk, quotientPowLinearEquivOfKernel_mk]

/-- The inverse module comparison is induced by the canonical original map. -/
@[simp]
theorem quotientPowSemilinearEquivOfFiniteCotangent_symm_mk
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent]
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) (m : M) :
    (quotientPowSemilinearEquivOfFiniteCotangent I M n).symm
        (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (of I M m) := by
  change (restrictScalarsLevelEquiv (S := AdicCompletion I R) I
      (AdicCompletion I M) n).symm
      ((quotientPowLinearEquivOfKernel I M n
        (pow_smul_top_eq_ker_eval_of_finite_cotangent I M n)).symm
          (Submodule.Quotient.mk m)) = _
  rw [quotientPowLinearEquivOfKernel_symm_mk, restrictScalarsLevelEquiv_symm_mk]

/-- The coefficient comparisons commute with precision reduction. -/
theorem quotientPowAlgEquivOfFiniteCotangent_factor
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent]
    {m n : ℕ} (hmn : m ≤ n)
    (z : AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n) :
    quotientPowAlgEquivOfFiniteCotangent I m
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn) z) =
      Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)
        (quotientPowAlgEquivOfFiniteCotangent I n z) :=
  quotientPowAlgEquivOfKernel_factor I hmn
    (pow_smul_top_eq_ker_eval_of_finite_cotangent I R m)
    (pow_smul_top_eq_ker_eval_of_finite_cotangent I R n) z

/-- The module comparisons commute with the precision transitions on quotient modules. -/
theorem quotientPowSemilinearEquivOfFiniteCotangent_transitionMap
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent]
    (M : Type v) [AddCommGroup M] [Module R M]
    {m n : ℕ} (hmn : m ≤ n)
    (z : AdicCompletion I M ⧸
      ((I.map (algebraMap R (AdicCompletion I R))) ^ n •
        (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I M)))) :
    quotientPowSemilinearEquivOfFiniteCotangent I M m
        (transitionMap (I.map (algebraMap R (AdicCompletion I R)))
          (AdicCompletion I M) hmn z) =
      transitionMap I M hmn (quotientPowSemilinearEquivOfFiniteCotangent I M n z) := by
  change quotientPowLinearEquivOfKernel I M m
      (pow_smul_top_eq_ker_eval_of_finite_cotangent I M m)
      (restrictScalarsLevelEquiv (S := AdicCompletion I R) I (AdicCompletion I M) m
        (transitionMap (I.map (algebraMap R (AdicCompletion I R)))
          (AdicCompletion I M) hmn z)) =
    transitionMap I M hmn
      (quotientPowLinearEquivOfKernel I M n
        (pow_smul_top_eq_ker_eval_of_finite_cotangent I M n)
        (restrictScalarsLevelEquiv (S := AdicCompletion I R) I (AdicCompletion I M) n z))
  rw [restrictScalarsLevelEquiv_transitionMap]
  exact quotientPowLinearEquivOfKernel_transitionMap I M hmn
    (pow_smul_top_eq_ker_eval_of_finite_cotangent I M m)
    (pow_smul_top_eq_ker_eval_of_finite_cotangent I M n) _

/-- The module comparisons are natural in original-ring-linear maps. -/
theorem quotientPowSemilinearEquivOfFiniteCotangent_natural
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent]
    (M : Type v) [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (n : ℕ) (f : M →ₗ[R] N)
    (z : AdicCompletion I M ⧸
      ((I.map (algebraMap R (AdicCompletion I R))) ^ n •
        (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I M)))) :
    quotientPowSemilinearEquivOfFiniteCotangent I N n
        ((map I f).reduceModIdeal
          ((I.map (algebraMap R (AdicCompletion I R))) ^ n) z) =
      f.reduceModIdeal (I ^ n)
        (quotientPowSemilinearEquivOfFiniteCotangent I M n z) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  simpa only [LinearMap.restrictScalars_apply, LinearMap.reduceModIdeal_apply,
    Submodule.mkQ_apply, quotientPowSemilinearEquivOfFiniteCotangent_mk,
    quotientPowLinearEquivOfKernel_mk] using
    quotientPowLinearEquivOfKernel_natural I M n
      (pow_smul_top_eq_ker_eval_of_finite_cotangent I M n)
      (pow_smul_top_eq_ker_eval_of_finite_cotangent I N n) f (Submodule.Quotient.mk x)

/-- The finite-cotangent and fixed-stage finite-generation coefficient comparisons agree. -/
theorem quotientPowAlgEquivOfFiniteCotangent_eq_quotientPowAlgEquiv
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent]
    (n : ℕ) (h : (I ^ n).FG) :
    quotientPowAlgEquivOfFiniteCotangent I n = quotientPowAlgEquiv I n h := by
  apply AlgEquiv.ext
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [quotientPowAlgEquivOfFiniteCotangent_mk, quotientPowAlgEquiv_mk]

/-- The finite-cotangent and positive-power finite-generation coefficient comparisons agree. -/
theorem quotientPowAlgEquivOfFiniteCotangent_eq_quotientPowAlgEquivOfFGPow
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) :
    quotientPowAlgEquivOfFiniteCotangent I k = quotientPowAlgEquivOfFGPow I hn hI k := by
  apply AlgEquiv.ext
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [quotientPowAlgEquivOfFiniteCotangent_mk, quotientPowAlgEquivOfFGPow_mk]

/-- The semilinear comparison retains the old module comparison, after the canonical
class-preserving restriction-of-scalars comparison of its source quotient. -/
theorem quotientPowSemilinearEquivOfFiniteCotangent_toAddEquiv_eq
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent]
    (M : Type v) [AddCommGroup M] [Module R M]
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) (k : ℕ) :
    (quotientPowSemilinearEquivOfFiniteCotangent I M k).toAddEquiv =
      ((restrictScalarsLevelEquiv (S := AdicCompletion I R) I
          (AdicCompletion I M) k).trans
        (quotientPowLinearEquivOfFGPow I M hn hI k)).toAddEquiv := by
  apply AddEquiv.ext
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  change quotientPowSemilinearEquivOfFiniteCotangent I M k (Submodule.Quotient.mk x) =
    quotientPowLinearEquivOfFGPow I M hn hI k
      (restrictScalarsLevelEquiv (S := AdicCompletion I R) I
        (AdicCompletion I M) k (Submodule.Quotient.mk x))
  rw [quotientPowSemilinearEquivOfFiniteCotangent_mk, restrictScalarsLevelEquiv_mk,
    quotientPowLinearEquivOfFGPow_mk]

/-- Maps from the original module with scalars reduced modulo `I ^ n` extend uniquely
to the completed quotient over its canonical coefficient comparison. -/
theorem quotientPowSemilinearEquivOfFiniteCotangent_existsUnique
    (I : Ideal R) [Module.Finite (R ⧸ I) I.Cotangent]
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ)
    (P : Type w) [AddCommMonoid P] [Module (R ⧸ I ^ n) P]
    (f : M →ₛₗ[Ideal.Quotient.mk (I ^ n)] P) :
    ∃! g :
      (AdicCompletion I M ⧸
        ((I.map (algebraMap R (AdicCompletion I R))) ^ n •
          (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I M)))) →ₛₗ[
            (quotientPowAlgEquivOfFiniteCotangent I n).toRingEquiv.toRingHom] P,
      ∀ m : M, g (Submodule.Quotient.mk (of I M m)) = f m := by
  have hkill : I ^ n • (⊤ : Submodule R M) ≤ LinearMap.ker f := by
    refine Submodule.smul_le.mpr ?_
    intro r hr m _
    change f (r • m) = 0
    have hr0 : Ideal.Quotient.mk (I ^ n) r = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hr
    rw [f.map_smulₛₗ, hr0, zero_smul]
  -- Bundle the original quotient projection with its quotient coefficient map.
  let π : M →ₛₗ[Ideal.Quotient.mk (I ^ n)]
      (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
    { toFun := (I ^ n • (⊤ : Submodule R M)).mkQ
      map_add' := (I ^ n • (⊤ : Submodule R M)).mkQ.map_add
      map_smul' := fun r m =>
        (Module.Quotient.mk_smul_mk (R := R) (M := M) (I := I ^ n) r m).symm }
  have hπ : Function.Surjective π :=
    (I ^ n • (⊤ : Submodule R M)).mkQ_surjective
  have hπker : π.ker = I ^ n • (⊤ : Submodule R M) := by
    apply SetLike.ext
    intro m
    change (Submodule.Quotient.mk m : M ⧸ (I ^ n • (⊤ : Submodule R M))) = 0 ↔
      m ∈ I ^ n • (⊤ : Submodule R M)
    exact Submodule.Quotient.mk_eq_zero _
  let l : (M ⧸ (I ^ n • (⊤ : Submodule R M))) →ₗ[R ⧸ I ^ n] P :=
    π.liftOfSurjective (τ := RingHom.id (R ⧸ I ^ n)) hπ f (hπker.le.trans hkill)
  have hl (m : M) : l (Submodule.Quotient.mk m) = f m :=
    π.liftOfSurjective_apply (τ := RingHom.id (R ⧸ I ^ n))
      hπ f (hπker.le.trans hkill) m
  let g :
      (AdicCompletion I M ⧸
        ((I.map (algebraMap R (AdicCompletion I R))) ^ n •
          (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I M)))) →ₛₗ[
            (quotientPowAlgEquivOfFiniteCotangent I n).toRingEquiv.toRingHom] P :=
    l.comp (quotientPowSemilinearEquivOfFiniteCotangent I M n).toLinearMap
  have hg (m : M) : g (Submodule.Quotient.mk (of I M m)) = f m := by
    change l (quotientPowSemilinearEquivOfFiniteCotangent I M n
      (Submodule.Quotient.mk (of I M m))) = f m
    rw [quotientPowSemilinearEquivOfFiniteCotangent_mk, eval_of]
    exact hl m
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  apply LinearMap.ext
  intro z
  obtain ⟨q, rfl⟩ := (quotientPowSemilinearEquivOfFiniteCotangent I M n).symm.surjective z
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ q
  simp only [Submodule.mkQ_apply]
  rw [quotientPowSemilinearEquivOfFiniteCotangent_symm_mk]
  exact (hg' m).trans (hg m).symm

/-- The original quotient is a retract of base change along evaluation; flatness,
projectivity and finite presentation descend. The scalar dictionaries stay local. -/
private theorem quotient_flat_projective_retract (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    (Module.Flat (AdicCompletion I R) (AdicCompletion I M) →
      Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M)))) ∧
    (Module.Projective (AdicCompletion I R) (AdicCompletion I M) →
      Module.Projective (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M)))) ∧
    (Module.FinitePresentation (AdicCompletion I R) (AdicCompletion I M) →
      Module.FinitePresentation (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M)))) := by
  let S := AdicCompletion I R
  let H := AdicCompletion I M
  let A := R ⧸ I ^ n
  let Q := M ⧸ (I ^ n • (⊤ : Submodule R M))
  let : Algebra S A := (evalₐ I n).toRingHom.toAlgebra
  let : IsScalarTower R S A := IsScalarTower.of_algHom (evalₐ I n)
  let : IsScalarTower R A Q :=
    (Module.isTorsionBySet_quotient_ideal_smul M (I ^ n)).isScalarTower
  let : Module S Q := Module.restrictScalars S A Q
  let : IsScalarTower S A Q := IsScalarTower.restrictScalars S A Q
  -- Evaluation is S-linear for precisely the action induced by evalₐ.
  let e : H →ₗ[S] Q :=
    { (eval I M n).toAddMonoidHom with
      map_smul' := fun s x => (evalₛₗ I M n).map_smulₛₗ s x }
  let T := A ⊗[S] H
  let f : M →ₗ[R] T :=
    ((TensorProduct.mk S A H 1).restrictScalars R).comp (of I M)
  let c : (A ⊗[R] M) ≃ₗ[A] Q :=
    (TensorProduct.quotTensorEquivQuotSMul M (I ^ n)).extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap R A))
  let α : Q →ₗ[A] T := (f.liftBaseChange A).comp c.symm.toLinearMap
  let β : T →ₗ[A] Q := e.liftBaseChange A
  have hsplit : β.comp α = LinearMap.id := by
    apply LinearMap.ext
    intro q
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
      (I ^ n • (⊤ : Submodule R M)) q
    change e.liftBaseChange A
      (f.liftBaseChange A (c.symm (Submodule.Quotient.mk m))) = _
    rw [show c.symm (Submodule.Quotient.mk m) = (1 : A) ⊗ₜ[R] m from
      TensorProduct.quotTensorEquivQuotSMul_symm_mk (I ^ n) m]
    rw [LinearMap.liftBaseChange_one_tmul]
    change e.liftBaseChange A ((1 : A) ⊗ₜ[S] of I M m) = _
    rw [LinearMap.liftBaseChange_one_tmul]
    exact eval_of I M n m
  refine ⟨?_, ?_, ?_⟩
  · intro h
    let : Module.Flat S H := h
    let : Module.Flat A T := Module.Flat.baseChange S A H
    exact Module.Flat.of_retract α β hsplit
  · intro h
    let : Module.Projective S H := h
    let : Module.Projective A T := inferInstance
    exact Module.Projective.of_split α β hsplit
  · intro h
    let : Module.FinitePresentation S H := h
    let : Module.FinitePresentation A T := inferInstance
    apply Module.finitePresentation_of_surjective β
    · intro q
      exact ⟨α q, LinearMap.congr_fun hsplit q⟩
    · rw [LinearMap.ker_eq_range_of_comp_eq_id hsplit]
      exact Submodule.fg_range _

/-- Flatness of the raw completion over its completed coefficient ring implies
flatness of every original ideal-power quotient over its coefficient quotient. -/
theorem moduleFlat_quotient_of_flat_completion
    {R : Type uR} [CommRing R] (I : Ideal R)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Flat (AdicCompletion I R) (AdicCompletion I M)] (n : ℕ) :
    Module.Flat (R ⧸ I ^ n)
      (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
  (quotient_flat_projective_retract I M n).1 inferInstance

/-- Projectivity of the raw completion over its completed coefficient ring implies
projectivity of every original ideal-power quotient over its coefficient quotient. -/
theorem moduleProjective_quotient_of_projective_completion
    {R : Type uR} [CommRing R] (I : Ideal R)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Projective (AdicCompletion I R) (AdicCompletion I M)] (n : ℕ) :
    Module.Projective (R ⧸ I ^ n)
      (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
  (quotient_flat_projective_retract I M n).2.1 inferInstance

/-- Finite presentation of the raw completion over its canonical completed ring descends
to every original ideal-power quotient, including degree zero, for an arbitrary ideal.
No finite generation of any ideal power, or finiteness or completeness of the original
module, is required. -/
theorem moduleFinitePresentation_quotient_of_finitePresentation_completion
    {R : Type uR} [CommRing R] (I : Ideal R)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.FinitePresentation (AdicCompletion I R) (AdicCompletion I M)]
    (n : ℕ) :
    Module.FinitePresentation (R ⧸ I ^ n)
      (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
  (quotient_flat_projective_retract I M n).2.2 inferInstance

end AdicCompletion
