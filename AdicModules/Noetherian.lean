/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Quotient
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Noetherian.Basic
public import GradedRings.ReesModule
import AdicModules.LinearAlgebra.Quotient.Noetherian
import AdicModules.AdicCompletion.Completeness
import AdicModules.AdicCompletion.LinearMap
import CoherentModules.RingTheory.Noetherian
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Over
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.SplitIfs

/-!
# Noetherian modules and adic completions

An adically complete commutative ring is Noetherian if its ideal of definition is
finitely generated and its quotient by that ideal is Noetherian. Applying this
criterion to the adic completion gives the corresponding result without requiring
the original ring to be complete or Noetherian. A Noetherian module is separated for any
ideal contained in the Jacobson radical of its annihilator; this follows by applying
Mathlib's Krull separation theorem over the quotient by the annihilator.

For every ideal, a Noetherian original module has Noetherian raw completion over the
canonical completed coefficient ring: its original second quotient is Noetherian.
Neither the original coefficient ring nor any of its ideal-power quotients needs to be
Noetherian.

The coefficient-reconstruction theorem `Submodule.fg_of_adic_approximation` applies
to a separated decreasing filtration on an arbitrary module. Its successive
corrections use original-ring coefficients; their limits lie in the adic completion
of the coefficient ring. Only compatibility of the completed coefficient action
with the filtration is required, not completeness of the target module.
Applied to the kernels of the canonical semilinear evaluations, it gives finite
generation of submodules of an arbitrary module's adic completion from successive
approximations.

For an arbitrary original module, its raw completion is Noetherian over the
completed coefficient ring exactly when its original second quotient is Noetherian
over the original ring. Equivalently, any chosen original quotient of precision
at least two is Noetherian over its canonical quotient coefficient ring.
No finite generation of the ideal or original module, Noetherianity of either
coefficient ring, completeness or separation is required. Sufficiency first uses
the original-quotient criterion to obtain a finite acted coefficient ideal, then
the associated graded module's Noetherianity and the single finite-leading argument.
Noetherianity of the associated graded module also suffices on its own.

Necessity descends to every original ideal-power quotient, including degree zero.

A raw completed module that is Noetherian over the completed coefficient ring is
intrinsically complete for the original ideal action, and every original ideal-power
submodule is an evaluation kernel. No Noetherianity of the completed ring is required.
The proof descends Noetherianity to the original second quotient, restricts its canonical
quotient-ring action, and applies the finite-generation criterion for the original first layer.
Consequently every original linear map to an intrinsically complete target has a unique
extension from this source completion, given by `AdicCompletion.extend`. The target
needs no action of the completed coefficient ring.

## References

* Mathlib's `RingTheory/AdicCompletion/Noetherian.lean`, by Andrew Yang, supplies
  Krull separation over a Noetherian ring. The module generalization also uses
  `RingTheory/Noetherian/Basic.lean`, by Mario Carneiro, Kevin Buzzard and
  María Inés de Frutos-Fernández; `LinearAlgebra/Isomorphisms.lean`, by
  Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury Kudryashov; and the
  canonical quotient-annihilator action from Pierre-Alexandre Bazin's
  `Algebra/Module/Torsion/Basic.lean`.
* `CoherentModules.RingTheory.Noetherian` supplies Noetherianity of the scalar
  ring modulo a Noetherian module's annihilator and Noetherian descent along
  surjective semilinear maps. Scalar restriction uses Mathlib's bijective-semilinear
  Noetherian equivalence.
* `GradedRings.ReesModule` supplies the original associated graded module, its
  coefficient and representative laws, and Noetherianity from finite acted
  coefficient covers. The coefficient extraction uses Andrew Yang's
  `PolynomialModule.smul_single_apply` from Mathlib.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5.
-/

@[expose] public section

universe u v w z

variable {R : Type u} [CommRing R]

namespace AdicCompletion

/-- If a completed module is Noetherian over the completed coefficient ring, every
original ideal-power quotient is Noetherian over the corresponding quotient ring
with its canonical action, including degree zero. -/
theorem isNoetherian_quotient_pow
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [IsNoetherian (AdicCompletion I R) (AdicCompletion I M)] (n : ℕ) :
    IsNoetherian (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
  isNoetherian_of_surjective_semilinear
    (evalₛₗ I M n) (evalₛₗ_surjective I M n)

private theorem fg_first_layer_of_isNoetherian
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [IsNoetherian (AdicCompletion I R) (AdicCompletion I M)] :
    ((I • (⊤ : Submodule R M)).map
      (I ^ 2 • (⊤ : Submodule R M)).mkQ).FG := by
  let Q := M ⧸ (I ^ 2 • (⊤ : Submodule R M))
  let B := R ⧸ I ^ 2
  have : IsNoetherian B Q := isNoetherian_quotient_pow I M 2
  have : RingHomSurjective (algebraMap R B) := ⟨Ideal.Quotient.mk_surjective⟩
  let e : Q →ₛₗ[algebraMap R B] Q :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => (IsScalarTower.algebraMap_smul B r x).symm }
  have : IsNoetherian R Q :=
    (LinearMap.isNoetherian_iff_of_bijective e Function.bijective_id).mpr inferInstance
  exact IsNoetherian.noetherian _

/-- If a completed module is Noetherian over the completed coefficient ring, all its
original ideal-power submodules are evaluation kernels, including degree zero.
The completed coefficient ring need not itself be Noetherian. -/
theorem pow_smul_top_eq_ker_eval_of_isNoetherian
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [IsNoetherian (AdicCompletion I R) (AdicCompletion I M)] (n : ℕ) :
    I ^ n • (⊤ : Submodule R (AdicCompletion I M)) = (eval I M n).ker :=
  pow_smul_top_eq_ker_eval_of_fg_first_layer I M
    (fg_first_layer_of_isNoetherian I M) n

/-- Every linear map to an adically complete target extends uniquely from the original
module when the source completion is Noetherian over the completed coefficient ring.
The extension is `AdicCompletion.extend`; the target needs no completed-ring action. -/
theorem existsUnique_extension_of_isNoetherian
    (I : Ideal R) {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] [IsAdicComplete I N]
    [IsNoetherian (AdicCompletion I R) (AdicCompletion I M)] (f : M →ₗ[R] N) :
    ∃! F : AdicCompletion I M →ₗ[R] N, F.comp (of I M) = f := by
  let hM := pow_smul_top_eq_ker_eval_of_isNoetherian I M
  let E := precompOfLinearEquivOfKernel I (N := N) hM
  refine ⟨E.symm f, ?_, ?_⟩
  · rw [show E.symm f = extend I f from precompOfLinearEquivOfKernel_symm_apply I hM f]
    exact extend_comp_of I f
  · intro F hF
    apply E.injective
    calc
      E F = f := (precompOfLinearEquivOfKernel_apply I hM F).trans hF
      _ = E (E.symm f) := (E.apply_symm_apply f).symm

/-- A completed module that is Noetherian over the completed coefficient ring is
intrinsically complete for the original ideal action. No Noetherianity or completeness
of either coefficient ring, finiteness or completeness of the original module,
or finite generation of the ideal is required. -/
theorem isAdicComplete_of_isNoetherian
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [IsNoetherian (AdicCompletion I R) (AdicCompletion I M)] :
    IsAdicComplete I (AdicCompletion I M) :=
  isAdicComplete_of_pow_smul_top_eq_ker_eval I M
    (pow_smul_top_eq_ker_eval_of_isNoetherian I M)

end AdicCompletion

/-- A Noetherian module is adically separated when the ideal lies in the Jacobson
radical of its annihilator. This generalizes Mathlib's Noetherian-ring finite-module
Krull separation theorem by passing to the quotient by the annihilator. -/
theorem IsHausdorff.of_le_jacobson_annihilator
    {A : Type u} [CommRing A] (K : Ideal A)
    (X : Type v) [AddCommGroup X] [Module A X] [IsNoetherian A X]
    (hK : K ≤ Ideal.jacobson (Module.annihilator A X)) : IsHausdorff K X := by
  let B := A ⧸ Module.annihilator A X
  let : Module B X := Module.quotientAnnihilator
  let : IsScalarTower A B X := (Module.isTorsionBySet_annihilator A X).isScalarTower
  have : IsNoetherianRing B := isNoetherianRing_quotient_annihilator X
  have : Module.Finite B X := Module.Finite.of_restrictScalars_finite A B X
  have hKB : K.map (algebraMap A B) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    change K ≤ Ideal.comap (Ideal.Quotient.mk (Module.annihilator A X)) _
    rw [Ideal.comap_jacobson_of_surjective (Ideal.Quotient.mk_surjective),
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact hK
  exact IsHausdorff.map_algebraMap_iff.mp (IsHausdorff.of_le_jacobson _ X hKB)

private theorem completion_quotient_isNoetherianRing (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] :
    IsNoetherianRing
      (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R))) := by
  have e :=
    (AdicCompletion.quotientPowAlgEquiv I 1 (by simpa only [pow_one] using hI)).toRingEquiv
  rw [pow_one, pow_one] at e
  exact isNoetherianRing_of_ringEquiv (R ⧸ I) e.symm

section Reconstruction

open scoped BigOperators

variable (I : Ideal R) {T : Type w} [Semiring T]
  {V : Type z} [AddCommGroup V] [Module T V] {ι : Type v} [Fintype ι]

/-- A submodule is finitely generated if a fixed finite family gives successive
approximations with original-ring coefficients of increasing adic order.

The filtration is decreasing and separated, and every completed coefficient with
zero evaluation at level `q` acts into `F q`. The coefficient limits are constructed
in `AdicCompletion I R`; no completeness of `T` or `V`, closedness of `N`, finite
generation of `I`, or filtration-degree condition on the generators is required. -/
theorem Submodule.fg_of_adic_approximation
    (σ : AdicCompletion I R →+* T) (F : ℕ → Submodule T V)
    (hF : Antitone F) (hsep : (⨅ q, F q) = ⊥)
    (haction : ∀ (q : ℕ) (a : AdicCompletion I R),
      AdicCompletion.evalₐ I q a = 0 → ∀ y : V, σ a • y ∈ F q)
    (N : Submodule T V) (g : ι → V) (d : ι → ℕ)
    (hg : ∀ i, g i ∈ N)
    (happrox : ∀ (m : ℕ) {x : V}, x ∈ N → x ∈ F m →
      ∃ c : ι → R, (∀ i, c i ∈ I ^ (m - d i)) ∧
        x - ∑ i, σ (AdicCompletion.of I R (c i)) • g i ∈ F (m + 1)) : N.FG := by
  classical
  -- Use additive action maps, so the target coefficient semiring needs no subtraction.
  let act (y : V) : AdicCompletion I R →+ V :=
    ((smulAddHom T V).flip y).comp σ.toAddMonoidHom
  let f (y : V) : R →+ V := (act y).comp (AdicCompletion.of I R).toAddMonoidHom
  have hFzero (y : V) : y ∈ F 0 := by
    have h := haction 0 1 (by
      rw [map_one]
      change Ideal.Quotient.mk (I ^ 0) (1 : R) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simp) y
    simpa only [map_one, one_smul] using h
  refine ⟨Finset.univ.image g, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hg i
  · intro x hx
    have hchoose : ∀ (m : ℕ) (y : V), ∃ c : ι → R,
        y ∈ N → y ∈ F m →
          (∀ i, c i ∈ I ^ (m - d i)) ∧
            y - ∑ i, f (g i) (c i) ∈ F (m + 1) := by
      intro m y
      by_cases hyN : y ∈ N
      · by_cases hyF : y ∈ F m
        · obtain ⟨c, hc⟩ := happrox m hyN hyF
          exact ⟨c, fun _ _ => hc⟩
        · exact ⟨0, fun _ hy => (hyF hy).elim⟩
      · exact ⟨0, fun hy _ => (hyN hy).elim⟩
    choose c hc using hchoose
    let a : ℕ → ι → R := Nat.rec (fun _ => 0)
      (fun m b i => b i + c m (x - ∑ j, f (g j) (b j)) i)
    have hresN (b : ι → R) : x - ∑ i, f (g i) (b i) ∈ N := by
      -- Negative corrections still come from the original coefficient ring.
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      refine N.add_mem hx ?_
      apply N.sum_mem
      intro i _
      rw [← map_neg (f (g i)) (b i)]
      change σ (AdicCompletion.of I R (-b i)) • g i ∈ N
      exact N.smul_mem _ (hg i)
    have hres (m : ℕ) : x - ∑ i, f (g i) (a m i) ∈ F m := by
      induction m with
      | zero =>
        change x - ∑ i, f (g i) (0 : R) ∈ F 0
        simpa only [map_zero, Finset.sum_const_zero, sub_zero] using hFzero x
      | succ m ih =>
        change x - ∑ i, f (g i) (a m i + c m (x - ∑ j, f (g j) (a m j)) i) ∈
          F (m + 1)
        simpa only [map_add, Finset.sum_add_distrib, sub_sub] using
          (hc m (x - ∑ j, f (g j) (a m j)) (hresN (a m)) ih).2
    have hstep (m : ℕ) (i : ι) : a (m + 1) i - a m i ∈ I ^ (m - d i) := by
      change a m i + c m (x - ∑ j, f (g j) (a m j)) i - a m i ∈ I ^ (m - d i)
      simpa only [add_sub_cancel_left] using
        (hc m (x - ∑ j, f (g j) (a m j)) (hresN (a m)) (hres m)).1 i
    let D := Finset.univ.sup d
    have hd (i : ι) : d i ≤ D := Finset.le_sup (Finset.mem_univ i)
    -- Shifting by the largest degree makes all coefficient sequences adic Cauchy.
    have htail (q m n : ℕ) (hm : q + D ≤ m) (hmn : m ≤ n) (i : ι) :
        a n i - a m i ∈ I ^ q := by
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have hn : q ≤ n - d i := by
          have hsum : q + d i ≤ n :=
            (Nat.add_le_add_left (hd i) q).trans (hm.trans hmn)
          simpa only [Nat.add_sub_cancel] using Nat.sub_le_sub_right hsum (d i)
        have hs : a (n + 1) i - a n i ∈ I ^ q :=
          Ideal.pow_le_pow_right hn (hstep n i)
        convert (I ^ q).add_mem hs ih using 1
        ring
    have hcauchy (i : ι) : ∀ {m n : ℕ}, m ≤ n →
        a (m + D) i ≡ a (n + D) i [SMOD (I ^ m • ⊤ : Submodule R R)] := by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      simpa only [neg_sub] using (I ^ m).neg_mem
        (htail m (m + D) (n + D) le_rfl (Nat.add_le_add_right hmn D) i)
    let s (i : ι) : AdicCompletion.AdicCauchySequence I R :=
      AdicCompletion.AdicCauchySequence.mk I R (fun n => a (n + D) i)
        (fun n => hcauchy i (Nat.le_succ n))
    let l (i : ι) : AdicCompletion I R := AdicCompletion.mk I R (s i)
    have hl (i : ι) (n : ℕ) :
        AdicCompletion.evalₐ I n (l i) = Ideal.Quotient.mk (I ^ n) (a (n + D) i) :=
      AdicCompletion.evalₐ_mk I n (s i)
    have herr (n : ℕ) : x - ∑ i, act (g i) (l i) ∈ F n := by
      have hr : x - ∑ i, f (g i) (a (n + D) i) ∈ F n :=
        hF (Nat.le_add_right n D) (hres (n + D))
      have hs : (∑ i, (f (g i) (a (n + D) i) - act (g i) (l i))) ∈ F n := by
        apply (F n).sum_mem
        intro i _
        have hk : AdicCompletion.evalₐ I n
            (AdicCompletion.of I R (a (n + D) i) - l i) = 0 := by
          simp only [map_sub, AdicCompletion.evalₐ_of, hl, sub_self]
        have ht := haction n _ hk (g i)
        change act (g i) (AdicCompletion.of I R (a (n + D) i) - l i) ∈ F n at ht
        change act (g i) (AdicCompletion.of I R (a (n + D) i)) -
          act (g i) (l i) ∈ F n
        simpa only [map_sub] using ht
      convert (F n).add_mem hr hs using 1
      simp only [Finset.sum_sub_distrib]
      abel
    have hzero : x - ∑ i, act (g i) (l i) = 0 := by
      have hmem : x - ∑ i, act (g i) (l i) ∈ ⨅ n, F n :=
        (Submodule.mem_iInf F).mpr herr
      simpa only [hsep, Submodule.mem_bot] using hmem
    rw [sub_eq_zero.mp hzero]
    apply Submodule.sum_mem
    intro i _
    have hi : g i ∈ Submodule.span T (↑(Finset.univ.image g) : Set V) :=
      Submodule.subset_span (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    exact Submodule.smul_mem _ (σ (l i)) hi

variable [IsAdicComplete I R] (K : Ideal R)

private theorem ideal_fg_of_adic_approximation
    (g : ι → R) (d : ι → ℕ)
    (hg : ∀ i, g i ∈ K)
    (happrox : ∀ (m : ℕ) {x : R}, x ∈ K → x ∈ I ^ m →
      ∃ c : ι → R, (∀ i, c i ∈ I ^ (m - d i)) ∧
        x - ∑ i, c i * g i ∈ I ^ (m + 1)) : K.FG := by
  let σ : AdicCompletion I R →+* R :=
    (AdicCompletion.ofAlgEquiv I).symm.toRingEquiv.toRingHom
  refine Submodule.fg_of_adic_approximation I σ (fun q => (I ^ q : Submodule R R))
    (fun _ _ h => Ideal.pow_le_pow_right h) ?_ ?_ K g d hg ?_
  · simpa only [smul_eq_mul, Ideal.mul_top] using
      IsHausdorff.iInf_pow_smul (I := I) (M := R) inferInstance
  · intro q a ha y
    have hmem : σ a ∈ I ^ q := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change Ideal.Quotient.mk (I ^ q) ((AdicCompletion.ofAlgEquiv I).symm a) = 0
      rw [AdicCompletion.mk_ofAlgEquiv_symm]
      exact ha
    exact (I ^ q).mul_mem_right y hmem
  · intro m x hxK hxI
    obtain ⟨c, hc, hr⟩ := happrox m hxK hxI
    refine ⟨c, hc, ?_⟩
    change x - ∑ i, (AdicCompletion.ofAlgEquiv I).symm
      (AdicCompletion.of I R (c i)) * g i ∈ I ^ (m + 1)
    simpa only [AdicCompletion.ofAlgEquiv_symm_of] using hr

end Reconstruction

section CompletionApproximation

open scoped BigOperators

variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
  {ι : Type w} [Fintype ι]

/-- A submodule of an adic completion is finitely generated over the completed
coefficient ring if a fixed finite family gives successive approximations with
original-ring coefficients of increasing adic order.

The approximation condition is expressed through the canonical semilinear evaluations.
No finite generation of `I`, completeness, separation or finiteness of the original
module, closedness of the submodule, or filtration-degree condition on the generators
is required. -/
theorem AdicCompletion.fg_of_eval_approximation
    (N : Submodule (AdicCompletion I R) (AdicCompletion I M))
    (g : ι → AdicCompletion I M) (d : ι → ℕ)
    (hg : ∀ i, g i ∈ N)
    (happrox : ∀ (m : ℕ) {x : AdicCompletion I M}, x ∈ N →
      AdicCompletion.evalₛₗ I M m x = 0 →
      ∃ c : ι → R, (∀ i, c i ∈ I ^ (m - d i)) ∧
        AdicCompletion.evalₛₗ I M (m + 1)
          (x - ∑ i, AdicCompletion.of I R (c i) • g i) = 0) : N.FG := by
  refine Submodule.fg_of_adic_approximation I
    (RingHom.id (AdicCompletion I R))
    (fun q => LinearMap.ker (AdicCompletion.evalₛₗ I M q))
    ?_ ?_ ?_ N g d hg ?_
  · intro m n hmn x hx
    apply LinearMap.mem_ker.mpr
    have hx0 : AdicCompletion.evalₛₗ I M n x = 0 := LinearMap.mem_ker.mp hx
    calc
      AdicCompletion.evalₛₗ I M m x =
          AdicCompletion.transitionMap I M hmn (AdicCompletion.evalₛₗ I M n x) :=
        (AdicCompletion.transitionMap_evalₛₗ I M hmn x).symm
      _ = 0 := by
        rw [hx0]
        exact (AdicCompletion.transitionMap I M hmn).map_zero
  · refine le_antisymm ?_ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    apply AdicCompletion.ext
    intro q
    have hxq : AdicCompletion.evalₛₗ I M q x = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hx q)
    simpa only [AdicCompletion.evalₛₗ_apply, AdicCompletion.eval_apply,
      AdicCompletion.val_zero_apply] using hxq
  · intro q a ha x
    apply LinearMap.mem_ker.mpr
    calc
      AdicCompletion.evalₛₗ I M q ((RingHom.id (AdicCompletion I R)) a • x) =
          AdicCompletion.evalₐ I q a • AdicCompletion.evalₛₗ I M q x :=
        (AdicCompletion.evalₛₗ I M q).map_smulₛₗ a x
      _ = 0 := by rw [ha, zero_smul]
  · intro m x hx hxq
    obtain ⟨c, hc, hres⟩ := happrox m hx (LinearMap.mem_ker.mp hxq)
    exact ⟨c, hc, LinearMap.mem_ker.mpr hres⟩

end CompletionApproximation

section LeadingGenerators

open Polynomial
open scoped BigOperators

variable (I : Ideal R)

private theorem isNoetherianRing_rees_quotient (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] :
    IsNoetherianRing ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) := by
  have : Algebra.FiniteType R (reesAlgebra I) :=
    (Subalgebra.fg_iff_finiteType _).mp (reesAlgebra.fg hI)
  have : Algebra.FiniteType (R ⧸ I)
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ I) _
  exact Algebra.FiniteType.isNoetherianRing (R ⧸ I)
    ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I)))

private theorem exists_pow_representative
    (M : Type v) [AddCommGroup M] [Module R M] (m : ℕ)
    (x : AdicCompletion I M) (hx : AdicCompletion.eval I M m x = 0) :
    ∃ a : M, a ∈ I ^ m • (⊤ : Submodule R M) ∧
      (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ a =
        AdicCompletion.eval I M (m + 1) x := by
  let e := AdicCompletion.powQuotientEquivKerEvalQuotient I M (Nat.le_succ m)
  let y : (AdicCompletion.eval I M m).ker := ⟨x, hx⟩
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective _ (e.symm (Submodule.Quotient.mk y))
  have h := LinearMap.congr_fun
    (AdicCompletion.mapQ_comp_powQuotientEquivKerEvalQuotient_symm I M
      (Nat.le_succ m)) y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply] at h
  rw [← ha] at h
  exact ⟨a, a.property, h⟩

private theorem exists_adic_generators
    (M : Type v) [AddCommGroup M] [Module R M]
    [IsNoetherian
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I)))
      (Ideal.AssociatedGradedModule I M)]
    (N : Submodule (AdicCompletion I R) (AdicCompletion I M)) :
    ∃ (k : ℕ) (g : Fin k → AdicCompletion I M) (d : Fin k → ℕ),
      (∀ i, g i ∈ N) ∧
      ∀ (m : ℕ) {x : AdicCompletion I M}, x ∈ N →
        AdicCompletion.evalₛₗ I M m x = 0 →
        ∃ c : Fin k → R, (∀ i, c i ∈ I ^ (m - d i)) ∧
          AdicCompletion.evalₛₗ I M (m + 1)
            (x - ∑ i, AdicCompletion.of I R (c i) • g i) = 0 := by
  classical
  let B := reesAlgebra I
  let P : Ideal B := I.map (algebraMap R B)
  let C := B ⧸ P
  let G := Ideal.AssociatedGradedModule I M
  let L := (I.stableFiltration (⊤ : Submodule R M)).submodule
  let single (d : ℕ) (a : M) (ha : a ∈ I ^ d • (⊤ : Submodule R M)) : L :=
    ⟨PolynomialModule.single R d a, Ideal.AssociatedGradedModule.single_mem I M d a ha⟩
  -- Select a finite subset of homogeneous classes, retaining their raw witnesses.
  let T : Set G := {z | ∃ (d : ℕ) (x : AdicCompletion I M) (a : M)
      (ha : a ∈ I ^ d • (⊤ : Submodule R M)),
    x ∈ N ∧ AdicCompletion.eval I M d x = 0 ∧
      (I ^ (d + 1) • (⊤ : Submodule R M)).mkQ a =
        AdicCompletion.eval I M (d + 1) x ∧
      Ideal.AssociatedGradedModule.mk I M (single d a ha) = z}
  obtain ⟨s, hsT, hs⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset T).mp
      (IsNoetherian.noetherian (Submodule.span C T))
  let k := Fintype.card s
  let e : Fin k ≃ s := (Fintype.equivFin s).symm
  let q : Fin k → G := fun i => (e i).val
  have hqrange : Set.range q = (s : Set G) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hz
      refine ⟨e.symm ⟨z, hz⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)
  have hselected (i : Fin k) :
      ∃ (di : ℕ) (gi : AdicCompletion I M) (ai : M)
        (hi : ai ∈ I ^ di • (⊤ : Submodule R M)),
      gi ∈ N ∧ AdicCompletion.eval I M di gi = 0 ∧
        (I ^ (di + 1) • (⊤ : Submodule R M)).mkQ ai =
          AdicCompletion.eval I M (di + 1) gi ∧
        Ideal.AssociatedGradedModule.mk I M (single di ai hi) = q i :=
    hsT (e i).property
  choose d g a ha hgN hgF hga hclass using hselected
  refine ⟨k, g, d, hgN, ?_⟩
  intro m x hxN hxF
  obtain ⟨ax, hax, haxval⟩ := exists_pow_representative I M m x hxF
  let z : G := Ideal.AssociatedGradedModule.mk I M (single m ax hax)
  have hz : z ∈ Submodule.span C (Set.range q) := by
    rw [hqrange, ← hs]
    exact Submodule.subset_span
      (show z ∈ T from ⟨m, x, ax, hax, hxN, hxF, haxval, rfl⟩)
  obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun C).mp hz
  have hlift (i : Fin k) : ∃ b : B, Ideal.Quotient.mk P b = v i :=
    Ideal.Quotient.mk_surjective (v i)
  choose b hb using hlift
  let c : Fin k → R := fun i =>
    if d i ≤ m then (b i : R[X]).coeff (m - d i) else 0
  have hc (i : Fin k) : c i ∈ I ^ (m - d i) := by
    dsimp [c]
    split_ifs with hi
    · exact (b i).property (m - d i)
    · exact Ideal.zero_mem _
  have hcoeff (i : Fin k) :
      Ideal.AssociatedGradedModule.coefficient I M m (v i • q i) =
        (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ (c i • a i) := by
    rw [← hb i, ← hclass i, Ideal.AssociatedGradedModule.quotient_smul_mk]
    rw [Ideal.AssociatedGradedModule.mk_apply,
      Ideal.AssociatedGradedModule.coefficient_mk]
    change Submodule.Quotient.mk
      (((b i : R[X]) • PolynomialModule.single R (d i) (a i)).coeff m) = _
    rw [PolynomialModule.smul_single_apply]
    by_cases hi : d i ≤ m
    · simp only [hi, ↓reduceIte, c, Submodule.mkQ_apply]
    · simp only [hi, ↓reduceIte, c, zero_smul, Submodule.mkQ_apply]
  have horig : (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ ax =
      ∑ i, (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ (c i • a i) := by
    have h := congrArg (Ideal.AssociatedGradedModule.coefficient I M m) hv
    simpa only [map_sum, hcoeff, z, Ideal.AssociatedGradedModule.mk_apply,
      Ideal.AssociatedGradedModule.coefficient_mk, single, PolynomialModule.coeff_single,
      Finsupp.single_eq_same, Submodule.mkQ_apply] using h.symm
  have hraw (i : Fin k) :
      AdicCompletion.eval I M (m + 1) (AdicCompletion.of I R (c i) • g i) =
        (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ (c i • a i) := by
    by_cases hi : d i ≤ m
    · have hscalar : AdicCompletion.of I R (c i) ∈
          (AdicCompletion.eval I R (m - d i)).ker := by
        rw [LinearMap.mem_ker, AdicCompletion.eval_of]
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hc i
      have herror : g i - AdicCompletion.of I M (a i) ∈
          (AdicCompletion.eval I M (d i + 1)).ker := by
        rw [LinearMap.mem_ker, map_sub, AdicCompletion.eval_of, hga i, sub_self]
      -- Each generator agrees with its original representative at its own next precision.
      have hprod := AdicCompletion.smul_mem_ker_eval_add I M hscalar herror
      have hzero : AdicCompletion.eval I M (m + 1)
          (AdicCompletion.of I R (c i) • (g i - AdicCompletion.of I M (a i))) = 0 := by
        have hdeg : m - d i + (d i + 1) = m + 1 := by
          rw [← Nat.add_assoc, Nat.sub_add_cancel hi]
        exact Eq.mp (congrArg (fun n => AdicCompletion.eval I M n
          (AdicCompletion.of I R (c i) • (g i - AdicCompletion.of I M (a i))) = 0)
          hdeg) (LinearMap.mem_ker.mp hprod)
      rw [smul_sub, map_sub, sub_eq_zero] at hzero
      exact hzero
    · simp only [c, hi, ↓reduceIte, map_zero, zero_smul]
  refine ⟨c, hc, ?_⟩
  rw [AdicCompletion.evalₛₗ_apply, map_sub, map_sum, sub_eq_zero]
  calc
    AdicCompletion.eval I M (m + 1) x =
        (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ ax := haxval.symm
    _ = ∑ i, (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ (c i • a i) := horig
    _ = ∑ i, AdicCompletion.eval I M (m + 1)
        (AdicCompletion.of I R (c i) • g i) :=
      Finset.sum_congr rfl fun i _ => (hraw i).symm

end LeadingGenerators

variable (I : Ideal R)

/-- Noetherianity of the associated graded module implies Noetherianity of the raw
completion over the completed coefficient ring. No finiteness, separation or completeness
of the original module, or Noetherianity of either coefficient ring, is required.
This is the module form of the adic Noetherian criterion of Fujiwara–Kato,
*Foundations of Rigid Geometry I*. -/
theorem AdicCompletion.isNoetherian_of_associatedGradedModule
    (M : Type v) [AddCommGroup M] [Module R M]
    [IsNoetherian
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I)))
      (Ideal.AssociatedGradedModule I M)] :
    IsNoetherian (AdicCompletion I R) (AdicCompletion I M) := by
  constructor
  intro N
  obtain ⟨k, g, d, hg, happrox⟩ := exists_adic_generators I M N
  exact AdicCompletion.fg_of_eval_approximation I M N g d hg happrox

namespace AdicCompletion

private theorem isNoetherian_associatedGradedModule_of_quotient_sq
    {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [IsNoetherian R (M ⧸ (I ^ 2 • (⊤ : Submodule R M)))] :
    IsNoetherian
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I)))
      (Ideal.AssociatedGradedModule I M) := by
  have hdata :=
    (Submodule.isNoetherian_quotient_pow_smul_top_iff I M (n := 2)
      (by decide : 2 ≤ (2 : ℕ))).mp
      (inferInstance : IsNoetherian R (M ⧸ (I ^ 2 • (⊤ : Submodule R M))))
  have : IsNoetherian R (M ⧸ (I • (⊤ : Submodule R M))) := hdata.1
  obtain ⟨J, hJ, hJI, hacted⟩ :=
    Ideal.exists_fg_subideal_smul_sup_eq_of_fg_map_mkQ I
      (I ^ 2 • (⊤ : Submodule R M)) hdata.2
  have hsq : I ^ 2 • (⊤ : Submodule R M) ≤ I • (⊤ : Submodule R M) :=
    Submodule.smul_mono_left (Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0))
  rw [sup_eq_left.mpr hsq] at hacted
  exact Ideal.AssociatedGradedModule.isNoetherian_of_fg_of_pow_smul_sup
    I M J hJI hJ (fun n =>
      (Submodule.pow_smul_sup_next_eq_of_smul_sup_sq_eq
        I J (⊤ : Submodule R M) hacted n).symm)


/-- Noetherianity of the raw completion over completed coefficients is detected by
the original second quotient, as a module over the original ring. No finiteness,
Noetherian coefficient ring, completeness or separation hypothesis is required.
This is the module form of the adic Noetherian criterion of Fujiwara–Kato,
*Foundations of Rigid Geometry I*. -/
theorem isNoetherian_iff_quotient_sq
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsNoetherian (AdicCompletion I R) (AdicCompletion I M) ↔
      IsNoetherian R (M ⧸ (I ^ 2 • (⊤ : Submodule R M))) := by
  constructor
  · intro h
    have := h
    have hQ := isNoetherian_quotient_pow I M 2
    have : RingHomSurjective (Ideal.Quotient.mk (I ^ 2)) :=
      ⟨Ideal.Quotient.mk_surjective⟩
    exact (LinearMap.isNoetherian_iff_of_bijective
      (Module.isTorsionBySet_quotient_ideal_smul M (I ^ 2)).semilinearMap
      Function.bijective_id).mpr hQ
  · intro h
    have := h
    have := isNoetherian_associatedGradedModule_of_quotient_sq I M
    exact isNoetherian_of_associatedGradedModule I M

/-- Each original quotient at precision at least two detects Noetherianity of the
raw completion over completed coefficients, using the canonical quotient-ring action.
No higher-quotient Noetherianity hypothesis is imposed. The lower bound excludes
the zero quotient at precision zero and the insufficient first quotient.
This is the module form of the adic Noetherian criterion of Fujiwara–Kato,
*Foundations of Rigid Geometry I*. -/
theorem isNoetherian_iff_quotient_pow
    (M : Type v) [AddCommGroup M] [Module R M] {n : ℕ} (hn : 2 ≤ n) :
    IsNoetherian (AdicCompletion I R) (AdicCompletion I M) ↔
      IsNoetherian (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M))) := by
  constructor
  · intro h
    have := h
    exact isNoetherian_quotient_pow I M n
  · intro h
    have : RingHomSurjective (Ideal.Quotient.mk (I ^ n)) :=
      ⟨Ideal.Quotient.mk_surjective⟩
    have hQ := (LinearMap.isNoetherian_iff_of_bijective
      (Module.isTorsionBySet_quotient_ideal_smul M (I ^ n)).semilinearMap
      Function.bijective_id).mpr h
    apply (isNoetherian_iff_quotient_sq I M).mpr
    exact (Submodule.isNoetherian_quotient_pow_smul_top_iff I M
      (by decide : 2 ≤ (2 : ℕ))).mpr
      ((Submodule.isNoetherian_quotient_pow_smul_top_iff I M hn).mp hQ)

end AdicCompletion

/-- The adic completion at a finitely generated ideal is Noetherian when the first
quotient is Noetherian, with no completeness or Noetherianity assumption on the original
ring. This is the completion application of the criterion in Fujiwara–Kato,
*Foundations of Rigid Geometry I*. -/
theorem AdicCompletion.isNoetherianRing_of_fg
    (hI : I.FG) [IsNoetherianRing (R ⧸ I)] :
    IsNoetherianRing (AdicCompletion I R) := by
  have : IsNoetherianRing
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) :=
    isNoetherianRing_rees_quotient I hI
  have : Module.Finite R (R ⧸ (I • (⊤ : Submodule R R))) := inferInstance
  have : Module.Finite (R ⧸ I) (R ⧸ (I • (⊤ : Submodule R R))) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ I) _
  have := Ideal.AssociatedGradedModule.finite_of_finite_quotient I R
  have := AdicCompletion.isNoetherian_of_associatedGradedModule I R
  exact isNoetherianRing_iff.mpr this

/-- An adically complete commutative ring with a finitely generated ideal of definition
and Noetherian first quotient is Noetherian. This is the adic Noetherian criterion of
Fujiwara–Kato, *Foundations of Rigid Geometry I*. -/
theorem IsAdicComplete.isNoetherianRing_of_fg
    [IsAdicComplete I R] (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] : IsNoetherianRing R := by
  have := AdicCompletion.isNoetherianRing_of_fg I hI
  exact isNoetherianRing_of_ringEquiv (AdicCompletion I R)
    (AdicCompletion.ofAlgEquiv I).symm.toRingEquiv

namespace AdicCompletion

/-- The raw adic completion of a Noetherian original module is Noetherian over the
canonical completed coefficient ring. No Noetherianity of the original ring or its
ideal-power quotients, finite generation of the ideal, separation or completeness is
required. This follows from the second-quotient criterion. -/
theorem isNoetherian_of_isNoetherian
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [IsNoetherian R M] :
    IsNoetherian (AdicCompletion I R) (AdicCompletion I M) := by
  exact (isNoetherian_iff_quotient_sq I M).2 inferInstance

end AdicCompletion
