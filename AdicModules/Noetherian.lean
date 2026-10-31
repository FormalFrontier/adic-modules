/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Quotient
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Noetherian.Basic
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

The coefficient-reconstruction theorem `Submodule.fg_of_adic_approximation` applies
to a separated decreasing filtration on an arbitrary module. Its successive
corrections use original-ring coefficients; their limits lie in the adic completion
of the coefficient ring. Only compatibility of the completed coefficient action
with the filtration is required, not completeness of the target module.
Applied to the kernels of the canonical semilinear evaluations, it gives finite
generation of submodules of an arbitrary module's adic completion from successive
approximations.

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
* `CoherentModules.RingTheory.Noetherian` supplies Noetherian descent along
  surjective semilinear maps. Scalar restriction uses Mathlib's bijective-semilinear
  Noetherian equivalence.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5.
-/

@[expose] public section

universe u v w z

variable {R : Type u} [CommRing R]

namespace AdicCompletion

private theorem fg_first_layer_of_isNoetherian
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [IsNoetherian (AdicCompletion I R) (AdicCompletion I M)] :
    ((I • (⊤ : Submodule R M)).map
      (I ^ 2 • (⊤ : Submodule R M)).mkQ).FG := by
  let Q := M ⧸ (I ^ 2 • (⊤ : Submodule R M))
  let B := R ⧸ I ^ 2
  have : IsNoetherian B Q :=
    isNoetherian_of_surjective_semilinear
      (evalₛₗ I M 2) (evalₛₗ_surjective I M 2)
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

private theorem isNoetherianRing_quotient_annihilator
    {A : Type u} [CommRing A] (X : Type v) [AddCommGroup X] [Module A X]
    [IsNoetherian A X] : IsNoetherianRing (A ⧸ Module.annihilator A X) := by
  let f := LinearMap.lsmul A X
  have : IsNoetherian A (Module.End A X) := isNoetherian_linearMap A X X
  have : IsNoetherian A (LinearMap.range f) :=
    isNoetherian_of_injective (LinearMap.range f).subtype Subtype.val_injective
  have hker : LinearMap.ker f = (Module.annihilator A X : Submodule A A) := by
    ext a
    exact (Module.mem_annihilator_iff_lsmul_eq_zero).symm
  have hquot : IsNoetherian A (A ⧸ Module.annihilator A X) := by
    rw [← hker]
    exact f.quotKerEquivRange.isNoetherian_iff.mpr inferInstance
  exact isNoetherian_of_tower A hquot

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

private theorem coeff_mem_pow_succ_of_mem_rees_map
    {p : reesAlgebra I} (hp : p ∈ I.map (algebraMap R (reesAlgebra I))) (m : ℕ) :
    (p : R[X]).coeff m ∈ I ^ (m + 1) := by
  let ell : reesAlgebra I →ₗ[R] R :=
    (Polynomial.lcoeff R m).comp (reesAlgebra I).val.toLinearMap
  have hle : I • (⊤ : Submodule R (reesAlgebra I)) ≤
      Submodule.comap ell (I ^ (m + 1) : Submodule R R) := by
    refine Submodule.smul_le.mpr ?_
    intro r hr q _
    change ell (r • q) ∈ I ^ (m + 1)
    rw [map_smul, smul_eq_mul]
    change r * (q : R[X]).coeff m ∈ I ^ (m + 1)
    rw [pow_succ']
    exact Ideal.mul_mem_mul hr (q.property m)
  have hp' : p ∈ I • (⊤ : Submodule R (reesAlgebra I)) := by
    rw [Ideal.smul_top_eq_map]
    exact hp
  exact hle hp'

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

private theorem exists_adic_generators (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] (K : Ideal R) :
    ∃ (n : ℕ) (g : Fin n → R) (d : Fin n → ℕ),
      (∀ i, g i ∈ K) ∧
      ∀ (m : ℕ) {x : R}, x ∈ K → x ∈ I ^ m →
        ∃ c : Fin n → R, (∀ i, c i ∈ I ^ (m - d i)) ∧
          x - ∑ i, c i * g i ∈ I ^ (m + 1) := by
  classical
  let A := reesAlgebra I
  let P : Ideal A := I.map (algebraMap R A)
  let G := A ⧸ P
  let pi : A →+* G := Ideal.Quotient.mk P
  have : IsNoetherianRing G := isNoetherianRing_rees_quotient I hI
  -- Keep the original monomial classes, so that each selected generator has a degree.
  let T : Set G := {z | ∃ (d : ℕ) (x : R) (hx : x ∈ I ^ d),
    x ∈ K ∧ pi ⟨monomial d x, reesAlgebra.monomial_mem.mpr hx⟩ = z}
  obtain ⟨s, hsT, hs⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset T).mp
      (IsNoetherian.noetherian (Submodule.span G T))
  let n := Fintype.card s
  let e : Fin n ≃ s := (Fintype.equivFin s).symm
  let q : Fin n → G := fun i => (e i).val
  have hqrange : Set.range q = (s : Set G) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hz
      refine ⟨e.symm ⟨z, hz⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)
  have hselected (i : Fin n) :
      ∃ (di : ℕ) (gi : R) (hi : gi ∈ I ^ di),
        gi ∈ K ∧ pi ⟨monomial di gi, reesAlgebra.monomial_mem.mpr hi⟩ = q i :=
    hsT (e i).property
  choose d g hgI hgK hclass using hselected
  let b : Fin n → A := fun i =>
    ⟨monomial (d i) (g i), reesAlgebra.monomial_mem.mpr (hgI i)⟩
  have hbclass (i : Fin n) : pi (b i) = q i := hclass i
  refine ⟨n, g, d, hgK, ?_⟩
  intro m x hxK hxI
  let a : A := ⟨monomial m x, reesAlgebra.monomial_mem.mpr hxI⟩
  have ha : pi a ∈ Submodule.span G (Set.range q) := by
    rw [hqrange, ← hs]
    exact Submodule.subset_span (show pi a ∈ T from ⟨m, x, hxI, hxK, rfl⟩)
  obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun G).mp ha
  have hlift (i : Fin n) : ∃ p : A, pi p = v i :=
    Ideal.Quotient.mk_surjective (v i)
  choose p hp using hlift
  have hsum : pi (∑ i, p i * b i) = pi a := by
    simpa only [map_sum, map_mul, hp, hbclass, smul_eq_mul] using hv
  have hrel : a - ∑ i, p i * b i ∈ P := Ideal.Quotient.eq.mp hsum.symm
  have hres := coeff_mem_pow_succ_of_mem_rees_map I hrel m
  let c : Fin n → R := fun i =>
    if d i ≤ m then (p i : R[X]).coeff (m - d i) else 0
  refine ⟨c, ?_, ?_⟩
  · intro i
    dsimp [c]
    split_ifs with hi
    · exact (p i).property (m - d i)
    · exact Ideal.zero_mem _
  · have hcoeff (i : Fin n) :
        ((p i : R[X]) * monomial (d i) (g i)).coeff m = c i * g i := by
      by_cases hi : d i ≤ m
      · simp only [c, ite_eq_left hi]
        simpa only [Nat.sub_add_cancel hi] using
          Polynomial.coeff_mul_monomial (p i : R[X]) (d i) (m - d i) (g i)
      · simp only [c, ite_eq_right hi, zero_mul]
        rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc,
          Polynomial.coeff_mul_X_pow', ite_eq_right hi]
    let ell : A →ₗ[R] R :=
      (Polynomial.lcoeff R m).comp (reesAlgebra I).val.toLinearMap
    have heq : ((a - ∑ i, p i * b i : A) : R[X]).coeff m =
        x - ∑ i, c i * g i := by
      change ell (a - ∑ i, p i * b i) = _
      rw [map_sub, map_sum]
      change (monomial m x).coeff m -
        ∑ i, ((p i : R[X]) * monomial (d i) (g i)).coeff m = _
      rw [Polynomial.coeff_monomial_same]
      exact congrArg (fun y : R => x - y)
        (Finset.sum_congr rfl fun i _ => hcoeff i)
    rwa [heq] at hres

end LeadingGenerators

variable (I : Ideal R)

/-- An adically complete commutative ring with a finitely generated ideal of definition
and Noetherian first quotient is Noetherian. This is the adic Noetherian criterion of
Fujiwara–Kato, *Foundations of Rigid Geometry I*. -/
theorem IsAdicComplete.isNoetherianRing_of_fg
    [IsAdicComplete I R] (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] : IsNoetherianRing R := by
  apply (isNoetherianRing_iff_ideal_fg R).mpr
  intro K
  obtain ⟨n, g, d, hg, happrox⟩ := exists_adic_generators I hI K
  exact ideal_fg_of_adic_approximation I K g d hg happrox

/-- The adic completion at a finitely generated ideal is Noetherian when the first
quotient is Noetherian, with no completeness or Noetherianity assumption on the original
ring. This is the completion application of the criterion in Fujiwara–Kato,
*Foundations of Rigid Geometry I*. -/
theorem AdicCompletion.isNoetherianRing_of_fg
    (hI : I.FG) [IsNoetherianRing (R ⧸ I)] :
    IsNoetherianRing (AdicCompletion I R) := by
  have := AdicCompletion.isAdicComplete_self I hI
  have := completion_quotient_isNoetherianRing I hI
  exact IsAdicComplete.isNoetherianRing_of_fg
    (I.map (algebraMap R (AdicCompletion I R))) (hI.map _)
