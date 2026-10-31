/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Quotient
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Over
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.SplitIfs

/-!
# Noetherian modules and adically complete rings

An adically complete commutative ring is Noetherian if its ideal of definition is
finitely generated and its quotient by that ideal is Noetherian. Applying this
criterion to the adic completion gives the corresponding result without requiring
the original ring to be complete or Noetherian. A Noetherian module is separated for any
ideal contained in the Jacobson radical of its annihilator; this follows by applying
Mathlib's Krull separation theorem over the quotient by the annihilator.

## References

* Mathlib's `RingTheory/AdicCompletion/Noetherian.lean`, by Andrew Yang, supplies
  Krull separation over a Noetherian ring. The module generalization also uses
  `RingTheory/Noetherian/Basic.lean`, by Mario Carneiro, Kevin Buzzard and
  María Inés de Frutos-Fernández; `LinearAlgebra/Isomorphisms.lean`, by
  Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury Kudryashov; and the
  canonical quotient-annihilator action from Pierre-Alexandre Bazin's
  `Algebra/Module/Torsion/Basic.lean`.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5.
-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

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

variable (I : Ideal R) [IsAdicComplete I R] (K : Ideal R)
  {ι : Type v} [Fintype ι]

private theorem ideal_fg_of_adic_approximation
    (g : ι → R) (d : ι → ℕ)
    (hg : ∀ i, g i ∈ K)
    (happrox : ∀ (m : ℕ) {x : R}, x ∈ K → x ∈ I ^ m →
      ∃ c : ι → R, (∀ i, c i ∈ I ^ (m - d i)) ∧
        x - ∑ i, c i * g i ∈ I ^ (m + 1)) : K.FG := by
  classical
  refine ⟨Finset.univ.image g, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hg i
  · intro x hx
    have hchoose : ∀ (m : ℕ) (y : R), ∃ c : ι → R,
        y ∈ K → y ∈ I ^ m →
          (∀ i, c i ∈ I ^ (m - d i)) ∧
            y - ∑ i, c i * g i ∈ I ^ (m + 1) := by
      intro m y
      by_cases hyK : y ∈ K
      · by_cases hyI : y ∈ I ^ m
        · obtain ⟨c, hc⟩ := happrox m hyK hyI
          exact ⟨c, fun _ _ => hc⟩
        · exact ⟨0, fun _ hy => (hyI hy).elim⟩
      · exact ⟨0, fun hy _ => (hyK hy).elim⟩
    choose c hc using hchoose
    let a : ℕ → ι → R := Nat.rec (fun _ => 0)
      (fun m b i => b i + c m (x - ∑ j, b j * g j) i)
    have hresK (b : ι → R) : x - ∑ i, b i * g i ∈ K := by
      exact K.sub_mem hx (K.sum_mem fun i _ => K.mul_mem_left _ (hg i))
    have hres (m : ℕ) : x - ∑ i, a m i * g i ∈ I ^ m := by
      induction m with
      | zero => simp
      | succ m ih =>
        change x - ∑ i, (a m i + c m (x - ∑ j, a m j * g j) i) * g i ∈
          I ^ (m + 1)
        simpa only [add_mul, Finset.sum_add_distrib, sub_sub] using
          (hc m (x - ∑ j, a m j * g j) (hresK (a m)) ih).2
    have hstep (m : ℕ) (i : ι) : a (m + 1) i - a m i ∈ I ^ (m - d i) := by
      change a m i + c m (x - ∑ j, a m j * g j) i - a m i ∈ I ^ (m - d i)
      simpa only [add_sub_cancel_left] using
        (hc m (x - ∑ j, a m j * g j) (hresK (a m)) (hres m)).1 i
    let D := Finset.univ.sup d
    have hd (i : ι) : d i ≤ D := Finset.le_sup (Finset.mem_univ i)
    -- After shifting by the largest degree, every coefficient sequence is adic Cauchy.
    have htail (N m n : ℕ) (hm : N + D ≤ m) (hmn : m ≤ n) (i : ι) :
        a n i - a m i ∈ I ^ N := by
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have hn : N ≤ n - d i := by
          have hsum : N + d i ≤ n :=
            (Nat.add_le_add_left (hd i) N).trans (hm.trans hmn)
          simpa only [Nat.add_sub_cancel] using Nat.sub_le_sub_right hsum (d i)
        have hs : a (n + 1) i - a n i ∈ I ^ N :=
          Ideal.pow_le_pow_right hn (hstep n i)
        convert (I ^ N).add_mem hs ih using 1
        ring
    have hcauchy (i : ι) : ∀ {m n : ℕ}, m ≤ n →
        a (m + D) i ≡ a (n + D) i [SMOD (I ^ m • ⊤ : Submodule R R)] := by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      simpa only [neg_sub] using (I ^ m).neg_mem
        (htail m (m + D) (n + D) le_rfl (Nat.add_le_add_right hmn D) i)
    have hlim (i : ι) : ∃ L : R, ∀ n : ℕ,
        a (n + D) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] :=
      IsPrecomplete.prec (I := I) (M := R) inferInstance (hcauchy i)
    choose l hl using hlim
    have herr (n : ℕ) : x - ∑ i, l i * g i ∈ I ^ n := by
      have hr : x - ∑ i, a (n + D) i * g i ∈ I ^ n :=
        Ideal.pow_le_pow_right (Nat.le_add_right n D) (hres (n + D))
      have hs : (∑ i, (a (n + D) i - l i) * g i) ∈ I ^ n := by
        apply (I ^ n).sum_mem
        intro i _
        apply Ideal.mul_mem_right (g i) (I ^ n)
        simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hl i n
      convert (I ^ n).add_mem hr hs using 1
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    have hzero : x - ∑ i, l i * g i = 0 := by
      apply IsHausdorff.haus (I := I) (M := R) inferInstance
      intro n
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, sub_zero] using herr n
    rw [sub_eq_zero.mp hzero]
    apply Submodule.sum_mem
    intro i _
    have hi : g i ∈ Submodule.span R (↑(Finset.univ.image g) : Set R) :=
      Submodule.subset_span (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    simpa only [smul_eq_mul] using Submodule.smul_mem _ (l i) hi

end Reconstruction

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
