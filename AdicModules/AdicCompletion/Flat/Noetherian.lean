/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import AdicModules.AdicCompletion.Pi
import AdicModules.AdicCompletion.Cotangent
import AdicModules.AdicCompletion.Quotient
import AdicModules.LinearAlgebra.Quotient.Flat
import CoherentModules.RingTheory.Flat.Equiv

/-!
# Flatness of complete modules over a Noetherian ring

An intrinsically adically complete module over a Noetherian ring is flat if all
its positive intrinsic quotients are flat over the corresponding quotient rings.
Neither completeness of the ring nor finite generation of the module is needed.

The proof uses Artin–Rees only on finite free coefficient modules. Flatness of
the quotients gives uniform approximate-kernel estimates. Successive corrections
then prove that finite coefficient-matrix images are closed, and finite generation
of coefficient kernels gives the equational criterion for flatness.

As an application, if `AdicCompletion I R` is Noetherian, then the raw completion
of an arbitrary original `R`-module `M` is flat over it exactly when every positive
original quotient `M / IⁿM` is flat over `R / Iⁿ`. In particular, the raw completion
of a flat original module is flat. No Noetherianity or completeness of `R`, finite
generation of `I` or `M`, or completed-ring action on original `M` is assumed.

## References

The standard mathematical ingredients are Artin–Rees and the equational criterion
for flatness (Stacks Project, Tag 00HK). We use Andrew Yang's formalization of
Artin–Rees, the flatness API of Johan Commelin, Jujian Zhang and Yongle Hu, and
Mitchell Lee and Junyan Xu's equational criterion. Finite-product tensor
coordinates and adic completeness use the formalizations of Judith Ludwig and
Christian Merten and the existing ideal-action and product-completeness APIs.
The raw-completion application combines this criterion with this library's
finite-cotangent completeness and quotient comparisons, and the action-preserving
semilinear flatness transport in `CoherentModules.RingTheory.Flat.Equiv`, by
Formal Frontier Agents.
-/

@[expose] public section

universe uA uN

open TensorProduct LinearMap

variable {A : Type uA} [CommRing A]

private noncomputable def tensorCoordinates
    (N : Type uN) [AddCommGroup N] [Module A N] (d : ℕ) :
    (Fin d → A) ⊗[A] N ≃ₗ[A] (Fin d → N) :=
  (TensorProduct.comm A (Fin d → A) N).trans
    (TensorProduct.piScalarRight A A N (Fin d))

private theorem tensorCoordinates_tmul
    {N : Type uN} [AddCommGroup N] [Module A N]
    {d : ℕ} (a : Fin d → A) (x : N) :
    tensorCoordinates N d (a ⊗ₜ[A] x) = fun i ↦ a i • x := by
  simp [tensorCoordinates]

/-- A coefficient map acting on a finite power, through the finite-Pi tensor
coordinate equivalence. -/
private noncomputable def tensorMap
    (N : Type uN) [AddCommGroup N] [Module A N]
    {p q : ℕ} (f : (Fin p → A) →ₗ[A] (Fin q → A)) :
    (Fin p → N) →ₗ[A] (Fin q → N) :=
  (tensorCoordinates N q).toLinearMap.comp
    ((f.rTensor N).comp (tensorCoordinates N p).symm.toLinearMap)

private theorem tensorMap_coordinates
    {N : Type uN} [AddCommGroup N] [Module A N]
    {p q : ℕ} (f : (Fin p → A) →ₗ[A] (Fin q → A))
    (t : (Fin p → A) ⊗[A] N) :
    tensorMap N f (tensorCoordinates N p t) =
      tensorCoordinates N q (f.rTensor N t) := by
  simp [tensorMap]

private theorem tensorMap_pure
    {N : Type uN} [AddCommGroup N] [Module A N]
    {p q : ℕ} (f : (Fin p → A) →ₗ[A] (Fin q → A))
    (a : Fin p → A) (x : N) :
    tensorMap N f (fun i ↦ a i • x) = fun j ↦ f a j • x := by
  simpa only [tensorCoordinates_tmul, rTensor_tmul] using
    tensorMap_coordinates f (a ⊗ₜ[A] x)

private theorem tensorMap_apply
    {N : Type uN} [AddCommGroup N] [Module A N]
    {p q : ℕ} (f : (Fin p → A) →ₗ[A] (Fin q → A))
    (x : Fin p → N) (j : Fin q) :
    tensorMap N f x j = ∑ i, f (Pi.single i 1) j • x i := by
  classical
  have hx : x = ∑ i, (fun l ↦ (Pi.single i (1 : A) : Fin p → A) l • x i) := by
    ext l
    simp [Pi.single_apply]
  calc
    tensorMap N f x j =
        tensorMap N f (∑ i, (fun l ↦ (Pi.single i (1 : A) : Fin p → A) l • x i)) j :=
      congrArg (fun z ↦ tensorMap N f z j) hx
    _ = ∑ i, f (Pi.single i 1) j • x i := by
      simp only [map_sum, Finset.sum_apply, tensorMap_pure]

private theorem tensorMap_self
    {p q : ℕ} (f : (Fin p → A) →ₗ[A] (Fin q → A)) (a : Fin p → A) :
    tensorMap A f a = f a := by
  simpa only [smul_eq_mul, mul_one] using tensorMap_pure f a (1 : A)

private theorem tensorMap_natural
    {N : Type uN} [AddCommGroup N] [Module A N]
    {M : Type*} [AddCommGroup M] [Module A M]
    {p q : ℕ} (f : (Fin p → A) →ₗ[A] (Fin q → A))
    (h : N →ₗ[A] M) (x : Fin p → N) :
    tensorMap M f (fun i ↦ h (x i)) = fun j ↦ h (tensorMap N f x j) := by
  ext j
  simp only [tensorMap_apply, map_sum, map_smul]

/-- The tensor image of a coefficient submodule; the map need not be injective. -/
private noncomputable def tensorImage
    (N : Type uN) [AddCommGroup N] [Module A N]
    {p : ℕ} (Z : Submodule A (Fin p → A)) : Submodule A (Fin p → N) :=
  LinearMap.range ((tensorCoordinates N p).toLinearMap.comp (Z.subtype.rTensor N))

private theorem tensorImage_ker_le
    {N : Type uN} [AddCommGroup N] [Module A N]
    {p q : ℕ} (f : (Fin p → A) →ₗ[A] (Fin q → A)) :
    tensorImage N f.ker ≤ (tensorMap N f).ker := by
  rintro _ ⟨t, rfl⟩
  change tensorMap N f (tensorCoordinates N p (f.ker.subtype.rTensor N t)) = 0
  rw [tensorMap_coordinates, ← rTensor_comp_apply]
  have hzero : f.comp f.ker.subtype = 0 := by
    apply LinearMap.ext
    intro x
    exact x.property
  simp [hzero]

private theorem tensorImage_range
    {N : Type uN} [AddCommGroup N] [Module A N]
    {r p : ℕ} (g : (Fin r → A) →ₗ[A] (Fin p → A)) :
    tensorImage N g.range = (tensorMap N g).range := by
  unfold tensorImage tensorMap
  rw [LinearMap.range_comp, ← LinearMap.rTensor_range, LinearMap.range_comp,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

/-- Artin–Rees gives one coefficient bound for all precisions. -/
private theorem exists_coefficient_bound [IsNoetherianRing A]
    (K : Ideal A) {p q : ℕ} (f : (Fin p → A) →ₗ[A] (Fin q → A)) :
    ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f (K ^ (n + k) • (⊤ : Submodule A (Fin q → A))) ≤
        f.ker ⊔ K ^ n • (⊤ : Submodule A (Fin p → A)) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul K f.range
  refine ⟨k, fun n d hd ↦ ?_⟩
  have hfd : f d ∈ K ^ n • f.range := by
    have h : f d ∈ K ^ (n + k) • (⊤ : Submodule A (Fin q → A)) ⊓ f.range :=
      ⟨hd, ⟨d, rfl⟩⟩
    rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h
    have hle : K ^ n • (K ^ k • (⊤ : Submodule A (Fin q → A)) ⊓ f.range) ≤
        K ^ n • f.range := smul_mono_right _ inf_le_right
    exact hle h
  have hmap : f d ∈ Submodule.map f (K ^ n • (⊤ : Submodule A (Fin p → A))) := by
    simpa only [Submodule.map_smul'', Submodule.map_top] using hfd
  obtain ⟨e, he, hfe⟩ := hmap
  apply Submodule.mem_sup.mpr
  refine ⟨d - e, ?_, e, he, sub_add_cancel d e⟩
  change f (d - e) = 0
  simp [hfe]

/-- Quotient flatness transfers a coefficient estimate to arbitrary module vectors.
The kernel tensored here is the kernel of the reduced map, not the reduction of
the original coefficient kernel. -/
private theorem approximate_kernel_of_coefficient_bound
    (J U : Ideal A) (hJ : J.FG) (hJU : J ≤ U)
    (N : Type uN) [AddCommGroup N] [Module A N]
    [Module.Flat (A ⧸ J) (N ⧸ (J • (⊤ : Submodule A N)))]
    {p q : ℕ} (f : (Fin p → A) →ₗ[A] (Fin q → A))
    (hcoef : Submodule.comap f (J • (⊤ : Submodule A (Fin q → A))) ≤
      f.ker ⊔ U • (⊤ : Submodule A (Fin p → A)))
    (y : Fin p → N)
    (hy : tensorMap N f y ∈ J • (⊤ : Submodule A (Fin q → N))) :
    y ∈ tensorImage N f.ker ⊔ U • (⊤ : Submodule A (Fin p → N)) := by
  classical
  let B := A ⧸ J
  let Q := N ⧸ (J • (⊤ : Submodule A N))
  let fB : (Fin p → B) →ₗ[B] (Fin q → B) :=
    (tensorMap B f).extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap A B))
  let ρ (d : ℕ) : (Fin d → N) →ₗ[A] (Fin d → Q) :=
    LinearMap.piMap fun _ ↦ (J • (⊤ : Submodule A N)).mkQ
  have hcoeff (a : Fin p → A) :
      fB (fun i ↦ Ideal.Quotient.mk J (a i)) =
        fun j ↦ Ideal.Quotient.mk J (f a j) := by
    change tensorMap B f (fun i ↦ Ideal.Quotient.mk J (a i)) = _
    simpa only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      tensorMap_self] using tensorMap_natural f (Ideal.Quotient.mkₐ A J).toLinearMap a
  have hbasis (i : Fin p) :
      fB (Pi.single i 1) = fun j ↦ Ideal.Quotient.mk J (f (Pi.single i 1) j) := by
    have hsingle :
        (fun l ↦ Ideal.Quotient.mk J ((Pi.single i (1 : A) : Fin p → A) l)) =
          (Pi.single i (1 : B)) := by
      ext l
      simp only [Pi.single_apply, apply_ite, map_one, map_zero]
      split_ifs <;> rfl
    simpa only [hsingle] using hcoeff (Pi.single i 1)
  have hcomm : tensorMap Q fB (ρ p y) = ρ q (tensorMap N f y) := by
    ext j
    change tensorMap Q fB (fun i ↦ (J • (⊤ : Submodule A N)).mkQ (y i)) j =
      (J • (⊤ : Submodule A N)).mkQ (tensorMap N f y j)
    simp only [tensorMap_apply, hbasis]
    change (∑ i, Ideal.Quotient.mk J (f (Pi.single i 1) j) •
        Submodule.Quotient.mk (y i)) =
      (J • (⊤ : Submodule A N)).mkQ (∑ i, f (Pi.single i 1) j • y i)
    simp only [Module.Quotient.mk_smul_mk]
    exact (map_sum (J • (⊤ : Submodule A N)).mkQ _ _).symm
  have hzero : ρ q (tensorMap N f y) = 0 := by
    change tensorMap N f y ∈ LinearMap.ker (ρ q)
    rw [show LinearMap.ker (ρ q) = J • (⊤ : Submodule A (Fin q → N)) from
      hJ.ker_piMap_mkQ (fun _ : Fin q ↦ N)]
    exact hy
  let t := (tensorCoordinates (A := B) Q p).symm (ρ p y)
  have ht : fB.rTensor Q t = 0 := by
    apply (tensorCoordinates (A := B) Q q).injective
    rw [map_zero, ← tensorMap_coordinates]
    simpa only [t, LinearEquiv.apply_symm_apply, hcomm] using hzero
  obtain ⟨s, hs⟩ :=
    (Module.Flat.rTensor_exact Q (LinearMap.exact_subtype_ker_map fB) t).mp ht
  let T := tensorImage N f.ker ⊔ U • (⊤ : Submodule A (Fin p → N))
  have hlift (s : fB.ker ⊗[B] Q) :
      ∃ w : Fin p → N, w ∈ T ∧
        ρ p w = tensorCoordinates (A := B) Q p (fB.ker.subtype.rTensor Q s) := by
    induction s with
    | tmul l ν =>
      choose d hd using fun i ↦ Ideal.Quotient.mk_surjective (l.val i)
      obtain ⟨v, hv⟩ := (J • (⊤ : Submodule A N)).mkQ_surjective ν
      have hfd : f d ∈ J • (⊤ : Submodule A (Fin q → A)) := by
        have hpi : J • (⊤ : Submodule A (Fin q → A)) =
            Submodule.pi Set.univ (fun _ : Fin q ↦ J • (⊤ : Submodule A A)) := by
          simpa only [Submodule.pi_top] using
            hJ.smul_pi (fun _ : Fin q ↦ (⊤ : Submodule A A))
        rw [hpi]
        intro j _
        change f d j ∈ J • (⊤ : Submodule A A)
        have hred : Ideal.Quotient.mk J (f d j) = 0 := by
          have h := congrFun (hcoeff d) j
          rw [show (fun i ↦ Ideal.Quotient.mk J (d i)) = l.val from funext hd] at h
          exact h.symm.trans (congrFun l.property j)
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
        exact Ideal.Quotient.eq_zero_iff_mem.mp hred
      obtain ⟨z, hz, e, he, hze⟩ := Submodule.mem_sup.mp (hcoef hfd)
      let w : Fin p → N := fun i ↦ d i • v
      have hzN : (fun i ↦ z i • v) ∈ tensorImage N f.ker := by
        refine ⟨(⟨z, hz⟩ : f.ker) ⊗ₜ[A] v, ?_⟩
        change tensorCoordinates N p
          (f.ker.subtype.rTensor N ((⟨z, hz⟩ : f.ker) ⊗ₜ[A] v)) = _
        rw [rTensor_tmul]
        exact tensorCoordinates_tmul z v
      have heN : (fun i ↦ e i • v) ∈ U • (⊤ : Submodule A (Fin p → N)) :=
        (Submodule.smul_top_le_comap_smul_top U
          (LinearMap.compLeft (LinearMap.toSpanSingleton A N v) (Fin p))) he
      refine ⟨w, ?_, ?_⟩
      · apply Submodule.mem_sup.mpr
        refine ⟨_, hzN, _, heN, ?_⟩
        ext i
        change z i • v + e i • v = d i • v
        rw [← add_smul, ← Pi.add_apply, hze]
      · ext i
        simp only [rTensor_tmul, tensorCoordinates_tmul]
        change Submodule.Quotient.mk (d i • v) = l.val i • ν
        rw [← hd i, ← hv]
        exact (Module.Quotient.mk_smul_mk N (I := J) (d i) v).symm
    | add s t ihs iht =>
      obtain ⟨w, hw, hws⟩ := ihs
      obtain ⟨v, hv, hvt⟩ := iht
      refine ⟨w + v, T.add_mem hw hv, ?_⟩
      simp only [map_add, hws, hvt]
  obtain ⟨w, hw, hws⟩ := hlift s
  have hρ : ρ p w = ρ p y := by
    rw [hws, hs]
    exact (tensorCoordinates (A := B) Q p).apply_symm_apply (ρ p y)
  have herr : y - w ∈ J • (⊤ : Submodule A (Fin p → N)) := by
    rw [← hJ.ker_piMap_mkQ (fun _ : Fin p ↦ N)]
    change ρ p (y - w) = 0
    simp only [map_sub, hρ, sub_self]
  have herrU : y - w ∈ U • (⊤ : Submodule A (Fin p → N)) :=
    (Submodule.smul_mono_left hJU) herr
  have hsum : w + (y - w) ∈ T := T.add_mem hw (Submodule.mem_sup_right herrU)
  convert hsum using 1
  abel

private theorem exists_approximate_kernel_bound [IsNoetherianRing A]
    (K : Ideal A) (N : Type uN) [AddCommGroup N] [Module A N]
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (A ⧸ K ^ n) (N ⧸ (K ^ n • (⊤ : Submodule A N))))
    {p q : ℕ} (f : (Fin p → A) →ₗ[A] (Fin q → A)) :
    ∃ k : ℕ, ∀ n : ℕ, 0 < n → ∀ y : Fin p → N,
      tensorMap N f y ∈ K ^ (n + k) • (⊤ : Submodule A (Fin q → N)) →
        y ∈ tensorImage N f.ker ⊔ K ^ n • (⊤ : Submodule A (Fin p → N)) := by
  obtain ⟨k, hk⟩ := exists_coefficient_bound K f
  refine ⟨k, fun n hn y hy ↦ ?_⟩
  let := hflat (n + k) (by omega)
  exact approximate_kernel_of_coefficient_bound (K ^ (n + k)) (K ^ n)
    (Ideal.fg_of_isNoetherianRing _) (Ideal.pow_le_pow_right (Nat.le_add_right n k))
    N f (hk n) y hy

section ControlledLimits

variable {P : Type*} [AddCommGroup P] [Module A P]
variable {Q : Type*} [AddCommGroup Q] [Module A Q]

/-- The successive-difference form of the intrinsic precompleteness axiom. -/
private theorem exists_limit_of_small_steps (K : Ideal A) [IsPrecomplete K P]
    (z : ℕ → P)
    (hz : ∀ n, z (n + 1) - z n ∈ K ^ n • (⊤ : Submodule A P)) :
    ∃ x : P, ∀ n, x - z n ∈ K ^ n • (⊤ : Submodule A P) := by
  have hc : ∀ {m n : ℕ}, m ≤ n →
      z n - z m ∈ K ^ m • (⊤ : Submodule A P) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have hn : z (n + 1) - z n ∈ K ^ m • (⊤ : Submodule A P) :=
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)) (hz n)
      convert Submodule.add_mem _ hn ih using 1
      abel
  obtain ⟨x, hx⟩ := IsPrecomplete.prec' (I := K) z (fun {_ _} hmn ↦ by
    exact ((Submodule.Quotient.eq _).mpr (hc hmn)).symm)
  refine ⟨x, fun n ↦ ?_⟩
  exact (Submodule.Quotient.eq _).mp (hx n).symm

/-- A uniform approximate-kernel bound permits each approximation to be corrected
without changing its image. -/
private theorem exists_small_correction (K : Ideal A) (F : P →ₗ[A] Q)
    (k n : ℕ)
    (hbound : ∀ y : P, F y ∈ K ^ (n + k) • (⊤ : Submodule A Q) →
      y ∈ F.ker ⊔ K ^ n • (⊤ : Submodule A P))
    {x : Q} {z w : P}
    (hz : F z - x ∈ K ^ (n + k) • (⊤ : Submodule A Q))
    (hw : F w - x ∈ K ^ (n + 1 + k) • (⊤ : Submodule A Q)) :
    ∃ z' : P,
      (F z' - x ∈ K ^ (n + 1 + k) • (⊤ : Submodule A Q)) ∧
      z' - z ∈ K ^ n • (⊤ : Submodule A P) := by
  have hw' : F w - x ∈ K ^ (n + k) • (⊤ : Submodule A Q) :=
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) hw
  have hdiff : F (w - z) ∈ K ^ (n + k) • (⊤ : Submodule A Q) := by
    rw [map_sub]
    convert Submodule.sub_mem _ hw' hz using 1
    abel
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (hbound (w - z) hdiff)
  have hFu : F u = 0 := hu
  refine ⟨w - u, ?_, ?_⟩
  · simpa only [map_sub, hFu, sub_zero] using hw
  · have heq : w - u - z = v := by
      calc
        w - u - z = (w - z) - u := by abel
        _ = (u + v) - u := by rw [← huv]
        _ = v := by abel
    simpa only [heq] using hv

/-- An explicit successive-correction proof of closedness, assuming the uniform
approximate-kernel estimate. No closed-image principle is assumed. -/
private theorem mem_range_of_approximations
    (K : Ideal A) [IsAdicComplete K P] [IsHausdorff K Q]
    (F : P →ₗ[A] Q) (k : ℕ)
    (hbound : ∀ n : ℕ, 0 < n → ∀ y : P,
      F y ∈ K ^ (n + k) • (⊤ : Submodule A Q) →
        y ∈ F.ker ⊔ K ^ n • (⊤ : Submodule A P))
    (x : Q)
    (hx : ∀ n : ℕ, 0 < n → ∃ z : P,
      F z - x ∈ K ^ n • (⊤ : Submodule A Q)) : x ∈ F.range := by
  classical
  have hnext (n : ℕ)
      (z : {z : P | F z - x ∈ K ^ (n + 1 + k) • (⊤ : Submodule A Q)}) :
      ∃ z' : {z' : P | F z' - x ∈ K ^ (n + 1 + 1 + k) • (⊤ : Submodule A Q)},
        (z' : P) - z ∈ K ^ (n + 1) • (⊤ : Submodule A P) := by
    obtain ⟨w, hw⟩ := hx (n + 1 + 1 + k) (by omega)
    obtain ⟨z', hz', hsmall⟩ := exists_small_correction K F k (n + 1)
      (hbound (n + 1) (by omega)) z.property hw
    exact ⟨⟨z', hz'⟩, hsmall⟩
  let z : (n : ℕ) → {z : P | F z - x ∈ K ^ (n + 1 + k) • (⊤ : Submodule A Q)} :=
    Nat.rec ⟨(hx (1 + k) (by omega)).choose, (hx (1 + k) (by omega)).choose_spec⟩
      (fun n z ↦ (hnext n z).choose)
  have z_succ (n : ℕ) : z (n + 1) = (hnext n (z n)).choose := by
    rfl
  have hz (n : ℕ) : (z (n + 1)).val - (z n).val ∈
      K ^ (n + 1) • (⊤ : Submodule A P) := by
    rw [z_succ n]
    exact (hnext n (z n)).choose_spec
  obtain ⟨l, hl⟩ := exists_limit_of_small_steps K (fun n ↦ (z n).val) (fun n ↦
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))) (hz n))
  refine ⟨l, sub_eq_zero.mp ?_⟩
  apply IsHausdorff.haus' (I := K)
  intro n
  apply (Submodule.Quotient.eq _).mpr
  simp only [sub_zero]
  have hmap : F (l - (z n).val) ∈ K ^ n • (⊤ : Submodule A Q) :=
    (Submodule.smul_top_le_comap_smul_top (K ^ n) F) (hl n)
  have hz' : F (z n).val - x ∈ K ^ n • (⊤ : Submodule A Q) :=
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) (z n).property
  convert Submodule.add_mem _ hmap hz' using 1
  simp only [map_sub]
  abel

end ControlledLimits

/-- A finite generating matrix for the coefficient kernel remains exact on `N`.
Closedness is applied to that generating matrix with its own Artin–Rees bound. -/
private theorem exists_kernel_presentation [IsNoetherianRing A]
    (K : Ideal A) (N : Type uN) [AddCommGroup N] [Module A N]
    [IsAdicComplete K N]
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (A ⧸ K ^ n) (N ⧸ (K ^ n • (⊤ : Submodule A N))))
    {p q : ℕ} (f : (Fin p → A) →ₗ[A] (Fin q → A)) :
    ∃ (r : ℕ) (g : (Fin r → A) →ₗ[A] (Fin p → A)), g.range = f.ker ∧
      ∀ x : Fin p → N, tensorMap N f x = 0 → x ∈ (tensorMap N g).range := by
  classical
  obtain ⟨r, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian f.ker)
  let g := Fintype.linearCombination A b
  have hg : g.range = f.ker := by
    simpa only [g, Fintype.range_linearCombination] using hb
  refine ⟨r, g, hg, fun x hx ↦ ?_⟩
  have hT : tensorImage N f.ker = (tensorMap N g).range := by
    rw [← hg, tensorImage_range]
  obtain ⟨kf, hkf⟩ := exists_approximate_kernel_bound K N hflat f
  obtain ⟨kg, hkg⟩ := exists_approximate_kernel_bound K N hflat g
  let := IsAdicComplete.pi_of_fg K (fun _ : Fin r ↦ N)
    (Ideal.fg_of_isNoetherianRing K)
  have hbound (n : ℕ) (hn : 0 < n) (y : Fin r → N)
      (hy : tensorMap N g y ∈ K ^ (n + kg) • (⊤ : Submodule A (Fin p → N))) :
      y ∈ (tensorMap N g).ker ⊔ K ^ n • (⊤ : Submodule A (Fin r → N)) := by
    have hle : tensorImage N g.ker ⊔ K ^ n • (⊤ : Submodule A (Fin r → N)) ≤
        (tensorMap N g).ker ⊔ K ^ n • (⊤ : Submodule A (Fin r → N)) :=
      sup_le_sup (tensorImage_ker_le (N := N) g) le_rfl
    exact hle (hkg n hn y hy)
  apply mem_range_of_approximations K (tensorMap N g) kg hbound x
  intro n hn
  have hmem := hkf n hn x (by simp only [hx, Submodule.zero_mem])
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hmem
  rw [hT] at hu
  obtain ⟨z, hz⟩ := hu
  refine ⟨z, ?_⟩
  have hdiff : tensorMap N g z - x = -v := by
    rw [hz, ← huv]
    abel
  rw [hdiff]
  exact Submodule.neg_mem _ hv

/-- A complete module over a Noetherian ring is flat if every positive intrinsic
adic quotient is flat over the corresponding quotient ring.

There is no finite-generation assumption on the module or its first quotient,
and the coefficient ring need not be complete. The proof combines Artin–Rees,
uniform approximate relations, successive corrections and the equational
criterion for flatness (Stacks Project, Tag 00HK). -/
theorem Module.Flat.of_isAdicComplete
    {A : Type uA} [CommRing A] [IsNoetherianRing A]
    (K : Ideal A) (N : Type uN) [AddCommGroup N] [Module A N]
    [IsAdicComplete K N]
    (hflat : ∀ n : ℕ, 0 < n → Module.Flat (A ⧸ K ^ n)
      (N ⧸ (K ^ n • (⊤ : Submodule A N)))) : Module.Flat A N := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro p a x hx
  let f : (Fin p → A) →ₗ[A] (Fin 1 → A) :=
    LinearMap.pi fun _ ↦ Fintype.linearCombination A a
  have hf (i : Fin p) (j : Fin 1) : f (Pi.single i 1) j = a i := by
    simp only [f, LinearMap.pi_apply, Fintype.linearCombination_apply_single, one_smul]
  have hfx : tensorMap N f x = 0 := by
    ext j
    simpa only [tensorMap_apply, hf, Pi.zero_apply] using hx
  obtain ⟨r, g, hg, hgen⟩ := exists_kernel_presentation K N hflat f
  obtain ⟨y, hy⟩ := hgen x hfx
  refine ⟨r, (fun i j ↦ g (Pi.single j 1) i), y, fun i ↦ ?_, fun j ↦ ?_⟩
  · simpa only [tensorMap_apply] using (congrFun hy i).symm
  · have hcol : g (Pi.single j 1) ∈ f.ker := by
      rw [← hg]
      exact ⟨Pi.single j 1, rfl⟩
    have hz := congrFun (show f (g (Pi.single j 1)) = 0 from hcol) (0 : Fin 1)
    simpa only [f, LinearMap.pi_apply, Fintype.linearCombination_apply,
      smul_eq_mul, mul_comm, Pi.zero_apply] using hz

universe uR uM

namespace AdicCompletion

/-- Over a Noetherian completed coefficient ring, the raw completion is flat
if and only if every positive original ideal-power quotient is flat over its
corresponding coefficient quotient. -/
theorem moduleFlat_iff_flat_quotient
    {R : Type uR} [CommRing R] (I : Ideal R)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [IsNoetherianRing (AdicCompletion I R)] :
    Module.Flat (AdicCompletion I R) (AdicCompletion I M) ↔
      ∀ n : ℕ, 0 < n → Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M))) := by
  constructor
  · intro hflat n _
    let : Module.Flat (AdicCompletion I R) (AdicCompletion I M) := hflat
    exact moduleFlat_quotient_of_flat_completion I M n
  · intro hflat
    let : Module.Finite (R ⧸ I) I.Cotangent := finite_cotangent_of_isNoetherianRing I
    let : IsAdicComplete (I.map (algebraMap R (AdicCompletion I R)))
        (AdicCompletion I M) := isAdicComplete_map_of_finite_cotangent I M
    apply Module.Flat.of_isAdicComplete
      (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I M)
    intro n hn
    let : Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M))) := hflat n hn
    exact Module.Flat.of_semilinearEquiv
      (quotientPowAlgEquivOfFiniteCotangent I n).toRingEquiv
      (quotientPowSemilinearEquivOfFiniteCotangent I M n)

/-- The raw completion of a flat original module is flat over its completed
coefficient ring when that completed coefficient ring is Noetherian. -/
theorem moduleFlat_of_flat
    {R : Type uR} [CommRing R] (I : Ideal R)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [IsNoetherianRing (AdicCompletion I R)] [Module.Flat R M] :
    Module.Flat (AdicCompletion I R) (AdicCompletion I M) :=
  (moduleFlat_iff_flat_quotient I M).mpr
    (fun n _ ↦ Module.Flat.quotient_smul_top M (I ^ n))

end AdicCompletion
