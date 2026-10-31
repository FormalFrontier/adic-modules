/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Smooth.Quotient

/-!
# Flat quotient modules and nilpotent isomorphism criteria

A linear map to a flat module is bijective if its reduction modulo a nilpotent
ideal is bijective. Neither module needs to be finitely generated, and the
source need not be flat.

The proof first kills the cokernel by iterating multiplication by the nilpotent
ideal. Reduced injectivity then puts the kernel inside the ideal times the
source. Flatness of the target identifies this intersection with the ideal
times the kernel, so the same nilpotent iteration kills the kernel.

Flatness of an original module descends to the canonical quotient module over
the quotient ring. More generally, for arbitrary original ideals `J,K`, if the
image of `K` in `R/J` is nilpotent and `N/JN` is flat over `R/J`, bijectivity
modulo `K` implies bijectivity modulo `J`. The ideals need not be nested:
quotienting the given equivalence further first gives bijectivity modulo `J ⊔ K`.
The nested factor kernels and additive square then reduce to the nilpotent
flat-target theorem over `R/J`.

## References

The kernel-intersection step uses Nailin Guan's Mathlib theorem
`LinearMap.ker_inf_smul_top_eq_smul_of_flat`. Reduction is Mathlib's
`LinearMap.reduceModIdeal`, formalized by Judith Ludwig and Christian Merten.
The nilpotent iteration is the standard elementary argument, with no
finite-generation form of Nakayama's lemma needed.
Quotient flatness uses Christian Merten's Mathlib flat base-change API,
Antoine Chambert-Loir and Jujian Zhang's quotient–tensor equivalence, and
Kenny Lau and Yury Kudryashov's scalar extension along a surjective algebra map.
Further quotient transport uses the submodule quotient and third isomorphism
APIs by Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury Kudryashov.
-/

@[expose] public section

universe uA uX uY uR uM uN

private theorem submodule_eq_bot_of_le_smul_of_isNilpotent
    {A : Type uA} [CommSemiring A]
    {X : Type uX} [AddCommMonoid X] [Module A X]
    (J : Ideal A) (hJ : IsNilpotent J) (P : Submodule A X)
    (hP : P ≤ J • P) : P = ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  apply Submodule.eq_bot_of_le_smul_of_pow_smul_eq_bot J n P ?_ hP
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul]

/-- A linear map with flat target is bijective if it is bijective modulo a
nilpotent ideal. No finiteness or source-flatness hypothesis is required.

Surjectivity follows by nilpotent iteration on the cokernel. For injectivity,
Mathlib's `LinearMap.ker_inf_smul_top_eq_smul_of_flat`, formalized by Nailin Guan,
identifies the kernel with its ideal multiple, which nilpotence forces to vanish. -/
theorem LinearMap.bijective_of_reduceModIdeal_bijective_of_isNilpotent
    {A : Type uA} [CommRing A]
    {X : Type uX} [AddCommGroup X] [Module A X]
    {Y : Type uY} [AddCommGroup Y] [Module A Y]
    [Module.Flat A Y]
    (J : Ideal A) (hJ : IsNilpotent J) (f : X →ₗ[A] Y)
    (hf : Function.Bijective (f.reduceModIdeal J)) :
    Function.Bijective f := by
  have hsup : f.range ⊔ (J • (⊤ : Submodule A Y)) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨q, hq⟩ := hf.2 (Submodule.Quotient.mk
      (p := J • (⊤ : Submodule A Y)) y)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hy : y - f x ∈ J • (⊤ : Submodule A Y) := by
      apply (Submodule.Quotient.eq _).mp
      simpa only [LinearMap.reduceModIdeal_apply] using hq.symm
    exact Submodule.mem_sup.mpr ⟨f x, f.mem_range_self x, y - f x, hy,
      by rw [add_comm, sub_add_cancel]⟩
  have hquot : J • (⊤ : Submodule A (Y ⧸ f.range)) = ⊤ := by
    simpa only [Submodule.map_sup, Submodule.mkQ_map_self,
      Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ, bot_sup_eq]
      using congrArg (Submodule.map f.range.mkQ) hsup
  have hbot : (⊤ : Submodule A (Y ⧸ f.range)) = ⊥ :=
    submodule_eq_bot_of_le_smul_of_isNilpotent J hJ ⊤ hquot.ge
  have hs : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    intro y _
    apply (Submodule.Quotient.mk_eq_zero f.range).mp
    have hy : (Submodule.Quotient.mk y : Y ⧸ f.range) ∈
        (⊥ : Submodule A (Y ⧸ f.range)) := by
      rw [← hbot]
      exact Submodule.mem_top
    exact (Submodule.mem_bot A).mp hy
  have hk : f.ker ≤ J • (⊤ : Submodule A X) := by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply hf.1
    simp only [LinearMap.reduceModIdeal_apply, LinearMap.mem_ker.mp hx,
      Submodule.Quotient.mk_zero, map_zero]
  have hker : f.ker = ⊥ := by
    apply submodule_eq_bot_of_le_smul_of_isNilpotent J hJ f.ker
    rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat J f hs]
    exact le_inf le_rfl hk
  exact ⟨LinearMap.ker_eq_bot.mp hker, hs⟩

/-- Flatness descends to the original quotient module with its canonical
quotient-ring action, by flat base change and the quotient–tensor equivalence. -/
theorem Module.Flat.quotient_smul_top
    {R : Type uR} [CommRing R]
    (N : Type uN) [AddCommGroup N] [Module R N] [Module.Flat R N]
    (J : Ideal R) :
    Module.Flat (R ⧸ J) (N ⧸ (J • (⊤ : Submodule R N))) := by
  exact Module.Flat.of_linearEquiv
    ((TensorProduct.quotTensorEquivQuotSMul N J).extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap R (R ⧸ J)))).symm

-- Quotient the given equivalence further. All maps here are restricted to R,
-- so no identification of the two quotient coefficient rings is needed.
private theorem LinearMap.bijective_reduceModIdeal_of_le
    {R : Type uR} [CommRing R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    (K L : Ideal R) (hKL : K ≤ L) (f : M →ₗ[R] N)
    (hf : Function.Bijective (f.reduceModIdeal K)) :
    Function.Bijective (f.reduceModIdeal L) := by
  let e := (LinearEquiv.ofBijective (f.reduceModIdeal K) hf).restrictScalars R
  let p : Submodule R M := K • ⊤
  let q : Submodule R N := K • ⊤
  let P : Submodule R M := L • ⊤
  let Q : Submodule R N := L • ⊤
  have he : (P.map p.mkQ).map e.toLinearMap = Q.map q.mkQ := by
    simp only [P, Q, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ,
      LinearEquiv.range]
  let E := (Submodule.quotientQuotientEquivQuotient p P
      (Submodule.smul_mono_left hKL)).symm |>.trans
    ((Submodule.Quotient.equiv (P.map p.mkQ) (Q.map q.mkQ) e he).trans
      (Submodule.quotientQuotientEquivQuotient q Q (Submodule.smul_mono_left hKL)))
  have hE : (E : M ⧸ P → N ⧸ Q) = f.reduceModIdeal L := by
    funext x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  rw [← hE]
  exact E.bijective

/-- If the image of `K` in `R/J` is nilpotent and `N/JN` is flat over `R/J`,
bijectivity modulo `K` implies bijectivity modulo `J`. The ideals need not
contain one another. The nilpotent flat-target criterion is applied over `R/J`. -/
theorem LinearMap.bijective_reduceModIdeal_of_isNilpotent_map
    {R : Type uR} [CommRing R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    (J K : Ideal R)
    [Module.Flat (R ⧸ J) (N ⧸ (J • (⊤ : Submodule R N)))]
    (hK : IsNilpotent (K.map (Ideal.Quotient.mk J)))
    (f : M →ₗ[R] N)
    (hf : Function.Bijective (f.reduceModIdeal K)) :
    Function.Bijective (f.reduceModIdeal J) := by
  let L := J ⊔ K
  have hL : L.map (Ideal.Quotient.mk J) = K.map (Ideal.Quotient.mk J) := by
    simp only [L, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]
  have hfL : Function.Bijective (f.reduceModIdeal L) :=
    f.bijective_reduceModIdeal_of_le K L le_sup_right hf
  apply LinearMap.bijective_of_reduceModIdeal_bijective_of_isNilpotent
    (K.map (Ideal.Quotient.mk J)) hK (f.reduceModIdeal J)
  have hJL : J ≤ L := le_sup_left
  let rM : (M ⧸ (J • (⊤ : Submodule R M))) →ₗ[R]
      M ⧸ (L • (⊤ : Submodule R M)) :=
    Submodule.factor (Submodule.smul_mono_left hJL)
  let rN : (N ⧸ (J • (⊤ : Submodule R N))) →ₗ[R]
      N ⧸ (L • (⊤ : Submodule R N)) :=
    Submodule.factor (Submodule.smul_mono_left hJL)
  have hrM : Function.Surjective rM :=
    Submodule.factor_surjective (Submodule.smul_mono_left hJL)
  have kM (x : M ⧸ (J • (⊤ : Submodule R M))) :
      rM x = 0 ↔ x ∈ K.map (Ideal.Quotient.mk J) •
        (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))) := by
    simpa only [rM, hL] using
      Submodule.factor_eq_zero_iff_mem_map_smul_top J L hJL x
  have kN (y : N ⧸ (J • (⊤ : Submodule R N))) :
      rN y = 0 ↔ y ∈ K.map (Ideal.Quotient.mk J) •
        (⊤ : Submodule (R ⧸ J) (N ⧸ (J • (⊤ : Submodule R N)))) := by
    simpa only [rN, hL] using
      Submodule.factor_eq_zero_iff_mem_map_smul_top J L hJL y
  apply LinearMap.bijective_reduceModIdeal_of_addHom_square
    (K.map (Ideal.Quotient.mk J)) (f.reduceModIdeal J)
    rM.toAddMonoidHom rN.toAddMonoidHom hrM kM kN
    (f.reduceModIdeal L).toAddMonoidHom hfL
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl
