/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Nakayama

/-!
# Surjectivity and splittings under adic completion

For any ideal `I` of a commutative ring `R` and any `R`-linear map `f : M →ₗ[R] N`,
`map_surjective_iff_mkQ_comp_surjective` characterizes surjectivity of the induced map
on `I`-adic completions by surjectivity of the original map `M → N / I N`.

If `I` lies in the Jacobson radical of `R` and the original cokernel `N / range f`
is finitely generated, `surjective_of_map_surjective` reflects surjectivity from
completion to `f`. Neither original module is required to be finitely generated,
complete or Hausdorff, and the ideal need not be finitely generated.

When the original target `N` is projective, with no rank restriction,
`exists_rightInverse_of_map_comp_eq_id` deduces existence of an `R`-linear right
inverse from a right inverse over the completed ring. It does not assert that the
resulting right inverse completes to the supplied one.

## Implementation notes

The characteristic equivalence uses level-one evaluation and representatives in
the original source quotient; its converse is Mathlib's completion surjectivity
criterion. The reflection argument applies Nakayama's lemma to the original finite
cokernel, not to a quotient of a completed module. The splitting then follows from
the lifting property of the original projective target.

## References

- The Stacks Project, [Nakayama's lemma, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV).
- Mathlib's completion formalizations by Kenny Lau, Judith Ludwig, Christian Merten
  and Jiedong Jiang; quotient formalizations by Johannes Hölzl, Mario Carneiro,
  Kevin Buzzard and Yury Kudryashov; Nakayama formalization by Chris Hughes; and
  projective-module formalization by Kevin Buzzard and Antoine Labelle.
- The finite-cokernel Nakayama approach is also formalized in the Formal Frontier
  Projective Modules library.
-/

@[expose] public section

universe u v w

namespace AdicCompletion

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- For any ideal, the completed map is surjective if and only if the original map
composed with the quotient `N → N / I N` is surjective. -/
theorem map_surjective_iff_mkQ_comp_surjective
    (I : Ideal R) (f : M →ₗ[R] N) :
    Function.Surjective (map I f) ↔
      Function.Surjective ((I • (⊤ : Submodule R N)).mkQ.comp f) := by
  constructor
  · intro hf z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) z
    obtain ⟨x, hx⟩ := hf (of I N y)
    obtain ⟨m, hm⟩ :=
      Submodule.mkQ_surjective (I ^ 1 • (⊤ : Submodule R M)) (x.val 1)
    refine ⟨m, ?_⟩
    have hxy := congrArg (eval I N 1) hx
    rw [eval_of, eval_apply, map_val_apply, ← hm, pow_one] at hxy
    simpa only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply] using hxy
  · exact map_surjective_of_mkQ_comp_surjective

/-- For an ideal contained in the Jacobson radical, surjectivity after completion
implies surjectivity of a map with finitely generated original cokernel. This is
Nakayama's lemma applied to that cokernel; see the Stacks Project, Tag 00DV. -/
theorem surjective_of_map_surjective
    (I : Ideal R) (f : M →ₗ[R] N)
    [Module.Finite R (N ⧸ LinearMap.range f)]
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (hf : Function.Surjective (map I f)) :
    Function.Surjective f := by
  have hmod := (map_surjective_iff_mkQ_comp_surjective I f).mp hf
  have hgen : LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤ := by
    have h := LinearMap.range_eq_top_of_surjective _ hmod
    rw [LinearMap.range_comp, Submodule.map_mkQ_eq_top] at h
    exact (sup_comm _ _).trans h
  -- Pass generation modulo `I` to the original cokernel.
  have hC : I • (⊤ : Submodule R (N ⧸ LinearMap.range f)) = ⊤ := by
    have h := congrArg (Submodule.map (LinearMap.range f).mkQ) hgen
    simpa only [Submodule.map_sup, Submodule.mkQ_map_self, Submodule.map_smul'',
      Submodule.map_top, Submodule.range_mkQ, bot_sup_eq] using h
  have htop : (⊤ : Submodule R (N ⧸ LinearMap.range f)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤ Module.Finite.fg_top hC.ge hI
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro y _
  apply (Submodule.Quotient.mk_eq_zero _).mp
  have hy : (LinearMap.range f).mkQ y ∈
      (⊤ : Submodule R (N ⧸ LinearMap.range f)) := Submodule.mem_top
  simpa only [htop, Submodule.mem_bot, Submodule.mkQ_apply] using hy

/-- If the original cokernel is finitely generated, the original target is projective,
and the ideal lies in the Jacobson radical, a right inverse over the completed ring
implies existence of an `R`-linear right inverse. Its completion need not equal the
supplied right inverse. -/
theorem exists_rightInverse_of_map_comp_eq_id
    (I : Ideal R) (f : M →ₗ[R] N)
    [Module.Finite R (N ⧸ LinearMap.range f)]
    [Module.Projective R N]
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (s : AdicCompletion I N →ₗ[AdicCompletion I R] AdicCompletion I M)
    (hs : (map I f).comp s = LinearMap.id) :
    ∃ g : N →ₗ[R] M, f.comp g = LinearMap.id := by
  have hf : Function.Surjective (map I f) := by
    intro y
    exact ⟨s y, LinearMap.congr_fun hs y⟩
  exact Module.projective_lifting_property f LinearMap.id
    (surjective_of_map_surjective I f hI hf)

end AdicCompletion
