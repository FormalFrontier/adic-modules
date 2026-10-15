/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Descent along surjective semilinear maps

A semilinear map out of an additive group descends along a surjective
semilinear map exactly when it kills its kernel. The intermediate and final
modules need only be additive commutative monoids.

For scalar maps `σ : R →+* S`, `τ : S →+* T`, and `ρ : R →+* T` with
`τ.comp σ = ρ`, surjectivity of `σ` supplies all `S`-scalars in the descended
scalar law. This is separate from surjectivity of the module map. Neither `τ`
nor `ρ` is required to be surjective. Identity scalar maps give ordinary
linear descent over a semiring. In the ring and additive-group setting,
descent along a quotient map agrees with `Submodule.liftQ`.
-/

@[expose] public section

universe uR uS uT uM uN uP

namespace LinearMap

section Semiring

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable {M : Type uM} {N : Type uN} {P : Type uP}
variable [Semiring R] [Semiring S] [Semiring T]
variable [AddCommGroup M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module S N] [Module T P]
variable {σ : R →+* S} {ρ : R →+* T} {τ : S →+* T}
variable [RingHomSurjective σ] [RingHomCompTriple σ τ ρ]

private theorem factorsThrough_of_ker_le_ker (f : M →ₛₗ[σ] N)
    (g : M →ₛₗ[ρ] P) (hker : f.ker ≤ g.ker) : Function.FactorsThrough g f := by
  intro x y hxy
  exact (g.toAddMonoidHom.sub_mem_ker_iff).mp
    (hker ((f.toAddMonoidHom.sub_mem_ker_iff).mpr hxy))

/-- Descend `g` along a surjective `f` when `g` kills the kernel of `f`.
The underlying function is the extension of `g` along `f`, with zero as its
value outside the range. -/
noncomputable def liftOfSurjective (f : M →ₛₗ[σ] N) (hf : Function.Surjective f)
    (g : M →ₛₗ[ρ] P) (hker : f.ker ≤ g.ker) : N →ₛₗ[τ] P where
  toFun := Function.extend f g 0
  map_add' := by
    have hfg := factorsThrough_of_ker_le_ker f g hker
    intro x y
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← f.map_add, hfg.extend_apply, hfg.extend_apply, hfg.extend_apply, g.map_add]
  map_smul' := by
    have hfg := factorsThrough_of_ker_le_ker f g hker
    intro c y
    obtain ⟨r, rfl⟩ := σ.surjective c
    obtain ⟨x, rfl⟩ := hf y
    rw [← f.map_smulₛₗ, hfg.extend_apply, hfg.extend_apply, g.map_smulₛₗ,
      RingHomCompTriple.comp_apply]

/-- Evaluation of the descended map on the image of `f`. -/
@[simp]
theorem liftOfSurjective_apply (f : M →ₛₗ[σ] N) (hf : Function.Surjective f)
    (g : M →ₛₗ[ρ] P) (hker : f.ker ≤ g.ker) (x : M) :
    f.liftOfSurjective (τ := τ) hf g hker (f x) = g x := by
  exact (factorsThrough_of_ker_le_ker f g hker).extend_apply 0 x

/-- The descended map factors `g` through `f`. -/
@[simp]
theorem liftOfSurjective_comp (f : M →ₛₗ[σ] N) (hf : Function.Surjective f)
    (g : M →ₛₗ[ρ] P) (hker : f.ker ≤ g.ker) :
    (f.liftOfSurjective (τ := τ) hf g hker).comp f = g := by
  ext x
  exact liftOfSurjective_apply (τ := τ) f hf g hker x

/-- The descender is characterized by its composite with `f`.
Uniqueness is cancellation of precomposition by the surjection. -/
theorem eq_liftOfSurjective_iff (f : M →ₛₗ[σ] N) (hf : Function.Surjective f)
    (g : M →ₛₗ[ρ] P) (hker : f.ker ≤ g.ker) (h : N →ₛₗ[τ] P) :
    h = f.liftOfSurjective (τ := τ) hf g hker ↔ h.comp f = g := by
  rw [← cancel_right hf, liftOfSurjective_comp (τ := τ)]

/-- Killing the kernel of a surjective semilinear map is equivalent to
factoring uniquely through it. Both kernels are submodules over `R`. -/
theorem ker_le_ker_iff_existsUnique_comp_eq (f : M →ₛₗ[σ] N)
    (hf : Function.Surjective f) (g : M →ₛₗ[ρ] P) :
    f.ker ≤ g.ker ↔ ∃! h : N →ₛₗ[τ] P, h.comp f = g := by
  constructor
  · intro hker
    refine ⟨f.liftOfSurjective (τ := τ) hf g hker,
      liftOfSurjective_comp (τ := τ) f hf g hker, ?_⟩
    intro h hh
    exact (eq_liftOfSurjective_iff (τ := τ) f hf g hker h).2 hh
  · rintro ⟨h, hh, _⟩
    simpa only [hh] using f.ker_le_ker_comp h

end Semiring

section Ring

variable {R : Type uR} {T : Type uT} {M : Type uM} {P : Type uP}
variable [Ring R] [Ring T] [AddCommGroup M] [AddCommGroup P]
variable [Module R M] [Module T P] {τ : R →+* T}

/-- Over rings with additive-group targets, descent along a quotient map
agrees with the standard quotient lift. -/
@[simp]
theorem liftOfSurjective_mkQ (p : Submodule R M) (g : M →ₛₗ[τ] P)
    (hker : p ≤ g.ker) :
    p.mkQ.liftOfSurjective (τ := τ) p.mkQ_surjective g
        ((Submodule.ker_mkQ p).le.trans hker) = p.liftQ g hker := by
  apply (cancel_right p.mkQ_surjective).mp
  rw [liftOfSurjective_comp (τ := τ), Submodule.liftQ_mkQ]

end Ring

end LinearMap
