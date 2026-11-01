/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Pi
public import AdicModules.AdicCompletion.RestrictScalars
public import AdicModules.AdicCompletion.RingHom

/-!
# Adic completion over finite products of coefficient rings

For a finite family of commutative rings `R i` and any ideal `I` of `Π i, R i`,
adic completion decomposes over the coordinate ideals
`I.map (Pi.evalRingHom R i)`. The ring comparison is an algebra equivalence over
`Π i, R i`, whose coefficient map sends `a` to the family of canonical images of
`a i`. For an arbitrary family of `R i`-modules, the module comparison is linear
over `Π i, R i` with its pointwise action.

The reduction laws describe every completed element at every natural precision,
including zero, by projecting an original representative at that precision.
The module comparisons also intertwine the canonical actions of the completed
coefficient rings through the ring comparisons.

The index, coefficient-ring, and module universe parameters are independent.
No finite-generation, completeness, separatedness, or nontriviality assumption is
imposed; empty indexed products and zero rings are included.

## References

The completion functor and common-coefficient finite-product comparison are from
Mathlib's adic completion formalization by Judith Ludwig and Christian Merten.
The coordinate-ideal comparisons use this library's scalar-restriction and
completed ring maps.
-/

@[expose] public section

universe uι uR uM

namespace AdicCompletion

/-- Adic completion of a finite product of modules over varying coefficient rings
is the product of their coordinate-ideal completions, linearly over the original
product ring with its canonical pointwise action. -/
noncomputable def piCoeffLinearEquiv {ι : Type uι} [Finite ι]
    (R : ι → Type uR) [∀ i, CommRing (R i)] (I : Ideal (Π i, R i))
    (M : ι → Type uM) [∀ i, AddCommGroup (M i)] [∀ i, Module (R i) (M i)] :
    AdicCompletion I (Π i, M i) ≃ₗ[Π i, R i]
      Π i, AdicCompletion (I.map (Pi.evalRingHom R i)) (M i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI (i : ι) : Algebra (Π j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
  letI (i : ι) : Module (Π j, R j) (M i) :=
    Module.compHom (M i) (Pi.evalRingHom R i)
  letI (i : ι) : IsScalarTower (Π j, R j) (R i) (M i) :=
    IsScalarTower.of_compHom (Π j, R j) (R i) (M i)
  -- Use the common-base product dictionary for the common-coefficient comparison.
  letI : Module (Π i, R i) (Π i, M i) := Pi.module ι M (Π i, R i)
  letI : Module (Π i, R i) (AdicCompletion I (Π i, M i)) := inferInstance
  exact ((piEquivOfFintype I M).restrictScalars (Π i, R i)).trans
    (LinearEquiv.piCongrRight fun i ↦ (restrictScalarsEquiv (S := R i) I (M i)).symm)

/-- On coefficient rings, each coordinate of the linear comparison is the completed
coordinate ring homomorphism. -/
theorem piCoeffLinearEquiv_ring_apply {ι : Type uι} [Finite ι]
    (R : ι → Type uR) [∀ i, CommRing (R i)] (I : Ideal (Π i, R i))
    (x : AdicCompletion I (Π i, R i)) (i : ι) :
    piCoeffLinearEquiv R I R x i =
      mapRingHom I (I.map (Pi.evalRingHom R i)) (Pi.evalRingHom R i)
        Ideal.le_comap_map x := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let (i : ι) : Algebra (Π j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
  let (i : ι) : Module (Π j, R j) (R i) :=
    Module.compHom (R i) (Pi.evalRingHom R i)
  let (i : ι) : IsScalarTower (Π j, R j) (R i) (R i) :=
    IsScalarTower.of_compHom (Π j, R j) (R i) (R i)
  let : Module (Π i, R i) (Π i, R i) := Pi.module ι R (Π i, R i)
  let y : AdicCompletion I (Π i, R i) := x
  change (restrictScalarsEquiv (S := R i) I (R i)).symm
    (piEquivOfFintype I R y i) = _
  apply (restrictScalarsEquiv (S := R i) I (R i)).injective
  rw [LinearEquiv.apply_symm_apply, piEquivOfFintype_apply]
  change map I (LinearMap.proj i) y = _
  exact (restrictScalarsEquiv_mapRingHom (S := R i) I x).symm

/-- Adic completion of a finite product of coefficient rings is the product of
the completions at the mapped coordinate ideals, as an algebra over the original
product ring. The target coefficient map is coordinatewise canonical completion. -/
noncomputable def piCoeffAlgEquiv {ι : Type uι} [Finite ι]
    (R : ι → Type uR) [∀ i, CommRing (R i)] (I : Ideal (Π i, R i)) :
    AdicCompletion I (Π i, R i) ≃ₐ[Π i, R i]
      Π i, AdicCompletion (I.map (Pi.evalRingHom R i)) (R i) := by
  let f : AdicCompletion I (Π i, R i) →+*
      Π i, AdicCompletion (I.map (Pi.evalRingHom R i)) (R i) :=
    RingHom.pi fun i ↦
      mapRingHom I (I.map (Pi.evalRingHom R i)) (Pi.evalRingHom R i) Ideal.le_comap_map
  let g : AdicCompletion I (Π i, R i) →ₐ[Π i, R i]
      Π i, AdicCompletion (I.map (Pi.evalRingHom R i)) (R i) :=
    { f with
      commutes' := by
        intro a
        funext i
        change mapRingHom I (I.map (Pi.evalRingHom R i)) (Pi.evalRingHom R i)
          Ideal.le_comap_map (of I (Π j, R j) a) =
            of (I.map (Pi.evalRingHom R i)) (R i) (a i)
        exact mapRingHom_of I (I.map (Pi.evalRingHom R i))
          (Pi.evalRingHom R i) Ideal.le_comap_map a }
  apply AlgEquiv.ofBijective g
  have hg : (g : AdicCompletion I (Π i, R i) →
      Π i, AdicCompletion (I.map (Pi.evalRingHom R i)) (R i)) =
      piCoeffLinearEquiv R I R := by
    funext x i
    exact (piCoeffLinearEquiv_ring_apply R I x i).symm
  rw [hg]
  exact (piCoeffLinearEquiv R I R).bijective

section Pi

variable {ι : Type uι} [Finite ι]
    (R : ι → Type uR) [∀ i, CommRing (R i)] (I : Ideal (Π i, R i))

/-- The finite coefficient-ring comparison sends an original element to the
canonical images of its coordinates. -/
@[simp]
theorem piCoeffAlgEquiv_of (a : Π i, R i) :
    piCoeffAlgEquiv R I (of I (Π i, R i) a) =
      fun i ↦ of (I.map (Pi.evalRingHom R i)) (R i) (a i) := by
  funext i
  exact mapRingHom_of I (I.map (Pi.evalRingHom R i))
    (Pi.evalRingHom R i) Ideal.le_comap_map a

/-- At every precision, including zero, each coordinate of the coefficient-ring
comparison reduces to the corresponding coordinate of any representative of the
source reduction. -/
theorem evalₐ_piCoeffAlgEquiv_of_eq_mk (n : ℕ)
    (x : AdicCompletion I (Π i, R i)) (a : Π i, R i)
    (h : evalₐ I n x = Ideal.Quotient.mk (I ^ n) a) (i : ι) :
    evalₐ (I.map (Pi.evalRingHom R i)) n (piCoeffAlgEquiv R I x i) =
      Ideal.Quotient.mk ((I.map (Pi.evalRingHom R i)) ^ n) (a i) := by
  change evalₐ (I.map (Pi.evalRingHom R i)) n
    (mapRingHom I (I.map (Pi.evalRingHom R i)) (Pi.evalRingHom R i)
      Ideal.le_comap_map x) = _
  rw [evalₐ_mapRingHom, h, Ideal.quotientMap_mk]
  rfl

variable (M : ι → Type uM) [∀ i, AddCommGroup (M i)] [∀ i, Module (R i) (M i)]

/-- The finite coefficient-module comparison sends an original product element
to the canonical images of its coordinates. -/
@[simp]
theorem piCoeffLinearEquiv_of (m : Π i, M i) :
    piCoeffLinearEquiv R I M (of I (Π i, M i) m) =
      fun i ↦ of (I.map (Pi.evalRingHom R i)) (M i) (m i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let (i : ι) : Algebra (Π j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
  let (i : ι) : Module (Π j, R j) (M i) :=
    Module.compHom (M i) (Pi.evalRingHom R i)
  let (i : ι) : IsScalarTower (Π j, R j) (R i) (M i) :=
    IsScalarTower.of_compHom (Π j, R j) (R i) (M i)
  let : Module (Π i, R i) (Π i, M i) := Pi.module ι M (Π i, R i)
  funext i
  change (restrictScalarsEquiv (S := R i) I (M i)).symm
    (piEquivOfFintype I M (of I (Π j, M j) m) i) = _
  rw [piEquivOfFintype_apply, pi_of, restrictScalarsEquiv_symm_of]
  rfl

/-- At every precision, including zero, each coordinate of the coefficient-module
comparison reduces to the corresponding coordinate of any representative of the
source reduction. -/
theorem eval_piCoeffLinearEquiv_of_eq_mk (n : ℕ)
    (x : AdicCompletion I (Π i, M i)) (m : Π i, M i)
    (h : eval I (Π i, M i) n x = Submodule.Quotient.mk m) (i : ι) :
    eval (I.map (Pi.evalRingHom R i)) (M i) n (piCoeffLinearEquiv R I M x i) =
      Submodule.Quotient.mk (m i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let (i : ι) : Algebra (Π j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
  let (i : ι) : Module (Π j, R j) (M i) :=
    Module.compHom (M i) (Pi.evalRingHom R i)
  let (i : ι) : IsScalarTower (Π j, R j) (R i) (M i) :=
    IsScalarTower.of_compHom (Π j, R j) (R i) (M i)
  let : Module (Π i, R i) (Π i, M i) := Pi.module ι M (Π i, R i)
  -- Name the input and its reduction in the common-base product module.
  let y : AdicCompletion I (Π i, M i) := x
  have hy : eval I (Π i, M i) n y = Submodule.Quotient.mk m := h
  let p : (Π j, M j) →ₗ[Π j, R j] M i := LinearMap.proj i
  change eval (I.map (algebraMap (Π j, R j) (R i))) (M i) n
    ((restrictScalarsEquiv (S := R i) I (M i)).symm
      (piEquivOfFintype I M y i)) = _
  rw [restrictScalarsEquiv_symm_eval]
  have hi : eval I (M i) n (piEquivOfFintype I M y i) =
      Submodule.Quotient.mk (m i) := by
    rw [piEquivOfFintype_apply]
    change p.reduceModIdeal (I ^ n) (eval I (Π j, M j) n y) = _
    calc
      _ = p.reduceModIdeal (I ^ n) (Submodule.Quotient.mk m) := by rw [hy]
      _ = Submodule.Quotient.mk (p m) :=
        LinearMap.reduceModIdeal_apply (I ^ n) p m
      _ = Submodule.Quotient.mk (m i) := rfl
  rw [hi, restrictScalarsLevelEquiv_symm_mk]

/-- The finite coefficient-module comparison intertwines the canonical completed
coefficient actions through the coefficient-ring comparison. -/
theorem piCoeffLinearEquiv_smul (a : AdicCompletion I (Π i, R i))
    (x : AdicCompletion I (Π i, M i)) :
    piCoeffLinearEquiv R I M (a • x) =
      piCoeffAlgEquiv R I a • piCoeffLinearEquiv R I M x := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let (i : ι) : Algebra (Π j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
  let (i : ι) : Module (Π j, R j) (M i) :=
    Module.compHom (M i) (Pi.evalRingHom R i)
  let (i : ι) : IsScalarTower (Π j, R j) (R i) (M i) :=
    IsScalarTower.of_compHom (Π j, R j) (R i) (M i)
  funext i
  change (restrictScalarsEquiv (S := R i) I (M i)).symm
    (piEquivOfFintype I M (a • x) i) =
      mapRingHom I (I.map (Pi.evalRingHom R i)) (Pi.evalRingHom R i)
        Ideal.le_comap_map a •
          (restrictScalarsEquiv (S := R i) I (M i)).symm (piEquivOfFintype I M x i)
  rw [show piEquivOfFintype I M (a • x) i = a • piEquivOfFintype I M x i from
    congrFun ((piEquivOfFintype I M).map_smul a x) i]
  exact (restrictScalarsSemilinearMap (S := R i) I (M i)).map_smulₛₗ a
    (piEquivOfFintype I M x i)

end Pi

end AdicCompletion
