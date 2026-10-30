/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Hom

/-!
# Arbitrary completed coefficient families

For a finitely generated ideal, any family of completed target coefficients on
the natural-number basis is realized by a map from the completed free module.
On each original vector the value is the finite sum prescribed by these
coefficients. The inverse Hom equivalence recovers all coefficients by completing
the original basis evaluations. No finite support or convergence condition is
imposed on the coefficient family, and the original target module is arbitrary.
-/

@[expose] public section

noncomputable section

universe u w

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (N : Type w) [AddCommGroup N] [Module R N]

private theorem completed_free_coefficients (hI : I.FG) (c : ℕ → AdicCompletion I N) :
    ∃ G : AdicCompletion I (ℕ →₀ R) →ₗ[AdicCompletion I R] AdicCompletion I N,
      (∀ m : ℕ →₀ R, G (of I (ℕ →₀ R) m) = m.sum (fun i r ↦ r • c i)) ∧
      (∀ i : ℕ, G (of I (ℕ →₀ R) (Finsupp.single i 1)) = c i) ∧
      (∀ i : ℕ,
        map I (LinearMap.applyₗ (R := R) (M₂ := N) (Finsupp.single i 1))
          ((homEquivOfProjective I (ℕ →₀ R) N hI).symm G) = c i) := by
  let eR := (Finsupp.llift N R R ℕ).symm
  let C : AdicCompletion I ((ℕ →₀ R) →ₗ[R] N) ≃ₗ[AdicCompletion I R]
      (ℕ → AdicCompletion I N) :=
    (congr I eR).trans (piEquivOfFG I (fun _ : ℕ => N) hI)
  let F := C.symm c
  let G := homComparison I (ℕ →₀ R) N F
  have hcoord (X : AdicCompletion I ((ℕ →₀ R) →ₗ[R] N)) (i : ℕ) :
      C X i =
        map I (LinearMap.applyₗ (R := R) (M₂ := N) (Finsupp.single i 1)) X := by
    change piEquivOfFG I (fun _ : ℕ => N) hI (congr I eR X) i = _
    rw [piEquivOfFG_apply_apply, congr_apply]
    change map I (LinearMap.proj i) (map I eR.toLinearMap X) = _
    rw [map_comp_apply]
    rfl
  have hcoeff (i : ℕ) :
      map I (LinearMap.applyₗ (R := R) (M₂ := N) (Finsupp.single i 1)) F = c i := by
    calc
      map I (LinearMap.applyₗ (R := R) (M₂ := N) (Finsupp.single i 1)) F = C F i :=
        (hcoord F i).symm
      _ = c i := congrFun (C.apply_symm_apply c) i
  have hinv : (homEquivOfProjective I (ℕ →₀ R) N hI).symm G = F := by
    change (homEquivOfProjective I (ℕ →₀ R) N hI).symm
      (homComparison I (ℕ →₀ R) N F) = F
    rw [← homEquivOfProjective_apply I (ℕ →₀ R) N hI F]
    exact (homEquivOfProjective I (ℕ →₀ R) N hI).symm_apply_apply F
  have hbasis (i : ℕ) : G (of I (ℕ →₀ R) (Finsupp.single i 1)) = c i := by
    change homComparison I (ℕ →₀ R) N F
      (of I (ℕ →₀ R) (Finsupp.single i 1)) = c i
    rw [homComparison_apply_of]
    exact hcoeff i
  refine ⟨G, ?_, hbasis, ?_⟩
  · intro m
    let g : (ℕ →₀ R) →ₗ[R] AdicCompletion I N :=
      (G.restrictScalars R).comp (of I (ℕ →₀ R))
    have hg := congrArg (fun f : (ℕ →₀ R) →ₗ[R] AdicCompletion I N ↦ f m)
      ((Finsupp.llift (AdicCompletion I N) R R ℕ).apply_symm_apply g)
    simpa only [Finsupp.llift_apply, Finsupp.lift_apply, Finsupp.llift_symm_apply,
      g, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hbasis] using hg.symm
  · intro i
    rw [hinv]
    exact hcoeff i

end AdicCompletion
