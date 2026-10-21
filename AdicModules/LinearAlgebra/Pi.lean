/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Finitely generated ideal action on dependent products

Action by a finitely generated ideal commutes with arbitrary dependent products
of submodules. The kernel of coordinatewise reduction by the ideal is therefore
the ideal action on the product module. Coordinatewise reduction consequently
identifies the quotient of a product with the product of its quotients.
-/

set_option warningAsError true

@[expose] public section

universe uR uJ uM

namespace Ideal

open scoped Pointwise

section Semiring

variable {R : Type uR} {J : Type uJ} {M : J → Type uM}
variable [CommSemiring R] [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]

/-- Action by a finitely generated ideal commutes with an arbitrary dependent
product of submodules. -/
theorem FG.smul_pi {I : Ideal R} (hI : I.FG) (N : ∀ j, Submodule R (M j)) :
    I • Submodule.pi Set.univ N =
      Submodule.pi Set.univ (fun j => I • N j) := by
  classical
  refine le_antisymm ?_ ?_
  · refine Submodule.smul_le.mpr ?_
    intro r hr x hx j hj
    exact Submodule.smul_mem_smul hr (hx j hj)
  · induction I, hI using Submodule.fg_induction with
    | singleton r =>
      intro x hx
      have hx' : ∀ j, ∃ y ∈ N j, r • y = x j := by
        intro j
        have hxj : x j ∈ (Ideal.span {r} : Ideal R) • N j := hx j trivial
        rw [Submodule.ideal_span_singleton_smul] at hxj
        exact (Submodule.mem_smul_pointwise_iff_exists (x j) r (N j)).mp hxj
      choose y hy hyx using hx'
      have hyPi : y ∈ Submodule.pi Set.univ N := fun j _ => hy j
      have hmem : r • y ∈ (Ideal.span {r} : Ideal R) • Submodule.pi Set.univ N :=
        Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) hyPi
      have hyx' : r • y = x := funext hyx
      exact hyx' ▸ hmem
    | sup K L _ _ ihK ihL =>
      intro x hx
      have hx' : ∀ j, ∃ y ∈ K • N j, ∃ z ∈ L • N j, y + z = x j := by
        intro j
        have hxj : x j ∈ (K ⊔ L) • N j := hx j trivial
        rw [Submodule.sup_smul] at hxj
        exact Submodule.mem_sup.mp hxj
      choose y hy z hz hyzx using hx'
      have hyPi : y ∈ Submodule.pi Set.univ (fun j => K • N j) := fun j _ => hy j
      have hzPi : z ∈ Submodule.pi Set.univ (fun j => L • N j) := fun j _ => hz j
      rw [Submodule.sup_smul]
      exact Submodule.mem_sup.mpr ⟨y, ihK hyPi, z, ihL hzPi, funext hyzx⟩

end Semiring

section Ring

variable {R : Type uR} [CommRing R]

/-- The kernel of coordinatewise reduction by a finitely generated ideal
is the ideal action on the product module. -/
theorem FG.ker_piMap_mkQ {I : Ideal R} (hI : I.FG)
    {J : Type uJ} (M : J → Type uM)
    [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] :
    LinearMap.ker
        (LinearMap.piMap fun j => (I • (⊤ : Submodule R (M j))).mkQ) =
      I • (⊤ : Submodule R (∀ j, M j)) := by
  change LinearMap.ker
    (LinearMap.pi fun j =>
      (I • (⊤ : Submodule R (M j))).mkQ.comp (LinearMap.proj j)) = _
  rw [LinearMap.ker_pi]
  simp_rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [Submodule.iInf_comap_proj]
  simpa only [Submodule.pi_top] using
    (hI.smul_pi (fun j => (⊤ : Submodule R (M j)))).symm

/-- Coordinatewise reduction by a finitely generated ideal identifies the quotient
of an arbitrary dependent product with the product of the coordinate quotients. -/
noncomputable def FG.quotientPi {I : Ideal R} (hI : I.FG)
    {J : Type uJ} (M : J → Type uM)
    [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] :
    ((∀ j, M j) ⧸ (I • (⊤ : Submodule R (∀ j, M j)))) ≃ₗ[R]
      ∀ j, M j ⧸ (I • (⊤ : Submodule R (M j))) := by
  classical
  let f := LinearMap.piMap fun j => (I • (⊤ : Submodule R (M j))).mkQ
  have hf : Function.Surjective f := by
    intro x
    choose y hy using fun j => (I • (⊤ : Submodule R (M j))).mkQ_surjective (x j)
    exact ⟨y, funext hy⟩
  exact (Submodule.quotEquivOfEq _ _ (hI.ker_piMap_mkQ M).symm).trans
    (f.quotKerEquivOfSurjective hf)

@[simp]
theorem FG.quotientPi_apply_mk {I : Ideal R} (hI : I.FG)
    {J : Type uJ} (M : J → Type uM)
    [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] (x : ∀ j, M j) :
    hI.quotientPi M (Submodule.Quotient.mk x) =
      fun j => (Submodule.Quotient.mk (x j) : M j ⧸ (I • (⊤ : Submodule R (M j)))) := by
  rfl

theorem FG.quotientPi_mkQ {I : Ideal R} (hI : I.FG)
    {J : Type uJ} (M : J → Type uM)
    [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] (x : ∀ j, M j) :
    hI.quotientPi M ((I • (⊤ : Submodule R (∀ j, M j))).mkQ x) =
      fun j => (I • (⊤ : Submodule R (M j))).mkQ (x j) :=
  hI.quotientPi_apply_mk M x

@[simp]
theorem FG.quotientPi_comp_mkQ {I : Ideal R} (hI : I.FG)
    {J : Type uJ} (M : J → Type uM)
    [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] :
    (hI.quotientPi M).toLinearMap.comp (I • (⊤ : Submodule R (∀ j, M j))).mkQ =
      LinearMap.piMap (fun j => (I • (⊤ : Submodule R (M j))).mkQ) := by
  ext x j
  exact congrFun (hI.quotientPi_mkQ M x) j

end Ring

end Ideal
