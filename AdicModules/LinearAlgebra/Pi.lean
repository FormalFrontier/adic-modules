/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Finitely generated ideal action on dependent products

Action by a finitely generated ideal commutes with arbitrary dependent products
of submodules. The kernel of coordinatewise reduction by the ideal is therefore
the ideal action on the product module.
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


end Ring

end Ideal
