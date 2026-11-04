/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import AdicModules.Topology.SubmoduleFamily
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.UniformSpace.Basic

/-!
# Submodule families and the stock module completion

The general application below keeps the original ring, additive group, module,
and submodule family while applying the completion module and continuous linear
coercion. It observes the whole module's distributive-action parent and the whole
linear and additive parents of the coercion, not just its scalar formula.

The integer control uses the zero-submodule family indexed by `Unit`, corresponding
to the zero-subgroup control in `GroupTheoryTest.SubgroupFamily`. Its diagonal
uniformity justifies injectivity; discrete topology alone is not used to infer a
uniformity. The completed action separates the images of `2` and `1` and sends the
image of `1` to the image of `2` under the scalar `2`.
-/

@[expose] public section

open Filter Set
open scoped Topology

universe uR uM uI

/-- Apply the completion module and continuous linear coercion to an arbitrary
original module and submodule family, retaining the bundled parents and actions. -/
example {R : Type uR} {M : Type uM} {I : Type uI}
    [r : Ring R] [g : AddCommGroup M] [m : Module R M] (F : I → Submodule R M) :
    let s : Semiring R := r.toSemiring
    let a : AddGroup M := g.toAddGroup
    let c : AddCommMonoid M := g.toAddCommMonoid
    let da : @DistribMulAction R M s.toMonoid c.toAddMonoid := m.toDistribMulAction
    let d : @DistribSMul R M a.toAddMonoid.toAddZeroClass :=
      @DistribMulAction.toDistribSMul R M s.toMonoid c.toAddMonoid da
    let sm : SMul R M := da.toMulAction.toSMul
    let H : I → @AddSubgroup M a := fun i => (F i).toAddSubgroup
    let S : I → @AddSubmonoid M a.toAddMonoid.toAddZeroClass :=
      fun i => (H i).toAddSubmonoid
    let T : I → @AddSubsemigroup M a.toAddMonoid.toAdd :=
      fun i => (H i).toAddSubmonoid.toAddSubsemigroup
    let B : @AddGroupFilterBasis M a := @AddSubgroup.familyBasis M I g H
    let t : TopologicalSpace M := B.topology
    let u : UniformSpace M :=
      @IsTopologicalAddGroup.rightUniformSpace M a t
        (@AddGroupFilterBasis.isTopologicalAddGroup M a B)
    let hTop : @IsTopologicalAddGroup M t a :=
      @AddGroupFilterBasis.isTopologicalAddGroup M a B
    let hU : @IsUniformAddGroup M u a :=
      @isUniformAddGroup_of_addCommGroup M g t hTop
    let hUC : @UniformContinuousConstSMul R M u sm :=
      @Submodule.familyBasis_uniformContinuousConstSMul R M I r g m F
    let C : Type uM := @UniformSpace.Completion M u
    let uC : UniformSpace C := inferInstance
    let gC : AddCommGroup C := @UniformSpace.Completion.instAddCommGroup M u g hU
    let smC : SMul R C := inferInstance
    let mC : @Module R C s gC.toAddCommMonoid :=
      @UniformSpace.Completion.instModule (α := M) (R := R) u g hU s m hUC
    let κ : @ContinuousLinearMap R R s s (RingHom.id R)
        M t c C uC.toTopologicalSpace gC.toAddCommMonoid m mC :=
      @UniformSpace.Completion.toComplL (α := M) (S := R) u g hU s m hUC
    let ℓ : @LinearMap R R s s (RingHom.id R) M C c gC.toAddCommMonoid m mC :=
      κ.toLinearMap
    a = g.toAddGroup ∧ c = g.toAddCommMonoid ∧ da = m.toDistribMulAction ∧
      d.toSMulZeroClass.toSMul = sm ∧
      S = (fun i => (F i).toAddSubmonoid) ∧
      T = (fun i => (F i).toAddSubmonoid.toAddSubsemigroup) ∧
      u.toTopologicalSpace = t ∧
      gC.toAddGroup = @UniformSpace.Completion.addGroup M u a hU ∧
      mC.toDistribMulAction =
        (@UniformSpace.Completion.instModule (α := M) (R := R)
          u g hU s m hUC).toDistribMulAction ∧
      mC.toDistribMulAction.toMulAction.toSMul = smC ∧
      κ = @UniformSpace.Completion.toComplL (α := M) (S := R) u g hU s m hUC ∧
      κ.toLinearMap = ℓ ∧
      ℓ.toAddMonoidHom = @UniformSpace.Completion.toCompl M u a hU ∧
      ℓ.toAddHom = (@UniformSpace.Completion.toCompl M u a hU).toAddHom ∧
      κ.toLinearMap.toMulActionHom = ℓ.toMulActionHom ∧
      κ.toFun = @UniformSpace.Completion.coe' M u ∧
      (κ : M → C) = @UniformSpace.Completion.coe' M u ∧
      ∀ (b : R) (x : M),
        κ.toFun (@SMul.smul R M sm b x) =
          @SMul.smul R C mC.toDistribMulAction.toMulAction.toSMul b (κ.toFun x) := by
  intro s a c da d sm H S T B t u hTop hU hUC C uC gC smC mC κ ℓ
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_,
    rfl, rfl, ?_, ?_, ?_⟩
  · exact @UniformSpace.Completion.toAddMonoidHom_toComplL (α := M) (S := R)
      u g hU s m hUC
  · exact @UniformSpace.Completion.coe_toComplL (α := M) (S := R) u g hU s m hUC
  · exact @UniformSpace.Completion.coe_toComplL (α := M) (S := R) u g hU s m hUC
  · intro b x
    exact κ.toLinearMap.map_smul' b x

/-- The zero-submodule family on the original integer module has diagonal
uniformity and a nonzero stock completed action on its original image. -/
private theorem zero_submodule_completion_smul :
    let r : Ring ℤ := inferInstance
    let s : Semiring ℤ := r.toSemiring
    let g : AddCommGroup ℤ := inferInstance
    let a : AddGroup ℤ := g.toAddGroup
    let c : AddCommMonoid ℤ := g.toAddCommMonoid
    let m : @Module ℤ ℤ s c := inferInstance
    let da : @DistribMulAction ℤ ℤ s.toMonoid c.toAddMonoid := m.toDistribMulAction
    let d : @DistribSMul ℤ ℤ a.toAddMonoid.toAddZeroClass :=
      @DistribMulAction.toDistribSMul ℤ ℤ s.toMonoid c.toAddMonoid da
    let sm : SMul ℤ ℤ := da.toMulAction.toSMul
    let F : Unit → @Submodule ℤ ℤ s c m := fun _ => ⊥
    let H : Unit → @AddSubgroup ℤ a := fun i => (F i).toAddSubgroup
    let S : Unit → @AddSubmonoid ℤ a.toAddMonoid.toAddZeroClass :=
      fun i => (H i).toAddSubmonoid
    let T : Unit → @AddSubsemigroup ℤ a.toAddMonoid.toAdd :=
      fun i => (H i).toAddSubmonoid.toAddSubsemigroup
    let B : @AddGroupFilterBasis ℤ a := @AddSubgroup.familyBasis ℤ Unit g H
    let t : TopologicalSpace ℤ := B.topology
    let u : UniformSpace ℤ :=
      @IsTopologicalAddGroup.rightUniformSpace ℤ a t
        (@AddGroupFilterBasis.isTopologicalAddGroup ℤ a B)
    let hTop : @IsTopologicalAddGroup ℤ t a :=
      @AddGroupFilterBasis.isTopologicalAddGroup ℤ a B
    let hU : @IsUniformAddGroup ℤ u a :=
      @isUniformAddGroup_of_addCommGroup ℤ g t hTop
    let hUC : @UniformContinuousConstSMul ℤ ℤ u sm :=
      @Submodule.familyBasis_uniformContinuousConstSMul ℤ ℤ Unit r g m F
    let C : Type := @UniformSpace.Completion ℤ u
    let gC : AddCommGroup C := @UniformSpace.Completion.instAddCommGroup ℤ u g hU
    let smC : SMul ℤ C := inferInstance
    let mC : @Module ℤ C s gC.toAddCommMonoid :=
      @UniformSpace.Completion.instModule (α := ℤ) (R := ℤ) u g hU s m hUC
    let κ : ℤ → C := @UniformSpace.Completion.coe' ℤ u
    a = g.toAddGroup ∧ c = g.toAddCommMonoid ∧ da = m.toDistribMulAction ∧
      H = (fun _ : Unit => (⊥ : @AddSubgroup ℤ a)) ∧
      S = (fun i => (F i).toAddSubmonoid) ∧
      T = (fun i => (F i).toAddSubmonoid.toAddSubsemigroup) ∧
      d.toSMulZeroClass.toSMul = sm ∧ u.toTopologicalSpace = t ∧
      u.uniformity = 𝓟 (SetRel.id : Set (ℤ × ℤ)) ∧
      mC.toDistribMulAction.toMulAction.toSMul = smC ∧
      @SMul.smul ℤ C mC.toDistribMulAction.toMulAction.toSMul 2 (κ 1) = κ 2 ∧
      κ 2 ≠ κ 1 := by
  intro r s g a c m da d sm F H S T B t u hTop hU hUC C gC smC mC κ
  have hn : @nhds ℤ t 0 = 𝓟 ({0} : Set ℤ) := by
    simpa [H, F, Submodule.bot_toAddSubgroup] using
      (@AddSubgroup.familyBasis_nhds_zero_eq_iInf ℤ Unit g H)
  have hu : u.uniformity = 𝓟 (SetRel.id : Set (ℤ × ℤ)) := by
    change Filter.comap (fun p : ℤ × ℤ => p.2 + -p.1) (@nhds ℤ t 0) = _
    rw [hn, Filter.comap_principal]
    congr 1
    ext p
    simp [SetRel.id, add_neg_eq_zero, eq_comm]
  have he : u = ⊥ := UniformSpace.ext hu
  have ht : t = ⊥ := congrArg (@UniformSpace.toTopologicalSpace ℤ) he
  have hT0 : @T0Space ℤ u.toTopologicalSpace := by
    change @T0Space ℤ t
    rw [ht]
    infer_instance
  have : @IsUniformAddGroup ℤ u a := hU
  have : @UniformContinuousConstSMul ℤ ℤ u sm := hUC
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hu, rfl, ?_, ?_⟩
  · have hOne := @MulAction.one_smul ℤ C s.toMonoid
      mC.toDistribMulAction.toMulAction (κ 1)
    calc
      _ = @SMul.smul ℤ C mC.toDistribMulAction.toMulAction.toSMul 1 (κ 1) +
          @SMul.smul ℤ C mC.toDistribMulAction.toMulAction.toSMul 1 (κ 1) :=
        @Module.add_smul ℤ C s gC.toAddCommMonoid mC 1 1 (κ 1)
      _ = κ 1 + κ 1 := congrArg (fun z : C => z + z) hOne
      _ = κ 2 := (@UniformSpace.Completion.coe_add ℤ u a hU 1 1).symm
  · intro hEq
    exact (by decide : (2 : ℤ) ≠ 1) (@UniformSpace.Completion.coe_injective ℤ u hT0 2 1 hEq)
