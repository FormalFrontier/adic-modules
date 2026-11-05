/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import AdicModules.Topology.Completion
import AdicModules.Topology.SubmoduleFamily
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-!
# An integer quotient for module completion

The zero-submodule family on the integer module gives a diagonal uniformity by
its neighborhood calculation. The quotient by the span of `2` retains the stock
quotient group, module, coinduced topology and continuous linear quotient map.
Its right uniformity is discrete, hence complete, and the quotient has a proper
nonzero kernel: `2` maps to zero, whereas `1` does not. Its completion extension
is a quotient map. The first isomorphism theorem on the completion quotient is a
homeomorphism, with the forward and inverse identities on both the completion
and the original integer module.

The controls below keep the whole quotient records, their action parents and the
whole bundled quotient map. Completeness uses the discrete uniformity, not just
the discrete topology. The fixed-scalar property concerns the quotient module's
own action. The proofs use Mathlib's quotient and discrete-uniformity APIs and
`AddSubgroup.familyBasis_nhds_zero_eq_iInf` for the source neighborhood calculation.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-- The quotient by the even integers is a complete separated target for the
zero-family uniformity. Its completion extension induces a homeomorphic linear
first isomorphism, compatible with the original quotient map in both directions. -/
example :
    let rZ : Ring ℤ := inferInstance
    let sZ : Semiring ℤ := rZ.toSemiring
    let gM : AddCommGroup ℤ := inferInstance
    let aM : AddGroup ℤ := gM.toAddGroup
    let cM : AddCommMonoid ℤ := gM.toAddCommMonoid
    let mM : @Module ℤ ℤ sZ cM := inferInstance
    let daM : @DistribMulAction ℤ ℤ sZ.toMonoid cM.toAddMonoid :=
      mM.toDistribMulAction
    let smM : SMul ℤ ℤ := daM.toMulAction.toSMul
    let F₀ : Unit → @Submodule ℤ ℤ sZ cM mM := fun _ => ⊥
    let H₀ : Unit → @AddSubgroup ℤ aM := fun i => (F₀ i).toAddSubgroup
    let B₀ : @AddGroupFilterBasis ℤ aM := @AddSubgroup.familyBasis ℤ Unit gM H₀
    let tM : TopologicalSpace ℤ := B₀.topology
    let hTM : @IsTopologicalAddGroup ℤ tM aM :=
      @AddGroupFilterBasis.isTopologicalAddGroup ℤ aM B₀
    let uM : UniformSpace ℤ :=
      @IsTopologicalAddGroup.rightUniformSpace ℤ aM tM hTM
    let hUM : @IsUniformAddGroup ℤ uM aM :=
      @isUniformAddGroup_of_addCommGroup ℤ gM tM hTM
    let hSM : @UniformContinuousConstSMul ℤ ℤ uM smM :=
      @Submodule.familyBasis_uniformContinuousConstSMul ℤ ℤ Unit rZ gM mM F₀
    let N : @Submodule ℤ ℤ sZ cM mM :=
      @Submodule.span ℤ ℤ sZ cM mM ({2} : Set ℤ)
    let relQ : Setoid ℤ := @Submodule.quotientRel ℤ ℤ rZ gM mM N
    let Q : Type := Quotient relQ
    let gQ : AddCommGroup Q := @Submodule.Quotient.addCommGroup ℤ ℤ rZ gM mM N
    let aQ : AddGroup Q := gQ.toAddGroup
    let cQ : AddCommMonoid Q := gQ.toAddCommMonoid
    let mQ : @Module ℤ Q sZ cQ := @Submodule.Quotient.module ℤ ℤ rZ gM mM N
    let daQ : @DistribMulAction ℤ Q sZ.toMonoid cQ.toAddMonoid :=
      mQ.toDistribMulAction
    let smQ : SMul ℤ Q := daQ.toMulAction.toSMul
    let tQ : TopologicalSpace Q :=
      @QuotientModule.Quotient.topologicalSpace ℤ ℤ rZ gM mM tM N
    let hTQ : @IsTopologicalAddGroup Q tQ aQ :=
      @Submodule.isTopologicalAddGroup_quotient ℤ ℤ rZ gM mM tM N hTM
    let uQ : UniformSpace Q :=
      @IsTopologicalAddGroup.rightUniformSpace Q aQ tQ hTQ
    let hUQ : @IsUniformAddGroup Q uQ aQ :=
      @isUniformAddGroup_of_addCommGroup Q gQ tQ hTQ
    let qL : @LinearMap ℤ ℤ sZ sZ (RingHom.id ℤ) ℤ Q cM cQ mM mQ :=
      @Submodule.mkQ ℤ ℤ rZ gM mM N
    let qCLM : @ContinuousLinearMap ℤ ℤ sZ sZ (RingHom.id ℤ)
        ℤ tM cM Q tQ cQ mM mQ :=
      @Submodule.mkQL ℤ rZ ℤ tM gM mM N
    let q : @ContinuousLinearMap ℤ ℤ sZ sZ (RingHom.id ℤ)
        ℤ uM.toTopologicalSpace cM Q uQ.toTopologicalSpace cQ mM mQ := qCLM
    aM = gM.toAddGroup ∧ cM = gM.toAddCommMonoid ∧
      daM = mM.toDistribMulAction ∧
      smM = mM.toDistribMulAction.toMulAction.toSMul ∧
      uM.toTopologicalSpace = tM ∧
      uM.uniformity = 𝓟 (SetRel.id : Set (ℤ × ℤ)) ∧
      gQ = @Submodule.Quotient.addCommGroup ℤ ℤ rZ gM mM N ∧
      aQ = (@Submodule.Quotient.addCommGroup ℤ ℤ rZ gM mM N).toAddGroup ∧
      cQ = (@Submodule.Quotient.addCommGroup ℤ ℤ rZ gM mM N).toAddCommMonoid ∧
      mQ = @Submodule.Quotient.module ℤ ℤ rZ gM mM N ∧
      daQ = (@Submodule.Quotient.module ℤ ℤ rZ gM mM N).toDistribMulAction ∧
      smQ = (@Submodule.Quotient.module ℤ ℤ rZ gM mM N).toDistribMulAction.toMulAction.toSMul ∧
      tQ = @QuotientModule.Quotient.topologicalSpace ℤ ℤ rZ gM mM tM N ∧
      tQ = @TopologicalSpace.coinduced ℤ Q (@Quotient.mk' ℤ relQ) tM ∧
      uQ = @IsTopologicalAddGroup.rightUniformSpace Q aQ tQ hTQ ∧
      uQ.toTopologicalSpace = tQ ∧
      qCLM = @Submodule.mkQL ℤ rZ ℤ tM gM mM N ∧
      q = qCLM ∧ qCLM.toLinearMap = qL ∧
      qCLM.toLinearMap.toAddMonoidHom = qL.toAddMonoidHom ∧
      qCLM.toLinearMap.toAddHom = qL.toAddHom ∧
      qCLM.toLinearMap.toMulActionHom = qL.toMulActionHom ∧
      qCLM.toFun = @Submodule.Quotient.mk ℤ ℤ rZ gM mM N ∧
      (qCLM : ℤ → Q) = @Submodule.Quotient.mk ℤ ℤ rZ gM mM N ∧
      (∀ (z x : ℤ),
        qCLM.toFun (@SMul.smul ℤ ℤ smM z x) =
          @SMul.smul ℤ Q smQ z (qCLM.toFun x)) ∧
      @IsUniformAddGroup ℤ uM aM ∧ @UniformContinuousConstSMul ℤ ℤ uM smM ∧
      @IsUniformAddGroup Q uQ aQ ∧ @DiscreteTopology Q tQ ∧
      uQ.uniformity = 𝓟 (SetRel.id : Set (Q × Q)) ∧
      @DiscreteUniformity Q uQ ∧ @CompleteSpace Q uQ ∧
      @T0Space Q uQ.toTopologicalSpace ∧ @UniformContinuousConstSMul ℤ Q uQ smQ ∧
      Function.Surjective (qCLM : ℤ → Q) ∧
      @Topology.IsQuotientMap ℤ Q tM tQ (qCLM : ℤ → Q) ∧
      qL.ker = N ∧ qCLM 2 = 0 ∧ qCLM 1 ≠ 0 ∧ (2 : ℤ) ∈ N ∧ (1 : ℤ) ∉ N ∧
      ∃ (h0Q : @T0Space Q uQ.toTopologicalSpace) (hCQ : @CompleteSpace Q uQ)
        (hSQ : @UniformContinuousConstSMul ℤ Q uQ smQ),
      let C : Type := @UniformSpace.Completion ℤ uM
      let uC : UniformSpace C := @UniformSpace.Completion.uniformSpace ℤ uM
      let gC : AddCommGroup C := @UniformSpace.Completion.instAddCommGroup ℤ uM gM hUM
      let aC : AddGroup C := gC.toAddGroup
      let cC : AddCommMonoid C := gC.toAddCommMonoid
      let mC : @Module ℤ C sZ cC :=
        @UniformSpace.Completion.instModule (R := ℤ) (α := ℤ) uM gM hUM sZ mM hSM
      let daC : @DistribMulAction ℤ C sZ.toMonoid cC.toAddMonoid :=
        mC.toDistribMulAction
      let smC : SMul ℤ C := daC.toMulAction.toSMul
      let κ : @ContinuousLinearMap ℤ ℤ sZ sZ (RingHom.id ℤ)
          ℤ uM.toTopologicalSpace cM C uC.toTopologicalSpace cC mM mC :=
        @UniformSpace.Completion.toComplL (α := ℤ) (S := ℤ) uM gM hUM sZ mM hSM
      let κL := κ.toLinearMap
      let F : @ContinuousLinearMap ℤ ℤ sZ sZ (RingHom.id ℤ)
          C uC.toTopologicalSpace cC Q uQ.toTopologicalSpace cQ mC mQ :=
        @ContinuousLinearMap.fromCompletion (α := ℤ) (β := Q) (R := ℤ) (S := ℤ)
          uM gM hUM sZ mM hSM sZ uQ gQ hUQ mQ hSQ (σ := RingHom.id ℤ) h0Q hCQ q
      let fL := F.toLinearMap
      let K : @Submodule ℤ C sZ cC mC := fL.ker
      let relP : Setoid C := @Submodule.quotientRel ℤ C rZ gC mC K
      let P : Type := Quotient relP
      let gP : AddCommGroup P := @Submodule.Quotient.addCommGroup ℤ C rZ gC mC K
      let aP : AddGroup P := gP.toAddGroup
      let cP : AddCommMonoid P := gP.toAddCommMonoid
      let mP : @Module ℤ P sZ cP := @Submodule.Quotient.module ℤ C rZ gC mC K
      let daP : @DistribMulAction ℤ P sZ.toMonoid cP.toAddMonoid :=
        mP.toDistribMulAction
      let smP : SMul ℤ P := daP.toMulAction.toSMul
      let tP : TopologicalSpace P :=
        @QuotientModule.Quotient.topologicalSpace ℤ C rZ gC mC uC.toTopologicalSpace K
      let π : @LinearMap ℤ ℤ sZ sZ (RingHom.id ℤ) C P cC cP mC mP :=
        @Submodule.mkQ ℤ C rZ gC mC K
      q = @Submodule.mkQL ℤ rZ ℤ tM gM mM N ∧
        q.toLinearMap = @Submodule.mkQ ℤ ℤ rZ gM mM N ∧
        uC = @UniformSpace.Completion.uniformSpace ℤ uM ∧
        gC = @UniformSpace.Completion.instAddCommGroup ℤ uM gM hUM ∧
        aC = gC.toAddGroup ∧ cC = gC.toAddCommMonoid ∧
        mC = @UniformSpace.Completion.instModule (R := ℤ) (α := ℤ) uM gM hUM sZ mM hSM ∧
        daC = mC.toDistribMulAction ∧
        smC = mC.toDistribMulAction.toMulAction.toSMul ∧
        κ = @UniformSpace.Completion.toComplL (α := ℤ) (S := ℤ) uM gM hUM sZ mM hSM ∧
        κ.toLinearMap = κL ∧
        κ.toLinearMap.toAddMonoidHom = κL.toAddMonoidHom ∧
        κ.toLinearMap.toAddHom = κL.toAddHom ∧
        κ.toLinearMap.toMulActionHom = κL.toMulActionHom ∧
        κ.toFun = (κL : ℤ → C) ∧ (κ : ℤ → C) = (κL : ℤ → C) ∧
        F = @ContinuousLinearMap.fromCompletion (α := ℤ) (β := Q) (R := ℤ) (S := ℤ)
          uM gM hUM sZ mM hSM sZ uQ gQ hUQ mQ hSQ (σ := RingHom.id ℤ) h0Q hCQ q ∧
        F.toLinearMap = fL ∧
        F.toLinearMap.toAddMonoidHom = fL.toAddMonoidHom ∧
        F.toLinearMap.toAddHom = fL.toAddHom ∧
        F.toLinearMap.toMulActionHom = fL.toMulActionHom ∧
        F.toFun = (fL : C → Q) ∧ (F : C → Q) = (fL : C → Q) ∧
        (∀ (z : ℤ) (x : C),
          F.toFun (@SMul.smul ℤ C smC z x) = @SMul.smul ℤ Q smQ z (F.toFun x)) ∧
        K = F.toLinearMap.ker ∧
        gP = @Submodule.Quotient.addCommGroup ℤ C rZ gC mC K ∧
        aP = (@Submodule.Quotient.addCommGroup ℤ C rZ gC mC K).toAddGroup ∧
        cP = (@Submodule.Quotient.addCommGroup ℤ C rZ gC mC K).toAddCommMonoid ∧
        mP = @Submodule.Quotient.module ℤ C rZ gC mC K ∧
        daP = (@Submodule.Quotient.module ℤ C rZ gC mC K).toDistribMulAction ∧
        smP = (@Submodule.Quotient.module ℤ C rZ gC mC K).toDistribMulAction.toMulAction.toSMul ∧
        tP = @QuotientModule.Quotient.topologicalSpace ℤ C rZ gC mC uC.toTopologicalSpace K ∧
        tP = @TopologicalSpace.coinduced C P (@Quotient.mk' C relP) uC.toTopologicalSpace ∧
        π = @Submodule.mkQ ℤ C rZ gC mC K ∧
        π.toAddMonoidHom = (@Submodule.mkQ ℤ C rZ gC mC K).toAddMonoidHom ∧
        π.toAddHom = (@Submodule.mkQ ℤ C rZ gC mC K).toAddHom ∧
        π.toMulActionHom = (@Submodule.mkQ ℤ C rZ gC mC K).toMulActionHom ∧
        π.toFun = @Submodule.Quotient.mk ℤ C rZ gC mC K ∧
        (π : C → P) = @Submodule.Quotient.mk ℤ C rZ gC mC K ∧
        (∀ (z : ℤ) (x : C),
          π.toFun (@SMul.smul ℤ C smC z x) = @SMul.smul ℤ P smP z (π.toFun x)) ∧
        F.comp κ = q ∧ (F : C → Q) ∘ (κ : ℤ → C) = (q : ℤ → Q) ∧
        (K : Set C) = @closure C uC.toTopologicalSpace (κ '' (N : Set ℤ)) ∧
        ∃ hFquot : @Topology.IsQuotientMap C Q uC.toTopologicalSpace
            uQ.toTopologicalSpace (F : C → Q),
        let e : @LinearEquiv ℤ ℤ sZ sZ (RingHom.id ℤ) (RingHom.id ℤ)
            inferInstance inferInstance P Q cP cQ mP mQ :=
          @LinearMap.quotKerEquivOfSurjective ℤ C Q rZ gC gQ mC mQ fL hFquot.surjective
        let eL := e.toLinearMap
        let eiL := e.symm.toLinearMap
        let eA := e.toAddEquiv
        let eiA := e.symm.toAddEquiv
        e = @LinearMap.quotKerEquivOfSurjective ℤ C Q rZ gC gQ mC mQ fL
            hFquot.surjective ∧
          e.symm = (@LinearMap.quotKerEquivOfSurjective ℤ C Q rZ gC gQ mC mQ fL
            hFquot.surjective).symm ∧
          e.toLinearMap = eL ∧ e.symm.toLinearMap = eiL ∧
          e.toAddEquiv = eA ∧ e.symm.toAddEquiv = eiA ∧
          e.toLinearMap.toMulActionHom = eL.toMulActionHom ∧
          e.symm.toLinearMap.toMulActionHom = eiL.toMulActionHom ∧
          e.toLinearMap.toAddMonoidHom = e.toAddEquiv.toAddMonoidHom ∧
          e.toLinearMap.toAddHom = e.toAddEquiv.toAddHom ∧
          e.toLinearMap.toMulActionHom.toFun = e.toFun ∧
          e.toLinearMap.toFun = e.toFun ∧ (e.toLinearMap : P → Q) = (e : P → Q) ∧
          e.symm.toLinearMap.toAddMonoidHom = e.symm.toAddEquiv.toAddMonoidHom ∧
          e.symm.toLinearMap.toAddHom = e.symm.toAddEquiv.toAddHom ∧
          e.symm.toLinearMap.toMulActionHom.toFun = e.symm.toFun ∧
          e.symm.toLinearMap.toFun = e.symm.toFun ∧
          (e.symm.toLinearMap : Q → P) = (e.symm : Q → P) ∧
          @IsHomeomorph P Q tP uQ.toTopologicalSpace (e : P → Q) ∧
          @Continuous Q P uQ.toTopologicalSpace tP (e.symm : Q → P) ∧
          e.toLinearMap.comp π = F.toLinearMap ∧
          e.symm.toLinearMap.comp F.toLinearMap = π ∧
          e.toLinearMap.comp (π.comp κ.toLinearMap) = qL ∧
          e.symm.toLinearMap.comp qL = π.comp κ.toLinearMap ∧
          (e : P → Q) ∘ (π : C → P) = (F : C → Q) ∧
          (e.symm : Q → P) ∘ (F : C → Q) = (π : C → P) ∧
          (e : P → Q) ∘ (π : C → P) ∘ (κ : ℤ → C) = (q : ℤ → Q) ∧
          (e.symm : Q → P) ∘ (q : ℤ → Q) = (π : C → P) ∘ (κ : ℤ → C) := by
  intro rZ sZ gM aM cM mM daM smM F₀ H₀ B₀ tM hTM uM hUM hSM N relQ Q
    gQ aQ cQ mQ daQ smQ tQ hTQ uQ hUQ qL qCLM q
  have hnM : @nhds ℤ tM 0 = 𝓟 ({0} : Set ℤ) := by
    simpa [H₀, F₀, Submodule.bot_toAddSubgroup] using
      (@AddSubgroup.familyBasis_nhds_zero_eq_iInf ℤ Unit gM H₀)
  have huM : uM.uniformity = 𝓟 (SetRel.id : Set (ℤ × ℤ)) := by
    change Filter.comap (fun p : ℤ × ℤ => p.2 + -p.1) (@nhds ℤ tM 0) = _
    rw [hnM, Filter.comap_principal]
    congr 1
    ext p
    simp [SetRel.id, add_neg_eq_zero, eq_comm]
  have heM : uM = ⊥ := UniformSpace.ext huM
  have htM : tM = ⊥ := congrArg (@UniformSpace.toTopologicalSpace ℤ) heM
  have htQ : tQ = ⊥ := by
    change @TopologicalSpace.coinduced ℤ Q (@Quotient.mk' ℤ relQ) tM = ⊥
    rw [htM, coinduced_bot]
  have hDQ : @DiscreteTopology Q tQ := ⟨htQ⟩
  have hnQ : @nhds Q tQ 0 = 𝓟 ({0} : Set Q) := by
    rw [@nhds_discrete Q tQ hDQ]
    ext s
    simp
  have hRQ : @IsRightUniformAddGroup Q uQ aQ :=
    @IsUniformAddGroup.isRightUniformAddGroup Q uQ aQ hUQ
  have huQ : uQ.uniformity = 𝓟 (SetRel.id : Set (Q × Q)) := by
    calc
      uQ.uniformity =
          Filter.comap (fun p : Q × Q => p.2 - p.1) (@nhds Q tQ 0) :=
        @uniformity_eq_comap_nhds_zero Q uQ aQ hRQ
      _ = 𝓟 (SetRel.id : Set (Q × Q)) := by
        rw [hnQ, Filter.comap_principal]
        congr 1
        ext p
        simp [SetRel.id, sub_eq_zero, eq_comm]
  have hDUQ : @DiscreteUniformity Q uQ :=
    (@discreteUniformity_iff_eq_principal_setRelId Q uQ).mpr huQ
  have hCQ : @CompleteSpace Q uQ := inferInstance
  have h0Q : @T0Space Q uQ.toTopologicalSpace := inferInstance
  have hSQ : @UniformContinuousConstSMul ℤ Q uQ smQ := by
    constructor
    intro z
    exact @DiscreteUniformity.uniformContinuous Q uQ hDUQ Q uQ
      (fun x => @SMul.smul ℤ Q smQ z x)
  have hTwo : (2 : ℤ) ∈ N :=
    @Submodule.mem_span_singleton_self ℤ ℤ sZ cM mM 2
  have hOne : (1 : ℤ) ∉ N := by
    intro h
    obtain ⟨a, ha⟩ := (@Submodule.mem_span_singleton ℤ ℤ sZ cM mM 1 2).mp h
    have hd : (2 : ℤ) ∣ 1 := ⟨a, by simpa only [smul_eq_mul, mul_comm] using ha.symm⟩
    norm_num at hd
  have hqTwo : qCLM 2 = 0 :=
    (@Submodule.Quotient.mk_eq_zero ℤ ℤ 2 rZ gM mM N).mpr hTwo
  have hqOne : qCLM 1 ≠ 0 := by
    intro h
    exact hOne ((@Submodule.Quotient.mk_eq_zero ℤ ℤ 1 rZ gM mM N).mp h)
  refine ⟨rfl, rfl, rfl, rfl, rfl, huM, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hUM, hSM, hUQ, hDQ,
    huQ, hDUQ, hCQ, h0Q, hSQ, ?_, ?_, ?_, hqTwo, hqOne, hTwo, hOne, ?_⟩
  · intro z x
    exact qCLM.toLinearMap.map_smul' z x
  · exact @Submodule.mkQ_surjective ℤ ℤ rZ gM mM N
  · exact @Submodule.isQuotientMap_mkQL ℤ rZ ℤ tM gM mM N
  · exact @Submodule.ker_mkQ ℤ ℤ rZ gM mM N
  · refine ⟨h0Q, hCQ, hSQ, ?_⟩
    intro C uC gC aC cC mC daC smC κ κL F fL K relP P gP aP cP mP daP smP tP π
    have hq : @Topology.IsQuotientMap ℤ Q uM.toTopologicalSpace
        uQ.toTopologicalSpace (q : ℤ → Q) :=
      @Submodule.isQuotientMap_mkQL ℤ rZ ℤ tM gM mM N
    have hFκ : F.comp κ = q :=
      @ContinuousLinearMap.fromCompletion_comp_toComplL ℤ ℤ ℤ Q sZ sZ uM uQ
        gM gQ mM mQ hUM hUQ hSM hSQ h0Q hCQ (RingHom.id ℤ) q
    have hFκfun : (F : C → Q) ∘ (κ : ℤ → C) = (q : ℤ → Q) := by
      funext x
      exact DFunLike.congr_fun hFκ x
    have hqker : q.toLinearMap.ker = N := @Submodule.ker_mkQ ℤ ℤ rZ gM mM N
    have hker : (K : Set C) = @closure C uC.toTopologicalSpace (κ '' (N : Set ℤ)) := by
      simpa only [hqker] using
        (@ContinuousLinearMap.ker_fromCompletion ℤ ℤ ℤ Q sZ sZ uM uQ gM gQ mM mQ
          hUM hUQ hSM hSQ h0Q hCQ (RingHom.id ℤ) q hq)
    have hFquot : @Topology.IsQuotientMap C Q uC.toTopologicalSpace
        uQ.toTopologicalSpace (F : C → Q) := by
      apply Topology.IsQuotientMap.of_comp κ.continuous F.continuous
      rw [hFκfun]
      exact hq
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro z x
      exact F.toLinearMap.map_smul' z x
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, ?_, hFκ, hFκfun, hker, hFquot, ?_⟩
    · intro z x
      exact π.map_smul' z x
    intro e eL eiL eA eiA
    have hπquot : @Topology.IsQuotientMap C P uC.toTopologicalSpace tP (π : C → P) :=
      @Submodule.isQuotientMap_mkQ ℤ C rZ gC mC uC.toTopologicalSpace K
    have hπcont : @Continuous C P uC.toTopologicalSpace tP (π : C → P) :=
      @Submodule.continuous_mkQ ℤ C rZ gC mC uC.toTopologicalSpace K
    have heπ : e.toLinearMap.comp π = F.toLinearMap := by
      ext x
      exact @LinearMap.quotKerEquivOfSurjective_apply_mk ℤ C Q rZ gC gQ mC mQ fL
        hFquot.surjective x
    have heinF : e.symm.toLinearMap.comp F.toLinearMap = π := by
      ext x
      exact @LinearMap.quotKerEquivOfSurjective_symm_apply ℤ C Q rZ gC gQ mC mQ fL
        hFquot.surjective x
    have heπfun : (e : P → Q) ∘ (π : C → P) = (F : C → Q) := by
      funext x
      exact DFunLike.congr_fun heπ x
    have heinFfun : (e.symm : Q → P) ∘ (F : C → Q) = (π : C → P) := by
      funext x
      exact DFunLike.congr_fun heinF x
    have hecont : @Continuous P Q tP uQ.toTopologicalSpace (e : P → Q) := by
      apply hπquot.continuous_iff.mpr
      rw [heπfun]
      exact F.continuous
    have hequot : @Topology.IsQuotientMap P Q tP uQ.toTopologicalSpace (e : P → Q) := by
      apply Topology.IsQuotientMap.of_comp hπcont hecont
      rw [heπfun]
      exact hFquot
    have hehomeo : @IsHomeomorph P Q tP uQ.toTopologicalSpace (e : P → Q) :=
      isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hequot, e.injective⟩
    have heincont : @Continuous Q P uQ.toTopologicalSpace tP (e.symm : Q → P) := by
      apply hFquot.continuous_iff.mpr
      rw [heinFfun]
      exact hπcont
    have heπκ : e.toLinearMap.comp (π.comp κ.toLinearMap) = qL := by
      apply LinearMap.ext
      intro x
      calc
        e (π (κ x)) = F (κ x) := DFunLike.congr_fun heπ (κ x)
        _ = q x := DFunLike.congr_fun hFκ x
    have heinq : e.symm.toLinearMap.comp qL = π.comp κ.toLinearMap := by
      apply LinearMap.ext
      intro x
      calc
        e.symm (q x) = e.symm (F (κ x)) :=
          congrArg (fun y => e.symm y) (DFunLike.congr_fun hFκ x).symm
        _ = π (κ x) := DFunLike.congr_fun heinF (κ x)
    have heπκfun : (e : P → Q) ∘ (π : C → P) ∘ (κ : ℤ → C) = (q : ℤ → Q) := by
      funext x
      exact DFunLike.congr_fun heπκ x
    have heinqfun : (e.symm : Q → P) ∘ (q : ℤ → Q) =
        (π : C → P) ∘ (κ : ℤ → C) := by
      funext x
      exact DFunLike.congr_fun heinq x
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, hehomeo, heincont, heπ, heinF, heπκ, heinq, heπfun, heinFfun, heπκfun,
      heinqfun⟩
