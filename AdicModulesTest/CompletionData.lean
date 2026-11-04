/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Topology.Algebra.Module.Completion

/-!
# Completion module data and scalar compatibility

These checks compare full algebraic and uniform records, as well as scalar-action
records and functions, before and after supplying uniform continuity. They also check
scalar towers, commuting actions, and iteration of completion without topologies on
the scalar semirings. The module-record helpers adapt Formal Frontier Agents' full-data
checks for Hausdorff completions.
-/

universe u v w

namespace UniformSpace.Completion

/-- Wrapping an observed class record prevents it from becoming a local instance
while later fields of a snapshot are elaborated. -/
private structure Frozen (A : Sort u) where
  val : A

section Records

variable {R : Type u} {X : Type v}
variable [sR : Semiring R] [aX : AddCommGroup X]
variable [mX : Module R X] [uX : UniformSpace X]

-- These selectors are elaborated with the original dictionaries, outside snapshots.
private abbrev moduleSMul : SMul R X := inferInstance

private abbrev moduleDistribMulAction
    (moduleRecord : @Module R X sR (@AddCommGroup.toAddCommMonoid X aX)) :
    @DistribMulAction R X (@Semiring.toMonoid R sR)
      (@AddCommMonoid.toAddMonoid X (@AddCommGroup.toAddCommMonoid X aX)) :=
  moduleRecord.toDistribMulAction

private structure ModuleRecords where
  scalar : Frozen (Semiring R)
  scalarAdd : Frozen (AddCommMonoid R)
  scalarMul : Frozen (MonoidWithZero R)
  scalarNonUnital : Frozen (NonUnitalSemiring R)
  scalarNonAssoc : Frozen (NonAssocSemiring R)
  group : Frozen (AddCommGroup X)
  addGroup : Frozen (AddGroup X)
  addMonoid : Frozen (AddCommMonoid X)
  moduleRecord : Frozen (@Module R X sR (@AddCommGroup.toAddCommMonoid X aX))
  moduleAction : Frozen
    (@DistribMulAction R X (@Semiring.toMonoid R sR)
      (@AddCommMonoid.toAddMonoid X (@AddCommGroup.toAddCommMonoid X aX)))
  scalarAction : Frozen (SMul R X)
  action : R → X → X
  uniform : Frozen (UniformSpace X)
  topology : Frozen (TopologicalSpace X)

private def captureModuleRecords :
    ModuleRecords (R := R) (X := X) (sR := sR) (aX := aX) where
  scalar := ⟨sR⟩
  scalarAdd := ⟨@Semiring.toAddCommMonoid R sR⟩
  scalarMul := ⟨@Semiring.toMonoidWithZero R sR⟩
  scalarNonUnital := ⟨@Semiring.toNonUnitalSemiring R sR⟩
  scalarNonAssoc := ⟨@Semiring.toNonAssocSemiring R sR⟩
  group := ⟨aX⟩
  addGroup := ⟨@AddCommGroup.toAddGroup X aX⟩
  addMonoid := ⟨@AddCommGroup.toAddCommMonoid X aX⟩
  moduleRecord := ⟨mX⟩
  moduleAction := ⟨moduleDistribMulAction (sR := sR) (aX := aX) mX⟩
  scalarAction := ⟨moduleSMul (sR := sR) (aX := aX) (mX := mX)⟩
  action := @SMul.smul R X (moduleSMul (sR := sR) (aX := aX) (mX := mX))
  uniform := ⟨uX⟩
  topology := ⟨@UniformSpace.toTopologicalSpace X uX⟩

end Records

section CompletionRecords

variable {R : Type u} {M : Type v}
variable [sR : Semiring R] [aM : AddCommGroup M] [mM : Module R M]
variable [uM : UniformSpace M] [iM : IsUniformAddGroup M]

-- Freeze the target structures before introducing either continuity hypothesis.
private noncomputable abbrev completedGroup : AddCommGroup (Completion M) :=
  instAddCommGroup (α := M)

private abbrev completedUniform : UniformSpace (Completion M) := inferInstance

private noncomputable abbrev completedSMul : SMul R (Completion M) :=
  instSMul (M := R) (X := M)

private abbrev completedUniformConstSMul : Prop :=
  UniformContinuousConstSMul R (Completion M)

private abbrev completedContinuousConstSMul : Prop :=
  ContinuousConstSMul R (Completion M)

private structure CompletionRecords where
  source : ModuleRecords (R := R) (X := M) (sR := sR) (aX := aM)
  sourceUniformAdd : Frozen (IsUniformAddGroup M)
  sourceContinuous : Frozen (ContinuousConstSMul R M)
  completed : ModuleRecords (R := R) (X := Completion M) (sR := sR)
    (aX := completedGroup (M := M))
  inheritedSMul : Frozen (SMul R (Completion M))
  inheritedAction : R → Completion M → Completion M
  targetUniform : Frozen (completedUniformConstSMul (R := R) (M := M))
  targetContinuous : Frozen (completedContinuousConstSMul (R := R) (M := M))
  iterated : ModuleRecords (R := R) (X := Completion (Completion M)) (sR := sR)
    (aX := completedGroup (M := Completion M))

variable [cM : ContinuousConstSMul R M]

-- The argument is a value, not an instance: it cannot change any other dictionary.
private noncomputable def captureCompletionRecords
    (mC : @Module R (Completion M) sR
      (@AddCommGroup.toAddCommMonoid (Completion M) (completedGroup (M := M))))
    (mCC : @Module R (Completion (Completion M)) sR
      (@AddCommGroup.toAddCommMonoid (Completion (Completion M))
        (completedGroup (M := Completion M)))) :
    CompletionRecords (R := R) (M := M) where
  source := captureModuleRecords
    (sR := sR) (aX := aM) (mX := mM) (uX := uM)
  sourceUniformAdd := ⟨iM⟩
  sourceContinuous := ⟨cM⟩
  completed := captureModuleRecords (sR := sR)
    (aX := completedGroup (M := M)) (mX := mC)
    (uX := completedUniform (M := M))
  inheritedSMul := ⟨moduleSMul (sR := sR)
    (aX := completedGroup (M := M)) (mX := mC)⟩
  inheritedAction := @SMul.smul R (Completion M)
    (moduleSMul (sR := sR) (aX := completedGroup (M := M)) (mX := mC))
  targetUniform := ⟨inferInstance⟩
  targetContinuous := ⟨inferInstance⟩
  iterated := captureModuleRecords (sR := sR)
    (aX := completedGroup (M := Completion M))
    (mX := mCC) (uX := completedUniform (M := Completion M))

-- Instance search here has only continuity on the original module.
private noncomputable def continuousRecords : CompletionRecords (R := R) (M := M) :=
  captureCompletionRecords (inferInstance : Module R (Completion M))
    (inferInstance : Module R (Completion (Completion M)))

-- Supplying a proposition changes instance search, but not the observed data.
private noncomputable def uniformRecords (h : UniformContinuousConstSMul R M) :
    CompletionRecords (R := R) (M := M) := by
  letI := h
  exact captureCompletionRecords (inferInstance : Module R (Completion M))
    (inferInstance : Module R (Completion (Completion M)))

private noncomputable abbrev canonicalModule (h : UniformContinuousConstSMul R M) :
    Module R (Completion M) := by
  letI := h
  exact instModule (R := R) (α := M)

/-- The public whole-module bridge also identifies snapshots containing all original
records, all completed records, and the automatically available iterated module. -/
private theorem records_eq (h : UniformContinuousConstSMul R M) :
    continuousRecords (R := R) (M := M) = uniformRecords h := by
  let := h
  change captureCompletionRecords (instModuleOfContinuousConstSMul (R := R) (M := M))
      (instModule (R := R) (α := Completion M)) =
    captureCompletionRecords (instModule (R := R) (α := M))
      (instModule (R := R) (α := Completion M))
  exact congrArg
    (fun m => captureCompletionRecords m (instModule (R := R) (α := Completion M)))
    (instModuleOfContinuousConstSMul_eq_instModule (R := R) (M := M))

/-- Full module and action records agree with the completion construction. The last
control uses the canonical module on the second completion; its synthesis needs no
uniform-continuity assumption on the original module. -/
private theorem continuous_data (h : UniformContinuousConstSMul R M) :
    (continuousRecords (R := R) (M := M)).source =
      captureModuleRecords (sR := sR) (aX := aM) (mX := mM) (uX := uM) ∧
    (continuousRecords (R := R) (M := M)).completed.moduleRecord.val = canonicalModule h ∧
    (continuousRecords (R := R) (M := M)).inheritedSMul.val =
      completedSMul (R := R) (M := M) ∧
    (continuousRecords (R := R) (M := M)).inheritedAction =
      @SMul.smul R (Completion M) (completedSMul (R := R) (M := M)) ∧
    (continuousRecords (R := R) (M := M)).iterated.moduleRecord.val =
      instModule (R := R) (α := Completion M) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

omit cM in
/-- Under the original uniform-continuity hypothesis, higher-priority instance search
returns the same entire module and the same inherited scalar-action record. -/
private theorem uniform_data [UniformContinuousConstSMul R M] :
    (inferInstance : Module R (Completion M)) = instModule (R := R) (α := M) ∧
    moduleSMul (sR := sR) (aX := completedGroup (M := M))
      (mX := (inferInstance : Module R (Completion M))) =
      instSMul (M := R) (X := M) := by
  exact ⟨rfl, rfl⟩

/-- Both endpoints of scalar multiplication use the unchanged source action and the
inherited completed-module action. This uses only a locally derived proposition. -/
private theorem continuous_endpoints (r : R) (m : M) (x : Completion M) :
    (↑(r • m) : Completion M) =
      (continuousRecords (R := R) (M := M)).inheritedAction r (m : Completion M) ∧
    (↑((continuousRecords (R := R) (M := M)).inheritedAction r x) :
      Completion (Completion M)) =
      (continuousRecords (R := R) (M := M)).iterated.action r
        (x : Completion (Completion M)) := by
  let : UniformContinuousConstSMul R M :=
    uniformContinuousConstSMul_of_continuousConstSMul R M
  exact ⟨coe_smul r m, coe_smul r x⟩

end CompletionRecords

section TwoScalars

variable {S : Type u} {R : Type v} {M : Type w}
variable [sS : Semiring S] [sR : Semiring R] [aM : AddCommGroup M]
variable [mS : Module S M] [mR : Module R M]
variable [uM : UniformSpace M] [iM : IsUniformAddGroup M]

section Tower

variable [sr : SMul S R]

private structure TowerRecords where
  left : CompletionRecords (R := S) (M := M)
  right : CompletionRecords (R := R) (M := M)
  scalarAction : Frozen (SMul S R)
  scalarFunction : S → R → R
  sourceTower : Frozen (IsScalarTower S R M)

variable [t : IsScalarTower S R M]

/-- With source uniform continuity already available, the inherited module actions
satisfy the existing completion scalar-tower theorem. -/
private theorem uniform_tower
    [UniformContinuousConstSMul S M] [UniformContinuousConstSMul R M] :
    @IsScalarTower S R (Completion M) sr
      (moduleSMul (sR := sR) (aX := completedGroup (M := M))
        (mX := (inferInstance : Module R (Completion M))))
      (moduleSMul (sR := sS) (aX := completedGroup (M := M))
        (mX := (inferInstance : Module S (Completion M)))) :=
  instIsScalarTower (M := S) (N := R) (X := M)

variable [cS : ContinuousConstSMul S M] [cR : ContinuousConstSMul R M]

private noncomputable def continuousTowerRecords : TowerRecords (S := S) (R := R) (M := M) where
  left := continuousRecords (sR := sS) (aM := aM) (mM := mS)
    (uM := uM) (iM := iM) (cM := cS)
  right := continuousRecords (sR := sR) (aM := aM) (mM := mR)
    (uM := uM) (iM := iM) (cM := cR)
  scalarAction := ⟨sr⟩
  scalarFunction := @SMul.smul S R sr
  sourceTower := ⟨t⟩

private noncomputable def uniformTowerRecords
    (hS : UniformContinuousConstSMul S M) (hR : UniformContinuousConstSMul R M) :
    TowerRecords (S := S) (R := R) (M := M) := by
  letI := hS
  letI := hR
  exact {
    left := captureCompletionRecords (sR := sS) (aM := aM) (mM := mS)
      (uM := uM) (iM := iM) (cM := cS) (inferInstance : Module S (Completion M))
      (inferInstance : Module S (Completion (Completion M)))
    right := captureCompletionRecords (sR := sR) (aM := aM) (mM := mR)
      (uM := uM) (iM := iM) (cM := cR) (inferInstance : Module R (Completion M))
      (inferInstance : Module R (Completion (Completion M)))
    scalarAction := ⟨sr⟩
    scalarFunction := @SMul.smul S R sr
    sourceTower := ⟨t⟩ }

/-- Deriving only uniform-continuity propositions preserves both full snapshots and
the original action on scalars, and proves the tower for the inherited module actions. -/
private theorem continuous_tower :
    continuousTowerRecords (S := S) (R := R) (M := M) =
      uniformTowerRecords
        (uniformContinuousConstSMul_of_continuousConstSMul S M)
        (uniformContinuousConstSMul_of_continuousConstSMul R M) ∧
    @IsScalarTower S R (Completion M) sr
      (continuousRecords (R := R) (M := M)).inheritedSMul.val
      (continuousRecords (R := S) (M := M)).inheritedSMul.val := by
  let : UniformContinuousConstSMul S M :=
    uniformContinuousConstSMul_of_continuousConstSMul S M
  let : UniformContinuousConstSMul R M :=
    uniformContinuousConstSMul_of_continuousConstSMul R M
  exact ⟨rfl, instIsScalarTower (M := S) (N := R) (X := M)⟩

end Tower

section Commuting

private structure CommRecords where
  left : CompletionRecords (R := S) (M := M)
  right : CompletionRecords (R := R) (M := M)
  sourceComm : Frozen (SMulCommClass S R M)

variable [c : SMulCommClass S R M]

/-- The existing commutation theorem applies to the full inherited module actions
under source uniform continuity, without an action of one scalar semiring on the other. -/
private theorem uniform_comm
    [UniformContinuousConstSMul S M] [UniformContinuousConstSMul R M] :
    @SMulCommClass S R (Completion M)
      (moduleSMul (sR := sS) (aX := completedGroup (M := M))
        (mX := (inferInstance : Module S (Completion M))))
      (moduleSMul (sR := sR) (aX := completedGroup (M := M))
        (mX := (inferInstance : Module R (Completion M)))) :=
  inferInstance

variable [cS : ContinuousConstSMul S M] [cR : ContinuousConstSMul R M]

private noncomputable def continuousCommRecords : CommRecords (S := S) (R := R) (M := M) where
  left := continuousRecords (sR := sS) (aM := aM) (mM := mS)
    (uM := uM) (iM := iM) (cM := cS)
  right := continuousRecords (sR := sR) (aM := aM) (mM := mR)
    (uM := uM) (iM := iM) (cM := cR)
  sourceComm := ⟨c⟩

private noncomputable def uniformCommRecords
    (hS : UniformContinuousConstSMul S M) (hR : UniformContinuousConstSMul R M) :
    CommRecords (S := S) (R := R) (M := M) := by
  letI := hS
  letI := hR
  exact {
    left := captureCompletionRecords (sR := sS) (aM := aM) (mM := mS)
      (uM := uM) (iM := iM) (cM := cS) (inferInstance : Module S (Completion M))
      (inferInstance : Module S (Completion (Completion M)))
    right := captureCompletionRecords (sR := sR) (aM := aM) (mM := mR)
      (uM := uM) (iM := iM) (cM := cR) (inferInstance : Module R (Completion M))
      (inferInstance : Module R (Completion (Completion M)))
    sourceComm := ⟨c⟩ }

/-- Under continuity alone, supplementing propositions proves commutation on the
unchanged completed modules and leaves all original records unchanged. -/
private theorem continuous_comm :
    continuousCommRecords (S := S) (R := R) (M := M) =
      uniformCommRecords
        (uniformContinuousConstSMul_of_continuousConstSMul S M)
        (uniformContinuousConstSMul_of_continuousConstSMul R M) ∧
    @SMulCommClass S R (Completion M)
      (continuousRecords (R := S) (M := M)).inheritedSMul.val
      (continuousRecords (R := R) (M := M)).inheritedSMul.val := by
  let : UniformContinuousConstSMul S M :=
    uniformContinuousConstSMul_of_continuousConstSMul S M
  let : UniformContinuousConstSMul R M :=
    uniformContinuousConstSMul_of_continuousConstSMul R M
  exact ⟨rfl, uniform_comm (S := S) (R := R) (M := M)⟩

end Commuting

end TwoScalars

end UniformSpace.Completion
