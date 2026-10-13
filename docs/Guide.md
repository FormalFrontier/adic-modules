# Using adic-modules

This library builds on mathlib's ideals, modules, canonical integer actions,
inverse-limit adic completion, valuations, localization and uniform-space
completion. Import `AdicModules` for the public producer API, or import a narrower
module below. The files under `AdicModulesTest` contain downstream uses and
separately importable named concrete model results. These models are not
re-exported by `AdicModules`. The aggregate `AdicModulesTest.Axioms` is
import-only and performs no axiom census; proof checking requires a transitive
audit of all declarations, including private, generated and test declarations.

## Uniform bounded torsion

`Module.IsKilledByIdealPower R M I` means that **one exponent works for the
whole module**: some power of `I` annihilates every element. This is stronger
than choosing an exponent separately for each element. The finite-module bridge
identifies the uniform condition with `Ideal.primaryComponent M I = ⊤` under
`Module.Finite R M`; do not drop that hypothesis.

The [bounded-torsion module](../AdicModules/BoundedIdealPowerTorsion.lean)
provides monotonicity, submodule, surjection, quotient and extension lemmas.
For a submodule killed by `I ^ n` and quotient killed by `I ^ m`, the explicit
extension lemma uses exponent `n + m`. The
[ordinary-import client](../AdicModulesTest/BoundedIdealPowerTorsion.lean)
shows both the specified-exponent and existential-bounded interfaces.

The [primary-component module](../AdicModules/PrimaryComponent.lean) instead
works with element-dependent ideal powers. For an exact pair of modules over a
Dedekind domain, its height-one component maps are exact if the **source** is
torsion; no other torsion, finiteness or uniform exponent premise is present.
For abelian groups, the integer prime `(p)` has the ordinary `p`-primary
subgroup as its component, and maps restricted to these ordinary subgroups
are exact when the source group is torsion. Read the
[manual reference](PrimaryComponent.md) and its
[ordinary-import client](../AdicModulesTest/PrimaryComponent.lean) for signatures.

## Restricting scalars in adic completions

Import [`AdicModules.AdicCompletion.RestrictScalars`](../AdicModules/AdicCompletion/RestrictScalars.lean)
alone or the `AdicModules` public root. For commutative rings `R` and `S`, an
`Algebra R S`, an additive commutative group `M` carrying compatible `R`- and
`S`-module structures with `IsScalarTower R S M`, and any `I : Ideal R`, the
native inverse-limit completions are equivalent as `R`-modules:

```lean
AdicCompletion.restrictScalarsEquiv I M :
  AdicCompletion (I.map (algebraMap R S)) M ≃ₗ[R] AdicCompletion I M
```

The forward direction goes **from the extended ideal over `S` to the original
ideal over `R`**; `.symm` reverses it. The `R`-module structure on the source
completion is the restriction of its `S`-module structure. This comparison
requires no finite generation, Noetherianity, flatness, separatedness,
completeness, nontriviality or injectivity/surjectivity of `algebraMap R S`.
It is neither a module base-change equivalence nor a claim that an arbitrary
adic completion satisfies a separate completeness predicate.

At level `n`, `map_pow_smul_top_restrictScalars I n` identifies the extended
ideal's power-filtration submodule after restriction of scalars with
`I ^ n • ⊤`. The `R`-linear `restrictScalarsLevelEquiv I M n` compares the
quotients in the same orientation as the completion equivalence.
`restrictScalarsLevelEquiv_mk` and `restrictScalarsLevelEquiv_symm_mk` preserve
representatives in both directions;
`restrictScalarsLevelEquiv_transitionMap` and
`restrictScalarsLevelEquiv_symm_transitionMap` commute with the native
`AdicCompletion.transitionMap` for every `m ≤ n`. Pointwise level comparison
therefore yields the forward and inverse maps on compatible families, and
their inverse laws follow at every level. The `@[simp]` laws
`restrictScalarsEquiv_eval` and `restrictScalarsEquiv_symm_eval` give both
evaluation formulas; `restrictScalarsEquiv_of` and
`restrictScalarsEquiv_symm_of` transport the two native `AdicCompletion.of`
maps.

Level zero works without a special assumption: `I ^ 0 = ⊤`, so its quotient
is trivial. The same equivalence covers the identity algebra and both `⊥`
and `⊤` ideals: for `⊥` positive-degree filtration terms vanish, and for
`⊤` all quotients and completions are trivial, even if `M` is not. For a
nonidentity algebra, import `Mathlib.RingTheory.Polynomial.Basic` and use:

```lean
example (I : Ideal ℤ) :
    AdicCompletion (I.map (algebraMap ℤ (Polynomial ℤ))) (Polynomial ℤ) ≃ₗ[ℤ]
      AdicCompletion I (Polynomial ℤ) :=
  AdicCompletion.restrictScalarsEquiv I (Polynomial ℤ)
```

The [ordinary-import client](../AdicModulesTest/AdicCompletion/RestrictScalars.lean)
exercises these directions and boundary cases. The 103-display-site native
`docs/API.md` snapshot predates this module and remains historical; this guide
and the Lean source describe the current scalar-restriction API.

## Integer singleton spans in unital rings

Import [`AdicModules.Algebra.Module.Int`](../AdicModules/Algebra/Module/Int.lean)
alone or the `AdicModules` public root. For `R : Type u` with `NonAssocRing R`,
the integer action is the canonical `AddCommGroup.toIntModule` action induced
by the additive group. No separately chosen `Module ℤ R` structure is needed.
The span `Submodule.span ℤ ({x} : Set R)` consists of the integer multiples
of `x`; it is not a span for a separately chosen self-scalar action of `R`.

`IsAddCyclic.intCast_surjective` says that the integer cast `ℤ → R` is
surjective when the additive group of `R` is cyclic.
`Submodule.intCast_surjective_of_span_singleton_eq_top` gives the same
conclusion if one element has top integer span. Its contrapositive,
`Submodule.int_span_singleton_ne_top_of_not_surjective_intCast`, makes
**every** singleton integer span proper when integer casts are not surjective.
Multiplication need not be associative or commutative. No `CharZero`,
`Nontrivial`, topology or special-generator hypothesis is added.

The proof uses mathlib's `AddMonoidHom.map_addCyclic`: every additive endomorphism
of a cyclic additive group is an integer scalar map. Apply this to the existing
right-multiplication homomorphism `AddMonoidHom.mulRight a`, and evaluate at
`1`. The identities `1 * a = a` and `m • 1 = (m : R)` put each `a` in the
integer-cast image. This uses no reassociation of ring multiplication or self
`Module R R` structure. Mathlib's `Submodule.span_singleton_eq_top_iff`
provides the cyclic additive-group witness from the top-span premise.

The [ordinary-import clients](../AdicModulesTest/Algebra/Module/Int.lean) show
that `1` generates `ℤ` and every `ZMod n` as an integer module. This includes
`ZMod 0` and the zero ring `ZMod 1`. In a subsingleton ring, every singleton
span is both top and bottom and integer casts are onto. Nonsurjectivity is not
necessary for one particular span to be proper: `ℤ` has surjective casts, yet
its integer span of `2` does not contain `1`.

For `Matrix (Fin 2) (Fin 2) ℤ`, every integer cast is a scalar diagonal matrix.
The matrix unit `E₀₁ = Matrix.single 0 1 1` is not a cast, because its `(0,1)`
entry is `1` rather than `0`. Hence every singleton integer span in this ring
is proper. The span of `E₀₁` contains `E₀₁` itself but not the identity matrix.
The identities `E₀₁ * E₁₀ = E₀₀` and `E₁₀ * E₀₁ = E₁₁` exhibit genuine
noncommutativity, so a commutative-ring restriction would omit this client.

## P-adic neighborhood bases and integer spans

Import [`AdicModules.Topology.Algebra.PadicInt`](../AdicModules/Topology/Algebra/PadicInt.lean)
or the public root. For a prime `p`, the existing norm topology on `ℤ_[p]`
has the zero-neighborhood basis

```lean
(𝓝 (0 : ℤ_[p])).HasBasis (fun _n : ℕ ↦ True)
  (fun n ↦ ((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) : Set ℤ_[p]))
```

`PadicInt.hasBasis_nhds_zero_span_pow` obtains this basis from geometric closed
balls with radii `((p : ℝ)⁻¹) ^ n`. Mathlib's
`PadicInt.norm_le_pow_iff_mem_span_pow` identifies the ideal carrier with the
norm bound `‖x‖ ≤ (p : ℝ) ^ (-n : ℤ)`, including `x = 0`. For nonzero `x`,
Mathlib also gives the equivalent valuation bound `n ≤ x.valuation`; at zero
one must retain a zero disjunct because `PadicInt.valuation_zero = 0`.
At `n = 0` the ideal is top. At positive degrees the positive-radius closed
balls are also open by the ultrametric topology.

`PadicInt.hasBasis_nhds_zero_int_submodule_pow` restricts each whole ideal to
integer scalars:

```lean
((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]).restrictScalars ℤ : Set ℤ_[p])
```

Restriction preserves the carrier and **all p-adic multiples**, not only
integer multiples of `p ^ n`. `PadicInt.isLinearTopology_self` and
`PadicInt.isLinearTopology_int` characterize the existing topology as linear
for the two scalar actions. They are ordinary theorems rather than global
instances; a user can install the desired result locally.

The [Submodule module](../AdicModules/Topology/Algebra/Submodule.lean) also gives
`Submodule.dense_int_span_of_isUnit_of_denseRange_intCast`. Its hypotheses are
`[Ring R]`, `[TopologicalSpace R]`, `[ContinuousConstSMul R R]`, dense range
of `Int.cast : ℤ → R`, and `IsUnit x`. Then `Submodule.span ℤ {x}` is dense.
The ring need not be commutative: multiplication by the unit is a homeomorphism,
and central integer casts identify its transported range with the integer
span. No topology on `ℤ`, characteristic-zero hypothesis, joint multiplication
continuity or separation hypothesis is added.

`PadicInt.dense_int_span_of_isUnit` uses Mathlib's density of integer casts;
`PadicInt.dense_int_span_intCast` specializes to an integer `a` with
`¬ (p : ℤ) ∣ a`. Independently, `PadicInt.int_span_intCast_ne_top` says that
every integer generator has a proper integer span, even `0`, `1` and `-1`.
`PadicInt.inv_succ_notMem_int_span_intCast` supplies the uniform witness
`PadicInt.inv ((p + 1 : ℕ) : ℤ_[p])`, which cannot lie in any such span:
membership would force an integer multiple of `p + 1` to equal one.

In particular, `PadicInt.int_span_three_two_proper_dense` gives a proper dense
integer submodule `Submodule.span ℤ {(3 : ℤ_[2])}`, and
`PadicInt.one_notMem_int_span_three_two` excludes `1`. The self-scalar ideal
generated by the p-adic unit `3` would instead be top.
`PadicInt.int_span_three_two_proper_sup_pow` retains properness and gives

```lean
∀ n : ℕ, Submodule.span ℤ {(3 : ℤ_[2])} ⊔
  (Ideal.span {(2 : ℤ_[2]) ^ n} : Ideal ℤ_[2]).restrictScalars ℤ = ⊤
```

This consumes `Submodule.topologicalClosure_eq_iInf_sup` with the restricted
ideal-power basis. Density gives top closure, `iInf_const` removes the inner
infimum over `True`, and `iInf_le` shows that every individual supremum is top.
It does not reprove the closure formula or replace the ideal carrier by an
integer span. Together, the generic density result and the eleven p-adic
results form this twelve-result API.

The [ordinary-import clients](../AdicModulesTest/Topology/Algebra/PadicInt.lean)
show that closure adds `1`, exercise the uniform witness and small integer
generators, check degree zero and the zero-element valuation boundary, and
refine zero-neighborhoods to submodule neighborhoods for each scalar action.
The positive-degree supremum client adds `1` with the degree-one restricted
ideal and `PadicInt.inv (3 : ℤ_[2])` with the degree-two restricted ideal;
both elements remain excluded from the original integer span of `3`.

## Completion and valuation hypotheses

[`AdicCompletion.abstractCompletion`](../AdicModules/AdicCompletion.lean)
packages the adic inverse limit as a uniform-space completion. It requires a
commutative ring with compatible uniform additive-group structure, `IsAdic I`
for that structure, and a finitely generated ideal `I`. It does not require a
valuation ring. Its canonical map is definitionally the algebra map, with the
public `abstractCompletion_coe` equation.

For valuation-ring results, keep the ring `V` and fraction field `K` explicit.
Their universes are independent. `ValuationRing.CompletionIntegers V K` is the
valuation-integer subring in the uniform completion of `K`, with the canonical
valuation induced by `V`.

`principalAdicCompletionEquiv` compares `AdicCompletion (Ideal.span {a}) V`
with those integers as `V`-algebras. It assumes `a ≠ 0` and
`IsHausdorff (Ideal.span {a}) V`. It does not assume discreteness, rank one,
finite height or Noetherianity. Statements about a non-field local completion,
faithful flatness and the prime-spectrum order isomorphism additionally retain
the hypothesis that `a` belongs to the maximal ideal where stated. The ordinary
[completed-integer](../AdicModulesTest/CompletedIntegers.lean),
[local-structure](../AdicModulesTest/CompletedLocalStructure.lean) and
[spectrum](../AdicModulesTest/PrincipalAdicSpectrum.lean) clients show the needed
local typeclass installations rather than silently adding global instances.

## Module map

All module names below have prefix `AdicModules.`. The public root re-exports
18 mathematical leaves; 19 separate test/audit source modules give 38 maintained
source modules in total when the public root is included. These are source-file
counts, not a compiled-declaration or axiom-audit inventory.

| Module | Main role |
| --- | --- |
| [BoundedIdealPowerTorsion](../AdicModules/BoundedIdealPowerTorsion.lean) | Uniform torsion and finite-module bridge |
| [PrimaryComponent](../AdicModules/PrimaryComponent.lean) | Height-one primary exactness and integer-subgroup restricted maps |
| [AdicCompletion](../AdicModules/AdicCompletion.lean) | Finitely generated adic inverse limit as an abstract completion |
| [AdicCompletion.RestrictScalars](../AdicModules/AdicCompletion/RestrictScalars.lean) | Native adic completion and quotient comparison under scalar restriction |
| [Algebra.Module.Int](../AdicModules/Algebra/Module/Int.lean) | Cyclic additive rings, integer casts and singleton-span properness |
| [Topology.Algebra.Submodule](../AdicModules/Topology/Algebra/Submodule.lean) | Bundled closure from a submodule zero-neighborhood basis and dense integer spans of units |
| [Topology.Algebra.PadicInt](../AdicModules/Topology/Algebra/PadicInt.lean) | P-adic ideal-power bases, linear topology, proper dense integer spans and top neighborhood suprema |
| [ValuationTopology](../AdicModules/ValuationTopology.lean) | Principal-adic versus valuation topology; radical containment |
| [CompletedIntegers](../AdicModules/CompletedIntegers.lean) | Comparison with completed valuation integers |
| [CompletedLocalStructure](../AdicModules/CompletedLocalStructure.lean) | Domain, valuation-ring, fraction-field, local and residue properties |
| [PrincipalAdicSpectrum](../AdicModules/PrincipalAdicSpectrum.lean) | Associated elements, ideal map/comap, faithful flatness, spectra and heights |
| [LocalizedFiltration](../AdicModules/LocalizedFiltration.lean) | Literal base-power images, topology and separatedness after localization |
| [LocalizedCompletion](../AdicModules/LocalizedCompletion.lean) | Embedding the localized completion into the common completed field |
| [LocalizedValuationSubring](../AdicModules/LocalizedValuationSubring.lean) | Realizing that completion as a valuation subring |
| [LocalizedResidueField](../AdicModules/LocalizedResidueField.lean) | Residue-field comparison with the original localization |
| [LocalizedQuotientValuationSubring](../AdicModules/LocalizedQuotientValuationSubring.lean) | Transport of the quotient factor at a nonzero prime |
| [CompositeValuationSubring](../AdicModules/CompositeValuationSubring.lean) | Residue-preimage composite, localization and quotient factors |
| [CompletedValuationComposite](../AdicModules/CompletedValuationComposite.lean) | Composite description of completed valuation integers |

In `LocalizedFiltration`, `localizedPowerImage` is a submodule over the **base
ring**, not the extended ideal. The comparison sandwiches it between successive
powers of the extended principal ideal. The general localization results require
denominators disjoint from the radical of the principal ideal. The nonzero-prime
specialization obtains the required containment from principal-adic separatedness;
it is not a statement about arbitrary localization without hypotheses.

The composite of a valuation subring with a valuation subring of its residue field
is a literal residue preimage. Its distinguished prime recovers the first factor
by localization and the second by quotient. The completed-composite results use
the previously constructed completion and residue maps; they do not introduce a
new notion of completion.

General nonseparated reduction, height/rational-rank additivity, isolated-subgroup
classification and value-group exact sequences are outside the asserted scope.
Source-level correspondence and whole-source coverage are separate research
decisions, not consequences of these APIs or this guide.

## Reproduction and resources

Use the checked-in Lean v4.34.0-rc2 and mathlib revision
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, including all transitive manifest
pins. Fetch `lake exe cache get` successfully before a build; an absent cache is
not permission to silently rebuild all of mathlib. On smaller machines, avoid
other concurrent builds. `LEAN_NUM_THREADS=2` sets each Lean runtime's worker
count; it does not cap the number of concurrent Lake jobs or processes, or total
build memory. No verified whole-build process or RAM cap is supplied here.
Leave space for several gigabytes of dependency sources and artifacts.

### Scalar-restriction resource sample

This historical configured run for the scalar-restriction proof and client used
Lean v4.34.0-rc2, mathlib revision
`e37d88a26f3791ed5a93daa1f949af1021b8d103` and the matching complete Lake
dependency graph. It succeeded for both `AdicModules` and `AdicModulesTest`:
fifteen public mathematical leaves, sixteen ordinary test/audit modules, and
the public root (32 modules total). With those historical pins, the matching
mathlib cache fetch took about 42.509s and decompressed 8892 entries. Cache
verification then took about 6.137s and reported 8907 up-to-date jobs. The
both-target build took about 41.119s and reported 2737 jobs; these are Lake job
counts, not counts of fresh compilations or concurrent processes. The workflow
elapsed about 378s including all its input collection and complete
private-inclusive axiom checks, not just building.

These are historical observations from that measured configuration, not
measurements of the current dependency pins or clean-machine guarantees. No
peak-memory measurement was established for this 32-module run. The older memory
observation below is historical, not a current whole-library estimate.

### Earlier module-readiness measurements

These are **historical author measurements**, not clean-machine guarantees:
on the module-readiness sequence, the matching cache fetch took about 98 seconds.
After a small normalization repair,
the affected default build took 34.020 seconds and Lake reported 2711 jobs,
mostly dependency/cache reuse rather than 2711 fresh compilations. That build
used an already populated dependency cache and prior project artifacts. The
combined native-lint/repair observations reached approximately 12.79 GB of total
container memory, including other resident data and filesystem cache; this is
not a per-process RSS measurement or minimum RAM requirement. No OOM event was
recorded in that bounded run. Source-comment changes and documentation generation
are separate subsequent work and are not benchmarked by those earlier numbers.

Allow more time and memory on a cold or different machine. Build success and
selected axiom output are distinct from the required complete transitive
standard-axiom audit, including private/generated and test declarations.
Native API documentation has
its own source/pin binding and reproduction requirements; no documentation output
should be used as proof-integrity or source-coverage evidence.
