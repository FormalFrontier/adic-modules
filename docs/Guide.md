# Using adic-modules

This library builds on mathlib's native ideals, modules, inverse-limit adic
completion, valuations, localization and uniform-space completion. Import
`AdicModules` for the public API, or import a narrower module below. The files
under `AdicModulesTest` are ordinary downstream-use examples and selected axiom
audits, not additional public mathematical API.

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

All module names below have prefix `AdicModules.`.

| Module | Main role |
| --- | --- |
| [BoundedIdealPowerTorsion](../AdicModules/BoundedIdealPowerTorsion.lean) | Uniform torsion and finite-module bridge |
| [PrimaryComponent](../AdicModules/PrimaryComponent.lean) | Height-one primary exactness and integer-subgroup restricted maps |
| [AdicCompletion](../AdicModules/AdicCompletion.lean) | Finitely generated adic inverse limit as an abstract completion |
| [AdicCompletion.RestrictScalars](../AdicModules/AdicCompletion/RestrictScalars.lean) | Native adic completion and quotient comparison under scalar restriction |
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
`e37d88a26f3791ed5a93daa1f949af1021b8d103`, including all transitive manifest
pins. Fetch `lake exe cache get` successfully before a build; an absent cache is
not permission to silently rebuild all of mathlib. On smaller machines, avoid
other concurrent builds. `LEAN_NUM_THREADS=2` sets each Lean runtime's worker
count; it does not cap the number of concurrent Lake jobs or processes, or total
build memory. No verified whole-build process or RAM cap is supplied here.
Leave space for several gigabytes of dependency sources and artifacts.

### 2026-09-30 scalar-restriction build sample

A configured CI run for the scalar-restriction contribution succeeded on
2026-09-30. It covered
both `AdicModules` and `AdicModulesTest`: fifteen public mathematical leaves,
sixteen ordinary test/audit modules, and the public root (32 modules total).
With the exact pins above, the matching mathlib cache fetch took about 42.509s
and decompressed 8892 entries. Cache verification then took about 6.137s and
reported 8907 up-to-date jobs. The both-target build took about 41.119s and
reported 2737 jobs; these are Lake job counts, not counts of fresh compilations
or concurrent processes. The workflow elapsed about 378s including all its
input collection and complete private-inclusive axiom checks, not just building.

These are observations from that measured configuration, not clean-machine
guarantees. No peak-memory measurement was established for this 32-module run.
The older memory observation below is historical, not a current 32-module estimate.

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
