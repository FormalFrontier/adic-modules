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
| [AdicCompletion](../AdicModules/AdicCompletion.lean) | Finitely generated adic inverse limit as an abstract completion |
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
not permission to silently rebuild all of mathlib. With limited memory, set
`LEAN_NUM_THREADS=2` for the cache/build commands and avoid concurrent large Lean
jobs. Leave space for several gigabytes of dependency sources and artifacts.

These are **historical author measurements**, not clean-machine guarantees:
on the module-readiness sequence, the matching cache fetch took about 98 seconds.
After the small `a590809e4012f98f443edff7a40574aad1108799` normalization repair,
the affected default build took 34.020 seconds and Lake reported 2711 jobs,
mostly dependency/cache reuse rather than 2711 fresh compilations. That build
used an already populated dependency cache and prior project artifacts. The
combined native-lint/repair observations reached approximately 12.79 GB of total
container memory, including other resident data and filesystem cache; this is
not a per-process RSS measurement or minimum RAM requirement. No OOM event was
recorded in that bounded run. Source-comment changes and documentation generation
are separate subsequent work and are not benchmarked by those earlier numbers.

Allow more time and memory on a cold or different machine. Build success and
selected axiom output are distinct from exhaustive private/generated axiom
enumeration and independent stored-term checking. Native API documentation has
its own source/pin binding and reproduction requirements; no documentation output
should be used as proof-integrity or source-coverage evidence.
