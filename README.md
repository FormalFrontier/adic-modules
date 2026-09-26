# adic-modules

Reusable Lean theory for adic modules and ideal-power torsion.

Authors: Formal Frontier Agents. Licensed under [Apache-2.0](LICENSE).
See the [mathematical guide](docs/Guide.md) for entry points and hypotheses,
the [complete native API reference](docs/API.md) for declaration signatures,
and [credits and provenance](docs/CREDITS.md) for original contributions,
earlier project adaptations and upstream acknowledgments. The
[documentation recipe](docs/README.md) records exact input binding, reproduction
and the limits of the shipped Markdown reference.

## Status

This repository is under active development. Its initial API defines the
source-independent predicate that a power of an ideal annihilates a module and
develops its basic closure API: exponent and ideal monotonicity, submodules,
surjective linear images, quotients, and extensions. For finite modules, it
also identifies uniform ideal-power torsion with the condition that the
elementwise `Ideal.primaryComponent` is the whole module. It also packages the
inverse-limit completion of a finitely generated ideal as an
`AbstractCompletion` of any ring carrying the corresponding adic uniform
topology. For a valuation ring, it proves that separation for the powers of a
nonzero principal ideal makes those powers cofinal in the induced valuation
topology, and identifies that topology as the corresponding principal-adic
topology without rank, discreteness, or Noetherianity assumptions. It then
identifies the separated principal-adic completion with the valuation-integer
subring of the completed fraction field, compatibly with the canonical maps
from the valuation ring. The completion is again a valuation domain, its
fraction field is the completed fraction field, and a nonzero generator in the
maximal ideal gives a non-field local completion with unchanged residue field.
Every element of this completion is associated to an element from the base
valuation ring, so extension after contraction fixes every completion ideal.
For a nonzero generator in the maximal ideal, the completion map is faithfully
flat, contraction is an order isomorphism on prime spectra, and corresponding
primes have equal height. The extension of the original valuation is also
equivalent to the canonical valuation of the completed valuation ring, yielding
the canonical ordered value-group comparison. For a localization at
denominators disjoint from the radical of a principal ideal, the API also
sandwiches the literal images of the base-ring powers between consecutive
powers of the extended ideal. These literal images form a neighborhood basis
for the localized principal-adic topology, and principal-adic separatedness
passes to the localization without finite-height, discreteness, or
Noetherianity assumptions. The induced embedding into the original fraction
field is uniform inducing, so it extends injectively from the localized
principal-adic completion into the same completed fraction field. This map is
compatible with the original valuation-ring embedding, contains the completed
valuation integers in its image, and makes that common completed field a
fraction field of the localized completion. In a separated principal-adic
valuation domain, the principal radical is contained in every nonzero prime,
so separatedness passes directly to localization at any such prime.
The localized principal-adic completion is consequently realized as a
valuation subring of the common completed fraction field, with a canonical
ring equivalence whose ambient map is the accepted completion embedding. Its
residue field is canonically identified with the residue field of the original
localization, compatibly with the canonical maps on elements. At a nonzero
prime, the quotient valuation ring is transported into this completed-
localization residue field by pulling its canonical valuation subring back
along the inverse residue-field equivalence.
Independently of completion, the repository also constructs the composite of a
valuation subring of a field
with a valuation subring of its residue field as the literal residue-preimage
subring. Localization at its distinguished prime recovers the first factor,
while quotienting by that prime recovers the residue factor. A local inclusion
between valuation subrings of the same field is equality.
For the completed valuation ring, these constructions now agree literally:
the completed valuation integers are the composite of the completed
localization at any nonzero prime and the transported quotient valuation ring.
The associated distinguished prime recovers the completed localization, while
the corresponding quotient recovers the transported quotient factor.

The API deliberately distinguishes this uniform module-wide bound from
elementwise ideal-primary torsion. Source interpretation, provenance,
correspondence, and coverage remain in their source-metadata repositories.

Formal Frontier's source-maintainer team maintains the library. It is usable
through its declared dependencies without the project's source-research records.
The [metadata](formalization.yaml) distinguishes historical development review
from later artifact-specific review. This is AI-agent development and review;
it is not a claim of human peer review or complete formalization of a source.

## Build

Install the version in `lean-toolchain` with elan, then fetch the matching
mathlib cache before building. Keep `lake-manifest.json`; do not substitute
floating dependency revisions:

```text
lake exe cache get
lake --wfail build
```

The default target includes the public library and all fourteen ordinary-import
test/audit modules. Individual clients can also be replayed with:

```text
lake env lean -DwarningAsError=true AdicModulesTest/BoundedIdealPowerTorsion.lean
lake env lean -DwarningAsError=true AdicModulesTest/AdicCompletion.lean
lake env lean -DwarningAsError=true AdicModulesTest/ValuationTopology.lean
lake env lean -DwarningAsError=true AdicModulesTest/CompletedIntegers.lean
lake env lean -DwarningAsError=true AdicModulesTest/CompletedLocalStructure.lean
lake env lean -DwarningAsError=true AdicModulesTest/PrincipalAdicSpectrum.lean
lake env lean -DwarningAsError=true AdicModulesTest/LocalizedFiltration.lean
lake env lean -DwarningAsError=true AdicModulesTest/LocalizedCompletion.lean
lake env lean -DwarningAsError=true AdicModulesTest/LocalizedValuationSubring.lean
lake env lean -DwarningAsError=true AdicModulesTest/LocalizedResidueField.lean
lake env lean -DwarningAsError=true AdicModulesTest/LocalizedQuotientValuationSubring.lean
lake env lean -DwarningAsError=true AdicModulesTest/CompositeValuationSubring.lean
lake env lean -DwarningAsError=true AdicModulesTest/CompletedValuationComposite.lean
lake env lean -DwarningAsError=true AdicModulesTest/Axioms.lean
```

The explicit `#print axioms` client is a useful selected audit, not a complete
private/generated-declaration census or an independent stored-proof checker.
Those are separate, exact-artifact release checks. A successful build, import,
documentation render or historical reviewer verdict does not replace them.

For measured cache/build cost and resource cautions, see
[reproduction and resources](docs/Guide.md#reproduction-and-resources).
