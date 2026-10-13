/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.BoundedIdealPowerTorsion
public import AdicModules.PrimaryComponent
public import AdicModules.AdicCompletion
public import AdicModules.AdicCompletion.RestrictScalars
public import AdicModules.Algebra.Module.Int
public import AdicModules.Topology.Algebra.Submodule
public import AdicModules.Topology.Algebra.PadicInt
public import AdicModules.ValuationTopology
public import AdicModules.CompletedIntegers
public import AdicModules.CompletedLocalStructure
public import AdicModules.PrincipalAdicSpectrum
public import AdicModules.LocalizedFiltration
public import AdicModules.LocalizedCompletion
public import AdicModules.LocalizedValuationSubring
public import AdicModules.LocalizedResidueField
public import AdicModules.LocalizedQuotientValuationSubring
public import AdicModules.CompositeValuationSubring
public import AdicModules.CompletedValuationComposite

/-!
# Adic modules and valuation-ring completions

The public entry point re-exports bounded ideal-power torsion, primary-component exactness,
abstract adic completions, principal-adic valuation topology, completed valuation integers
and their local, spectral, localization and composite-valuation interfaces. It also
compares native adic completions under restriction of scalars and describes submodule closure
using a basis of submodule neighborhoods of zero in a given topological additive group.
For unital rings, additive cyclicity implies surjective integer casts; nonsurjective
integer casts force every singleton span under the canonical integer action to be proper.
For the p-adic integers it gives ideal-power neighborhood bases and proper dense
integer spans, using their usual norm topology. Test and audit modules are separate.
Theorems retain their stated separation, nonzero-generator and localization hypotheses.
-/
