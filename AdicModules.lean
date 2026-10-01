/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.BoundedIdealPowerTorsion
public import AdicModules.PrimaryComponent
public import AdicModules.AdicCompletion
public import AdicModules.AdicCompletion.RestrictScalars
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
compares native adic completions under restriction of scalars.
Test and audit modules are separate.
Theorems retain their stated separation, nonzero-generator and localization hypotheses.
-/
