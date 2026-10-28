module

import AdicModules.AdicCompletion.Pi

universe uR uJ uM

example {R : Type uR} [CommRing R] (I : Ideal R)
    {J : Type uJ} (M : J → Type uM)
    [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    (hI : I.FG) [∀ j, IsAdicComplete I (M j)] :
    Function.Bijective (AdicCompletion.of I (∀ j, M j)) := by
  exact (AdicCompletion.of_bijective_iff (I := I) (M := ∀ j, M j)).mpr
    (IsAdicComplete.pi_of_fg I M hI)
