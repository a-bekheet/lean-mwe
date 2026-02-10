/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Lorentz Force Density

The electromagnetic force per unit volume on a charged fluid:
  f = ρ_c E + J × B
where ρ_c is the charge density and J is the current density.
-/
import PlasmaEquations.VectorAlgebra

noncomputable section

open scoped BigOperators

namespace PlasmaEquations

open MaxwellWave

/-- Lorentz force per unit volume: `f = ρ_c E + J × B`.
    This is the force density exerted by electromagnetic fields on a plasma. -/
def LorentzForcePerVolume (ρ_c : ScalarField) (J E B : VectorField)
    (x : Vec3) : Vec3 :=
  fun i => ρ_c x * E x i + fieldCross J B x i

/-- The Lorentz force dotted with B gives ρ_c(E · B).
    This follows because (J × B) · B = 0 — the magnetic force does no work
    along B. -/
theorem lorentz_dot_B (ρ_c : ScalarField) (J E B : VectorField) (x : Vec3) :
    vec3Dot (LorentzForcePerVolume ρ_c J E B x) (B x) =
    ρ_c x * vec3Dot (E x) (B x) := by
  simp only [vec3Dot, LorentzForcePerVolume, dotProduct, fieldCross, vec3Cross, crossProduct]
  simp [Fin.sum_univ_three]
  ring

end PlasmaEquations
