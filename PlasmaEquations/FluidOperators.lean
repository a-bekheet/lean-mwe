/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Fluid Operators

Advective derivative (v·∇)f and material derivative Df/Dt for scalar and
vector fields, fundamental to fluid dynamics and MHD.
-/
import PlasmaEquations.VectorAlgebra

noncomputable section

open scoped BigOperators

namespace PlasmaEquations

open MaxwellWave

/-! ## Advective Derivatives

The advective derivative `(v·∇)f` represents transport of a quantity `f`
by a velocity field `v`. For a scalar field: `(v·∇)f = Σ_i v_i ∂f/∂x_i`.
For a vector field component: `((v·∇)F)_j = Σ_i v_i ∂F_j/∂x_i`. -/

/-- Advective derivative of a scalar field: `(v·∇)f(x) = Σ_i v(x)_i · ∂f/∂x_i(x)`. -/
def advectiveDerivScalar (v : VectorField) (f : ScalarField) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, v x i * partialDeriv f i x

/-- Advective derivative of a vector field component:
    `((v·∇)F)_j(x) = Σ_i v(x)_i · ∂F_j/∂x_i(x)`. -/
def advectiveDerivVector (v : VectorField) (F : VectorField) (x : Vec3) (j : Fin 3) : ℝ :=
  ∑ i : Fin 3, v x i * partialDerivComp F i j x

/-! ## Material Derivatives

The material derivative `Df/Dt = ∂f/∂t + (v·∇)f` gives the rate of change
of a quantity following a fluid element. -/

/-- Material derivative of a time-dependent scalar field:
    `Df/Dt = ∂f/∂t + (v·∇)f`. -/
def materialDerivScalar (v : TDVectorField) (f : TDScalarField) (t : ℝ) (x : Vec3) : ℝ :=
  timeDeriv f t x + advectiveDerivScalar (v t) (f t) x

/-- Material derivative of a time-dependent vector field component:
    `(DF/Dt)_j = ∂F_j/∂t + ((v·∇)F)_j`. -/
def materialDerivVector (v : TDVectorField) (F : TDVectorField)
    (t : ℝ) (x : Vec3) (j : Fin 3) : ℝ :=
  timeDerivComp F j t x + advectiveDerivVector (v t) (F t) x j

end PlasmaEquations
