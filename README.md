# Formal Plasma Physics in Lean 4

A fully verified formalization of **electromagnetic wave equations** and **plasma equilibrium physics** in [Lean 4](https://lean-lang.org/) with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/). Two modules build from first principles:

1. **MaxwellWave** — Maxwell's equations to electromagnetic wave equations in vacuum, dielectrics, and conductors
2. **PlasmaEquations** — Fluid plasma theory from two-fluid equations through MHD to tokamak (Grad-Shafranov) and rotamak (FRC) equilibria

**Every proof is machine-checked. There are zero `sorry` axioms across both modules.**

---

## MaxwellWave

Formalizes one of the most important results in classical electrodynamics: that Maxwell's equations imply electromagnetic waves travel at the speed of light.

| Medium | Wave Equation |
|--------|--------------|
| **Vacuum** | `nabla^2 E = mu_0 * eps_0 * d^2 E/dt^2` |
| **Dielectric** | `nabla^2 E = mu * eps * d^2 E/dt^2` |
| **Conductor** | `nabla^2 E = mu * eps * d^2 E/dt^2 + mu * sigma * dE/dt` |

(And the same for **B** in each case.)

The conductor equation is the **telegraph equation** (damped wave equation), where the `mu * sigma * dE/dt` term causes exponential attenuation (the skin effect).

### Vector Calculus Layer (`VectorCalculus.lean`)

All differential operators are built on Mathlib's Frechet derivative (`fderiv`):

- **Partial derivatives**: `partialDeriv f i x = fderiv R f x (Pi.single i 1)`
- **Gradient**: `grad f x = fun i => partial_i f(x)`
- **Divergence**: `div F x = sum_i partial_i F_i(x)`
- **Curl**: `curl F x` via the standard cross-product formula
- **Laplacian**: scalar and vector, `nabla^2 F x j = sum_i partial_i^2 F_j(x)`

#### Proven Identities

| Theorem | Statement |
|---------|-----------|
| `fderiv_apply_comm` | Symmetry of mixed partials (Clairaut/Schwarz) |
| `curl_gradient_eq_zero` | `curl(grad f) = 0` |
| `divergence_curl_eq_zero` | `div(curl F) = 0` |
| `curl_curl_eq_grad_div_sub_laplacian` | `curl(curl F) = grad(div F) - nabla^2 F` |
| `curl_neg` | `curl(-F) = -curl(F)` |
| `curl_add` | `curl(F + G) = curl(F) + curl(G)` |
| `curl_const_mul` | `curl(c * F) = c * curl(F)` |

### Electrodynamics Layer (`Maxwell.lean`)

- **`Medium`**: Linear, isotropic, homogeneous medium with permittivity `eps`, permeability `mu`, and conductivity `sigma`
- **`MaxwellSystem`**: The four Maxwell equations in differential form
- **`SourceFreeMaxwell`**: Specialization with `rho = 0` and `J_free = 0`
- **Constructors**: `vacuum`, `dielectric`, `conductor` with appropriate parameter constraints

### Wave Equation Layer (`WaveEquation.lean`)

The unified result from which all special cases follow:

```
theorem general_wave_equation_E :
    nabla^2 E(t,x)_j = mu * eps * d^2 E_j/dt^2 + mu * sigma * dE_j/dt

theorem general_wave_equation_B :
    nabla^2 B(t,x)_j = mu * eps * d^2 B_j/dt^2 + mu * sigma * dB_j/dt
```

| Theorem | Medium | Equation |
|---------|--------|----------|
| `vacuum_wave_equation_E/B` | `sigma = 0`, `eps_0`, `mu_0` | `nabla^2 F = mu_0 * eps_0 * d^2F/dt^2` |
| `dielectric_wave_equation_E/B` | `sigma = 0`, general `eps`, `mu` | `nabla^2 F = mu * eps * d^2F/dt^2` |
| `conductor_wave_equation_E/B` | `sigma > 0` | `nabla^2 F = mu * eps * d^2F/dt^2 + mu * sigma * dF/dt` |
| `vacuum_wave_speed` | vacuum | `c = 1 / sqrt(mu_0 * eps_0)` |
| `dielectric_wave_speed_sq` | dielectric | `v^2 = 1 / (mu * eps)` |

---

## PlasmaEquations

Builds from the MaxwellWave foundation through fluid plasma theory to reach tokamak and rotamak equilibrium equations. The mathematical path:

```
Maxwell's equations
    |
    v
Two-fluid plasma equations (ions + electrons)
    |
    v
Single-fluid ideal MHD (mass-weighted averages, quasi-neutrality)
    |                     \
    v                      v
Resistive MHD          MHD Equilibrium (force balance: nabla p = J x B)
                           |                    \
                           v                     v
                   Grad-Shafranov             FRC / Rotamak
                   (Tokamak)                  (Rotamak)
```

### Vector Algebra (`VectorAlgebra.lean`)

Cross product, dot product, and field-level algebra on R^3 vector fields, built atop Mathlib's `crossProduct` and `dotProduct`.

| Lemma | Statement |
|-------|-----------|
| `cross_anticomm_field` | `F(x) x G(x) = -(G(x) x F(x))` |
| `fieldDot_self_cross_eq_zero` | `F(x) . (F(x) x G(x)) = 0` |
| `fieldDot_cross_self_eq_zero` | `(F(x) x G(x)) . G(x) = 0` |

### Fluid Operators (`FluidOperators.lean`)

- **Advective derivative**: `(v . nabla)f` and `(v . nabla)F`
- **Material derivative**: `Df/Dt = df/dt + (v . nabla)f`

### Ideal MHD (`SingleFluidMHD.lean`)

The `IdealMHD` structure encodes the six coupled equations as axioms:

1. **Mass conservation**: `d rho/dt + nabla . (rho v) = 0`
2. **Momentum**: `rho Dv/Dt = J x B - nabla p`
3. **Energy (adiabatic)**: `dp/dt + v . nabla p + gamma p nabla . v = 0`
4. **Induction**: `dB/dt = nabla x (v x B)`
5. **Solenoidal**: `nabla . B = 0`
6. **Ampere (MHD limit)**: `nabla x B = mu_0 J`

| Theorem | Statement |
|---------|-----------|
| `ideal_induction_from_faraday_ohm` | Faraday + ideal Ohm's law implies the induction equation |
| `J_from_ampere` | `J = (nabla x B) / mu_0` |
| `div_B_preserved` | Solenoidal constraint holds at all times |

### Resistive MHD (`ResistiveMHD.lean`)

Extends ideal MHD with finite resistivity eta. The induction equation becomes `dB/dt = nabla x (v x B - eta J)`.

| Theorem | Statement |
|---------|-----------|
| `resistive_reduces_to_ideal` | Setting `eta = 0` recovers the ideal induction equation |
| `resistive_induction_diffusion_form` | `dB/dt = nabla x (v x B) - eta nabla x J` via curl linearity |

### MHD Equilibrium (`MHDEquilibrium.lean`)

Static force balance `nabla p = J x B` with Ampere's law and solenoidal constraint.

| Theorem | Statement |
|---------|-----------|
| `B_dot_grad_p_eq_zero` | `B . nabla p = 0` (B lies on pressure surfaces) |
| `J_dot_grad_p_eq_zero` | `J . nabla p = 0` (J lies on pressure surfaces) |
| `force_balance_cross_form` | `nabla p = (1/mu_0)(nabla x B) x B` |
| `magnetic_pressure_form` | `nabla p = (1/mu_0)((B . nabla)B - nabla(B^2/2))` |

### Grad-Shafranov / Tokamak (`GradShafranov.lean`)

The central equation of tokamak equilibrium theory for axisymmetric plasmas:

```
Delta* psi = -mu_0 R^2 p'(psi) - g(psi) g'(psi)
```

where `Delta* = d^2/dR^2 - (1/R) d/dR + d^2/dZ^2` is the Grad-Shafranov operator, `p(psi)` is the pressure profile, and `g(psi) = R B_phi` is the poloidal current function.

| Theorem | Statement |
|---------|-----------|
| `gs_pressure_flux_surface` | Pressure is constant on flux surfaces |
| `gs_is_equilibrium` | The GS equation implies `nabla p = J x B` in cylindrical geometry |
| `gs_solovev_linear` | For linear `p(psi)` and `g^2(psi)`, the GS equation has constant RHS |

The `gs_is_equilibrium` proof uses the chain rule for composite scalar fields (`p(psi(x))`), explicit cylindrical current density from Ampere's law (not the Cartesian curl, which gives incorrect metric factors), and the `linear_combination` tactic to algebraically verify each component against the GS equation.

### Rotamak / FRC (`RotamakFRC.lean`)

A Field-Reversed Configuration (FRC) is a compact toroid where the poloidal field reverses direction. A Rotamak sustains the FRC via a Rotating Magnetic Field (RMF) drive.

| Theorem | Statement |
|---------|-----------|
| `frc_no_toroidal_balance` | With `B_theta = 0`, radial balance simplifies |
| `frc_total_pressure_conservation` | `p + B^2/(2 mu_0) = const` in theta-pinch limit |
| `frc_beta_at_separatrix` | `beta = 1` at the separatrix (where `B_z = 0`) |
| `rotamak_ampere_consistency` | `J_theta > 0` where `B_z` decreases (current drives field reversal) |

---

## Project Structure

```
MaxwellWave/
  VectorCalculus.lean   -- Differential operators + identities (347 lines)
  Maxwell.lean          -- Medium, MaxwellSystem (164 lines)
  WaveEquation.lean     -- Wave equation derivations (301 lines)
  ProofSketch.lean      -- Intermediate result + docs (111 lines)
MaxwellWave.lean        -- Root module

PlasmaEquations/
  VectorAlgebra.lean      -- Cross/dot product, field algebra (96 lines)
  FluidOperators.lean     -- Advective/material derivatives (51 lines)
  LorentzForce.lean       -- Electromagnetic force on fluids (37 lines)
  TwoFluid.lean           -- Two-fluid plasma equations (65 lines)
  SingleFluidMHD.lean     -- Ideal MHD system (128 lines)
  ResistiveMHD.lean       -- Resistive MHD + Ohm's law (114 lines)
  MHDEquilibrium.lean     -- Static force balance (156 lines)
  CylindricalCoords.lean  -- Cylindrical coordinates + GS operator (64 lines)
  GradShafranov.lean      -- Tokamak equilibrium (193 lines)
  RotamakFRC.lean         -- Rotamak / FRC equilibrium (165 lines)
PlasmaEquations.lean      -- Root module

lakefile.toml           -- Build configuration
lean-toolchain          -- Lean version pin
```

## Proof Statistics

| | MaxwellWave | PlasmaEquations | **Total** |
|--|-------------|-----------------|-----------|
| Lines of Lean 4 | ~930 | ~1,080 | **~2,010** |
| Definitions | 20 | 23 | **43** |
| Structures | 4 | 12 | **16** |
| Theorems | 17 | 18 | **35** |
| Lemmas | 8 | 9 | **17** |
| `sorry` axioms | **0** | **0** | **0** |

## Dependencies

- **Lean 4**: `v4.28.0-rc1`
- **Mathlib**: latest compatible (pinned via `lake-manifest.json`)

Key Mathlib imports:
- `Mathlib.Analysis.Calculus.FDeriv.*` — Frechet derivative and its properties
- `Mathlib.Analysis.Calculus.FDeriv.Symmetric` — `IsSymmSndFDerivAt` (Clairaut's theorem)
- `Mathlib.Analysis.Calculus.ContDiff.Defs` — Smoothness classes (`ContDiff`)
- `Mathlib.Analysis.InnerProductSpace.PiL2` — Inner product on `Fin n -> R`
- `Mathlib.LinearAlgebra.CrossProduct` — Cross product on `Fin 3 -> R`

## Building

### Prerequisites

Install [elan](https://github.com/leanprover/elan) (the Lean version manager):

```bash
curl https://elan.lean-lang.org/install.sh -sSf | sh
```

### Build

```bash
# Fetch pre-compiled Mathlib oleans (saves ~1 hour of compilation)
lake exe cache get

# Build the project
lake build
```

A successful build with zero errors and zero warnings confirms that every proof is verified by Lean's kernel.

## Design Decisions

### Why `fderiv` instead of `deriv`?

All spatial differential operators are built on Mathlib's **Frechet derivative** (`fderiv`) rather than the univariate `deriv`. This is because our fields live on `R^3` (modeled as `Fin 3 -> R`), which is a multi-dimensional space. The Frechet derivative is the natural generalization:

```
partialDeriv f i x = fderiv R f x (Pi.single i 1)
```

This extracts the partial derivative in direction `i` by evaluating the total derivative at the `i`-th basis vector.

### Why `Fin 3 -> R` instead of `EuclideanSpace R (Fin 3)`?

Using `Fin 3 -> R` (aliased as `Vec3`) keeps things simple and avoids the coercion overhead of `EuclideanSpace`. Since we don't need the Euclidean space structure beyond what `PiLp` provides, the function type is sufficient and more ergonomic.

### Structure-with-axioms pattern

Physical systems (Maxwell, ideal MHD, resistive MHD, equilibria) are modeled as Lean `structure`s where the physical equations appear as fields of type `Prop`. This is the same approach used in Mathlib for algebraic structures. For example, `IdealMHD` bundles the field variables `rho, v, p, B, J` with six axioms (mass conservation, momentum, energy, induction, solenoidal, Ampere). Theorems are then consequences derived from the axioms.

### Cylindrical vs Cartesian curl

The `gs_is_equilibrium` proof uses explicit cylindrical current density definitions rather than applying the Cartesian `curl` to cylindrical field components. This is necessary because the Cartesian curl gives incorrect results when applied to cylindrical coordinates (the metric factors differ, specifically the Z-component of current differs by `-g(psi)/R^2`).

## Related Work

- **[PhysLean](https://physlean.com/)**: A comprehensive physics formalization in Lean 4 with tensor-based electrodynamics. Uses differential forms and tensor notation rather than the vector calculus approach taken here.
- **[Mathlib](https://leanprover-community.github.io/mathlib4_docs/)**: Provides the foundational analysis (Frechet derivatives, smoothness classes, symmetry of second derivatives) that this project builds on.

## License

Apache 2.0
