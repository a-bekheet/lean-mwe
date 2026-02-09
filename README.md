# MaxwellWave

A fully verified formalization of the **electromagnetic wave equations** in [Lean 4](https://lean-lang.org/) with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/). Starting from Maxwell's equations in differential form, we derive the wave equations for the electric field **E** and magnetic field **B** in three types of linear media: vacuum, lossless dielectrics, and lossy conductors.

**Every proof is machine-checked. There are zero `sorry` axioms.**

## What Is This?

This project formalizes one of the most important results in classical electrodynamics: that Maxwell's equations imply electromagnetic waves travel at the speed of light. Specifically, we prove:

| Medium | Wave Equation |
|--------|--------------|
| **Vacuum** | `nabla^2 E = mu_0 * eps_0 * d^2 E/dt^2` |
| **Dielectric** | `nabla^2 E = mu * eps * d^2 E/dt^2` |
| **Conductor** | `nabla^2 E = mu * eps * d^2 E/dt^2 + mu * sigma * dE/dt` |

(And the same for **B** in each case.)

The conductor equation is the **telegraph equation** (damped wave equation), where the `mu * sigma * dE/dt` term causes exponential attenuation (the skin effect).

## Mathematical Content

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

The **curl-curl identity** is the critical bridge from Maxwell's equations to the wave equation. Its proof is the most involved in the project (100+ lines), requiring component-by-component expansion across all three spatial dimensions, `fderiv_sub` to split derivatives of differences, and `fderiv_apply_comm` for mixed-partial symmetry.

The **Clairaut/Schwarz theorem** (`fderiv_apply_comm`) connects our `fderiv`-based partial derivatives to Mathlib's `IsSymmSndFDerivAt` via the chain rule for continuous linear map evaluation (`fderiv_clm_apply`).

### Electrodynamics Layer (`Maxwell.lean`)

Defines the mathematical structures:

- **`Medium`**: Linear, isotropic, homogeneous medium with permittivity `eps`, permeability `mu`, and conductivity `sigma` (all positive reals)
- **`MaxwellSystem`**: The four Maxwell equations in differential form:
  1. Gauss's law: `div E = rho / eps`
  2. No monopoles: `div B = 0`
  3. Faraday's law: `curl E = -dB/dt`
  4. Ampere-Maxwell: `curl B = mu * (J_free + sigma * E) + mu * eps * dE/dt`
- **`SourceFreeMaxwell`**: Specialization with `rho = 0` and `J_free = 0`
- **Constructors**: `vacuum`, `dielectric`, `conductor` with appropriate parameter constraints

### Wave Equation Layer (`WaveEquation.lean`)

#### General Wave Equations

The unified result from which all special cases follow:

```
theorem general_wave_equation_E :
    nabla^2 E(t,x)_j = mu * eps * d^2 E_j/dt^2 + mu * sigma * dE_j/dt

theorem general_wave_equation_B :
    nabla^2 B(t,x)_j = mu * eps * d^2 B_j/dt^2 + mu * sigma * dB_j/dt
```

**Derivation strategy for E** (10 proof steps):
1. Curl-curl identity: `curl(curl E) = grad(div E) - nabla^2 E`
2. Source-free Gauss (`div E = 0`): `nabla^2 E = -curl(curl E)`
3. Faraday's law: `curl E = -dB/dt`
4. Distribute curl over negation
5. Commute curl with time derivative
6. Substitute Ampere-Maxwell for `curl B`
7. Linearity of time derivative to split the sum
8. Rearrange

**Derivation strategy for B** (6 proof steps):
1. Curl-curl + `div B = 0`: `nabla^2 B = -curl(curl B)`
2. Ampere as function equality
3. Curl linearity (`curl_add`, `curl_const_mul`) to distribute
4. Faraday substitution
5. Commute curl/time derivatives
6. `deriv_neg` and rearrange

#### Specialized Theorems

| Theorem | Medium | Equation |
|---------|--------|----------|
| `vacuum_wave_equation_E/B` | `sigma = 0`, `eps_0`, `mu_0` | `nabla^2 F = mu_0 * eps_0 * d^2F/dt^2` |
| `dielectric_wave_equation_E/B` | `sigma = 0`, general `eps`, `mu` | `nabla^2 F = mu * eps * d^2F/dt^2` |
| `conductor_wave_equation_E/B` | `sigma > 0` | `nabla^2 F = mu * eps * d^2F/dt^2 + mu * sigma * dF/dt` |
| `vacuum_wave_speed` | vacuum | `c = 1 / sqrt(mu_0 * eps_0)` |
| `dielectric_wave_speed_sq` | dielectric | `v^2 = 1 / (mu * eps)` |

### Proof Sketches (`ProofSketch.lean`)

Contains the step-by-step derivation for the curl-of-Faraday intermediate result (`curl_of_faraday`), which shows `curl(curl E) = -d(curl B)/dt` — the first step in the wave equation derivation.

## Project Structure

```
MaxwellWave/
  VectorCalculus.lean   -- Differential operators + vector calculus identities (347 lines)
  Maxwell.lean          -- Medium, MaxwellSystem, SourceFreeMaxwell (164 lines)
  WaveEquation.lean     -- Wave equation derivations for all media (301 lines)
  ProofSketch.lean      -- Intermediate result + documentation (111 lines)
MaxwellWave.lean        -- Root module (imports all)
lakefile.toml           -- Build configuration
lean-toolchain          -- Lean version pin
```

**Total**: ~930 lines of Lean 4 across 5 source files.

## Proof Statistics

| Category | Count |
|----------|-------|
| Definitions | 20 |
| Structures | 4 |
| Theorems | 17 |
| Lemmas | 8 |
| `sorry` axioms | **0** |

## Dependencies

- **Lean 4**: `v4.28.0-rc1`
- **Mathlib**: latest compatible (pinned via `lake-manifest.json`)

Key Mathlib imports:
- `Mathlib.Analysis.Calculus.FDeriv.*` — Frechet derivative and its properties
- `Mathlib.Analysis.Calculus.FDeriv.Symmetric` — `IsSymmSndFDerivAt` (Clairaut's theorem)
- `Mathlib.Analysis.Calculus.ContDiff.Defs` — Smoothness classes (`ContDiff`)
- `Mathlib.Analysis.InnerProductSpace.PiL2` — Inner product on `Fin n -> R`

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

A successful build with zero errors and zero warnings (other than unused variable lints) confirms that every proof is verified by Lean's kernel.

## Design Decisions

### Why `fderiv` instead of `deriv`?

All spatial differential operators are built on Mathlib's **Frechet derivative** (`fderiv`) rather than the univariate `deriv`. This is because our fields live on `R^3` (modeled as `Fin 3 -> R`), which is a multi-dimensional space. The Frechet derivative is the natural generalization:

```
partialDeriv f i x = fderiv R f x (Pi.single i 1)
```

This extracts the partial derivative in direction `i` by evaluating the total derivative at the `i`-th basis vector.

### Why `Fin 3 -> R` instead of `EuclideanSpace R (Fin 3)`?

Using `Fin 3 -> R` (aliased as `Vec3`) keeps things simple and avoids the coercion overhead of `EuclideanSpace`. Since we don't need the Euclidean space structure beyond what `PiLp` provides, the function type is sufficient and more ergonomic.

### Why `ContDiff R 2` for smoothness?

The symmetry of mixed partial derivatives (Clairaut's theorem) requires C^2 smoothness. This is the minimal regularity assumption needed for our proofs. The `IsC2Vector` predicate requires each component `fun x => F x j` to be C^2, which is sufficient to derive differentiability of `fderiv` (via `ContDiff.fderiv_right`) and the symmetry result (via `IsSymmSndFDerivAt`).

### Why `SufficientlySmooth` as a structure?

The wave equation derivation requires several regularity conditions beyond spatial C^2:
- **Curl-time commutativity**: swapping `curl` with `d/dt` (a Leibniz integral rule consequence)
- **Time differentiability**: components and their time derivatives must be differentiable in `t`

Rather than threading these as separate hypotheses through every theorem, we bundle them in `SufficientlySmooth`. This is physically reasonable — real electromagnetic fields are smooth — and keeps the theorem statements clean.

### Why separate `general_wave_equation_E` and `_B`?

The derivations for E and B follow different paths:
- **E**: curl Faraday -> substitute Ampere -> derivative linearity
- **B**: curl Ampere -> curl linearity to distribute -> substitute Faraday -> `deriv_neg`

The B derivation requires curl linearity (`curl_add`, `curl_const_mul`) because Ampere's law has a sum `mu * sigma * E + mu * eps * dE/dt` inside the curl, while Faraday's law has a single term.

## Technical Challenges

### Differentiability Threading

The main difficulty in this formalization is not the mathematics but the **differentiability bookkeeping**. Every use of `fderiv_sub`, `fderiv_add`, or `fderiv_const_smul` requires a `DifferentiableAt` proof for each operand. When the operand is itself an `fderiv` application (as in second derivatives), you need:

1. `ContDiff R 2 f` (C^2 hypothesis)
2. `ContDiff R 1 (fderiv R f)` (via `ContDiff.fderiv_right`)
3. `DifferentiableAt R (fderiv R f) x` (via `.differentiable.differentiableAt`)
4. `DifferentiableAt R (fun y => fderiv R f y v) x` (via `.clm_apply`)

This chain appears repeatedly throughout the proofs.

### `WithTop ENNReal` Coercions

Lean's smoothness order has type `WithTop NNInfty` (written `WithTop ℕ∞`). The coercion `(2 : ℕ) -> WithTop ℕ∞` sometimes requires `norm_num` rather than `simp` to resolve arithmetic goals like `1 + 1 <= 2` at this type.

### CLM Evaluation Chain

The proof of `fderiv_apply_comm` requires connecting:
```
fderiv R (fun y => fderiv R f y v) x w
```
to Mathlib's `IsSymmSndFDerivAt`. The bridge is `fderiv_clm_apply`, which gives a product-rule decomposition for evaluating a CLM-valued function at a point. With a constant second argument and `simp`, this reduces to `(fderiv R (fderiv R f) x).flip v`, from which symmetry follows.

## Related Work

- **[PhysLean](https://physlean.com/)**: A comprehensive physics formalization in Lean 4 with tensor-based electrodynamics. Uses differential forms and tensor notation rather than the vector calculus approach taken here.
- **[Mathlib](https://leanprover-community.github.io/mathlib4_docs/)**: Provides the foundational analysis (Frechet derivatives, smoothness classes, symmetry of second derivatives) that this project builds on.

## License

Apache 2.0
