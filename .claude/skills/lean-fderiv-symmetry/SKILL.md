---
name: lean-fderiv-symmetry
description: Proving symmetry of mixed partial derivatives in Lean 4 / Mathlib. Use when working with second derivatives, mixed partials, Clairaut/Schwarz theorem, or IsSymmSndFDerivAt.
user-invocable: false
---

# Symmetry of Mixed Partial Derivatives (Clairaut/Schwarz)

## The Problem

Proving that mixed partial derivatives commute:
```
fderiv R (fun y => fderiv R f y v) x w = fderiv R (fun y => fderiv R f y w) x v
```

This is NOT trivially available in Mathlib. Mathlib provides `IsSymmSndFDerivAt` which states symmetry at the level of `fderiv (fderiv f) x`, but connecting your `fderiv`-of-evaluation expression to that requires a non-obvious bridge.

## The Bridge: `fderiv_clm_apply`

The key insight is that `fun y => fderiv R f y v` is really "evaluate a CLM-valued function at a constant vector". Mathlib's `fderiv_clm_apply` gives a product rule for this:

```lean
fderiv_clm_apply : DifferentiableAt R c x -> DifferentiableAt R u x ->
  fderiv R (fun y => c y (u y)) x = ...
```

When the second argument `u` is constant (e.g., `fun _ => v`), `simp` simplifies the product rule to just the `flip` term.

## Complete Proof Pattern

```lean
lemma fderiv_apply_comm (f : ScalarField) (hf : ContDiff R 2 f) (x v w : Vec3) :
    fderiv R (fun y => fderiv R f y v) x w =
    fderiv R (fun y => fderiv R f y w) x v := by
  -- Step 1: Get Mathlib's symmetry result
  have hsymm : IsSymmSndFDerivAt R f x :=
    hf.contDiffAt.isSymmSndFDerivAt (by simp)
  -- Step 2: Get differentiability of fderiv (C^2 => fderiv is C^1 => differentiable)
  have hfderiv_c1 : ContDiff R 1 (fderiv R f) :=
    hf.fderiv_right (by norm_num)  -- NOTE: norm_num, not simp!
  have hdf : DifferentiableAt R (fderiv R f) x :=
    (hfderiv_c1.differentiable (by simp)).differentiableAt
  -- Step 3: Apply fderiv_clm_apply with constant second argument
  have key_v := fderiv_clm_apply hdf (differentiableAt_const v)
  have key_w := fderiv_clm_apply hdf (differentiableAt_const w)
  -- Step 4: simp kills the constant-derivative term, leaving flip
  simp at key_v key_w
  -- Step 5: Rewrite to match function form
  rw [show (fun y => fderiv R f y v) = fun y => (fderiv R f y) v from rfl] at key_v
  rw [show (fun y => fderiv R f y w) = fun y => (fderiv R f y) w from rfl] at key_w
  -- Step 6: Extract pointwise equality from CLM equality
  have := ContinuousLinearMap.ext_iff.mp key_v w
  have := ContinuousLinearMap.ext_iff.mp key_w v
  simp [ContinuousLinearMap.flip_apply] at *
  -- Step 7: Rewrite both sides and apply symmetry
  rw [<the two hypotheses>]
  exact (hsymm v w).symm
```

## Critical Pitfalls

1. **`fderiv_right` needs `norm_num`**: The bound `1 + 1 <= 2` at type `WithTop NNInfty` requires `norm_num`, NOT `simp`.
2. **`hsymm v w` vs `hsymm w v`**: Check the argument order. `IsSymmSndFDerivAt` gives `fderiv(fderiv f) x v w = fderiv(fderiv f) x w v`. You may need `.symm`.
3. **The `show ... from rfl` trick**: Lean sometimes doesn't see that `fun y => fderiv R f y v` and `fun y => (fderiv R f y) v` are definitionally equal in context. The explicit `show ... from rfl` rewrite fixes this.
4. **`ContinuousLinearMap.ext_iff.mp`**: Converts a CLM equality `L = M` to pointwise `L v = M v`.

## When You Need This

- Proving `curl(grad f) = 0`
- Proving `div(curl F) = 0`
- Proving `curl(curl F) = grad(div F) - nabla^2 F`
- Any identity involving commuting partial derivative orders
