---
name: lean-differentiability-chain
description: Threading differentiability hypotheses from ContDiff through fderiv applications in Lean 4 / Mathlib. Use when you need DifferentiableAt proofs for expressions involving fderiv, or when fderiv_sub/fderiv_add/fderiv_const_smul fails due to missing differentiability.
user-invocable: false
---

# Differentiability Threading from ContDiff

## The Problem

Mathlib's `fderiv_sub`, `fderiv_add`, `fderiv_const_smul` all require `DifferentiableAt` proofs. When your expressions involve `fderiv` (i.e., you're working with second derivatives), getting these proofs requires a specific chain of steps.

## The Chain

Starting from `hf : ContDiff R 2 f`:

### Level 1: fderiv is C^1
```lean
have hfderiv_c1 : ContDiff R 1 (fderiv R f) :=
  hf.fderiv_right (by norm_num)  -- 1 + 1 <= 2, needs norm_num!
```

### Level 2: fderiv is differentiable
```lean
have hdf : DifferentiableAt R (fderiv R f) x :=
  (hfderiv_c1.differentiable (by simp)).differentiableAt
  --                          ^^^^^^^^ proves 1 != 0 at WithTop NNInfty
```

### Level 3: fderiv applied to constant vector is differentiable
```lean
have hpdiff : DifferentiableAt R (fun y => fderiv R f y v) x :=
  hdf.clm_apply (differentiableAt_const v)
```

This is the key step! `DifferentiableAt.clm_apply` says: if `c` is differentiable as a CLM-valued function and `u` is differentiable, then `fun y => c y (u y)` is differentiable.

## Common Patterns

### For IsC2Vector (component-wise C^2)
```lean
-- Given: hF : IsC2Vector F  (i.e., forall j, ContDiff R 2 (fun x => F x j))
-- Need: DifferentiableAt R (fun y => F y j) x
have : DifferentiableAt R (fun y => F y j) x :=
  ((hF j).differentiable (by simp)).differentiableAt
```

### For partial derivative expressions
```lean
-- Given: hF : IsC2Vector F
-- Need: DifferentiableAt R (fun y => partialDerivComp F i j y) x
-- where partialDerivComp F i j y = fderiv R (fun z => F z j) y (basisVec i)
have : DifferentiableAt R (fun y => partialDerivComp F i j y) x := by
  dsimp [partialDerivComp]
  have hfderiv_c1 : ContDiff R 1 (fderiv R (fun z => F z j)) :=
    (hF j).fderiv_right (by norm_num)
  have hdf : DifferentiableAt R (fderiv R (fun z => F z j)) x :=
    (hfderiv_c1.differentiable (by simp)).differentiableAt
  simpa using hdf.clm_apply (differentiableAt_const (basisVec i))
```

### For scalar-multiplied expressions
```lean
-- Given: hd : DifferentiableAt R f x
-- Need: DifferentiableAt R (fun y => c * f y) x
have : DifferentiableAt R (fun y => c * f y) x := hd.const_mul c
-- OR equivalently:
have : DifferentiableAt R (fun y => c * f y) x := (hd).const_smul c
```

## Critical Pitfalls

1. **`by simp` vs `by norm_num`**:
   - `ContDiff.differentiable` needs `n != 0` — use `by simp` (proves `(1 : WithTop NNInfty) != 0`)
   - `ContDiff.fderiv_right` needs `m + 1 <= n` — use `by norm_num` (proves `1 + 1 <= 2`)
   - Getting these mixed up causes silent failures or confusing type errors

2. **`simpa using` for clm_apply**: The goal after `dsimp [partialDerivComp]` may not exactly match the output of `hdf.clm_apply`. Use `simpa using` to let simp bridge the gap.

3. **Don't use `differentiableAt_fderiv`**: This doesn't exist. Use the chain above instead.

4. **`autoImplicit = false`**: If your project has this set, you must explicitly declare all variables. E.g., helper lemmas need `{F : VectorField}` explicit.

## Quick Reference

| Have | Need | Use |
|------|------|-----|
| `ContDiff R 2 f` | `ContDiff R 1 (fderiv R f)` | `.fderiv_right (by norm_num)` |
| `ContDiff R 1 g` | `Differentiable R g` | `.differentiable (by simp)` |
| `Differentiable R g` | `DifferentiableAt R g x` | `.differentiableAt` |
| `DifferentiableAt R c x` (CLM-valued) | `DifferentiableAt R (fun y => c y v) x` | `.clm_apply (differentiableAt_const v)` |
| `DifferentiableAt R f x` | `DifferentiableAt R (fun y => c * f y) x` | `.const_mul c` or `.const_smul c` |
| `ContDiff R 2 (fun x => F x j)` | `DifferentiableAt R (fun y => F y j) x` | `((hF j).differentiable (by simp)).differentiableAt` |
