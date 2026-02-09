---
name: lean-smoothness-coercions
description: Handling WithTop NNInfty (smoothness order) coercion and arithmetic issues in Lean 4 / Mathlib. Use when ContDiff, fderiv_right, or differentiable goals fail with type mismatches or unsolved arithmetic.
user-invocable: false
---

# Smoothness Order Coercions in Mathlib

## The Problem

Mathlib's `ContDiff R n f` uses `n : WithTop NNInfty` (also written `WithTop ℕ∞`). This type has non-trivial coercion from `Nat`, and arithmetic goals at this type behave differently than you'd expect.

## Common Goals and How to Close Them

### `(1 : WithTop ℕ∞) ≠ 0`
```lean
by simp
```
Appears when using `ContDiff.differentiable`:
```lean
(hf.differentiable (by simp)).differentiableAt
```

### `1 + 1 ≤ 2` at `WithTop ℕ∞`
```lean
by norm_num
```
**NOT `by simp`!** This is the most common mistake. Appears when using `ContDiff.fderiv_right`:
```lean
hf.fderiv_right (by norm_num)  -- C^2 => fderiv is C^1 (needs 1+1 <= 2)
```

### `(2 : WithTop ℕ∞) ≠ 0`
```lean
by simp
```

### `1 ≤ 2` at `WithTop ℕ∞`
```lean
by norm_num
```

### General pattern
- **Inequality/ordering goals** (`<=`, `<`): try `by norm_num` first
- **Disequality goals** (`≠ 0`): try `by simp` first
- **If both fail**: try `by omega` or `by decide`

## Quick Reference Table

| Goal | Tactic | Context |
|------|--------|---------|
| `(n : WithTop ℕ∞) ≠ 0` | `by simp` | `ContDiff.differentiable` |
| `m + 1 ≤ n` at `WithTop ℕ∞` | `by norm_num` | `ContDiff.fderiv_right` |
| `m ≤ n` at `WithTop ℕ∞` | `by norm_num` | `ContDiff.of_le` |
| `(n : ℕ) → WithTop ℕ∞` coercion | automatic | Just write the natural number |

## The `ContDiff` API Summary

| Lemma | Type Signature | Closing Tactic for Bound |
|-------|---------------|-------------------------|
| `ContDiff.differentiable` | `ContDiff R n f → n ≠ 0 → Differentiable R f` | `by simp` |
| `ContDiff.fderiv_right` | `ContDiff R n f → m + 1 ≤ n → ContDiff R m (fderiv R f)` | `by norm_num` |
| `ContDiffAt.isSymmSndFDerivAt` | `ContDiffAt R n f x → 2 ≤ n → IsSymmSndFDerivAt R f x` | `by simp` (2 ≤ 2) |
| `ContDiff.of_le` | `ContDiff R n f → m ≤ n → ContDiff R m f` | `by norm_num` |

## Pitfall: `ℕ∞` vs `WithTop ℕ∞`

The smoothness order type is `WithTop ℕ∞` (which is `WithTop (WithTop ℕ)`), NOT just `ℕ∞`. This double-wrapping means:
- `⊤ : WithTop ℕ∞` means C^infinity (smooth)
- `(2 : WithTop ℕ∞)` means C^2
- Arithmetic is more complex than plain `ℕ` or `ℕ∞`

If you get type errors mentioning `ENNReal` or `ℕ∞` vs `WithTop ℕ∞`, check that you're not confusing the two.

## Pitfall: `minSmoothness` and Custom Abbreviations

If you define abbreviations like `def minSmoothness : WithTop ℕ∞ := 2`, be careful:
- `simp [minSmoothness]` may create "unused simp argument" warnings if `minSmoothness` is already unfolded
- Prefer using literal `2` directly in `ContDiff R 2 f` rather than custom names
