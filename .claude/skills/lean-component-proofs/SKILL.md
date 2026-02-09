---
name: lean-component-proofs
description: Component-wise proofs for vector calculus identities on Fin 3 vectors in Lean 4 / Mathlib. Use when proving identities like div(curl F) = 0 or curl(curl F) = grad(div F) - laplacian F that require expanding into components.
user-invocable: false
---

# Component-wise Vector Calculus Proofs

## The Problem

Vector calculus identities like `div(curl F) = 0` or `curl(curl F) = grad(div F) - nabla^2 F` cannot be proved abstractly — they require expanding each component into sums of partial derivatives, splitting compound `fderiv` expressions, and using algebraic cancellation (often via symmetry of mixed partials).

## Strategy Overview

1. **Define a local shorthand** for mixed second partial derivatives
2. **Prove differentiability** of partial derivative expressions (reusable helper)
3. **Prove symmetry** of mixed partials via `fderiv_apply_comm` (reusable helper)
4. **Prove a `fderiv_sub` pointwise helper** for extracting scalar values
5. **Expand each component** using the helpers
6. **Combine and cancel** using `ring` and symmetry

## The `d` Shorthand Pattern

Define a local function for second mixed partials:
```lean
let d : Fin 3 -> Fin 3 -> Fin 3 -> R :=
  fun i k j => fderiv R (fun y => partialDerivComp F i j y) x (basisVec k)
```

Here `d i k j` means "differentiate (partial_i F_j) in direction k", i.e., `partial_k partial_i F_j`.

## Reusable Helpers (define once per proof)

### Differentiability of partial derivative expressions
```lean
have hpdiff (i j : Fin 3) : DifferentiableAt R (fun y => partialDerivComp F i j y) x := by
  dsimp [partialDerivComp]
  have hfderiv_c1 : ContDiff R 1 (fderiv R (fun z => F z j)) :=
    (hF j).fderiv_right (by norm_num)
  have hdf : DifferentiableAt R (fderiv R (fun z => F z j)) x :=
    (hfderiv_c1.differentiable (by simp)).differentiableAt
  simpa using hdf.clm_apply (differentiableAt_const (basisVec i))
```

### Symmetry of mixed partials
```lean
have hcomm (i k j : Fin 3) : d i k j = d k i j := by
  simpa [d, partialDerivComp] using
    (fderiv_apply_comm (fun y => F y j) (hF j) x (basisVec i) (basisVec k))
```

### Pointwise fderiv_sub
```lean
have hsubApply (f g : Vec3 -> R) (hf : DifferentiableAt R f x)
    (hg : DifferentiableAt R g x) (v : Vec3) :
    fderiv R (fun y => f y - g y) x v = fderiv R f x v - fderiv R g x v :=
  congrArg (fun L => L v) (fderiv_sub hf hg)
```

## Example: `div(curl F) = 0`

After setting up helpers, expand each diagonal component of `divergence (curl F)`:

```lean
-- Component 0: partial_0 of (curl F)_0 = partial_0 of (partial_1 F_2 - partial_2 F_1)
have h0 : partialDerivComp (curl F) 0 0 x = d 1 0 2 - d 2 0 1 := by
  simpa [d, curl, partialDerivComp, Fin.isValue] using
    hsubApply (fun y => partialDerivComp F 1 2 y) (fun y => partialDerivComp F 2 1 y)
      (hpdiff 1 2) (hpdiff 2 1) (basisVec 0)
-- Similar for h1, h2...
```

Then combine:
```lean
calc divergence (curl F) x
    = partialDerivComp (curl F) 0 0 x + partialDerivComp (curl F) 1 1 x +
        partialDerivComp (curl F) 2 2 x := by simp [divergence, Fin.sum_univ_three]
  _ = (d 1 0 2 - d 2 0 1) + (d 2 1 0 - d 0 1 2) + (d 0 2 1 - d 1 2 0) := by rw [h0, h1, h2]
  _ = 0 := by rw [hcomm 1 0 2, hcomm 2 1 0, hcomm 0 2 1]; ring
```

## Example: `curl(curl F) = grad(div F) - nabla^2 F`

This requires `funext j` then `fin_cases j` to handle each of the 3 components. For each component:

1. **Expand LHS**: The curl-of-curl component involves two `partialDerivComp (curl F)` terms, each of which is a difference that must be split with `hsubApply`
2. **Expand RHS**: `partialDeriv (divergence F) j` requires `fderiv_sum` to distribute over the sum, and `vectorLaplacian` unfolds directly
3. **Match using `hcomm`**: Rewrite certain `d i k j` terms to `d k i j` to make both sides match
4. **Close with `ring`**

Key helper for the RHS gradient-of-divergence expansion:
```lean
have hgraddiv (j : Fin 3) :
    partialDeriv (divergence F) j x = sum i : Fin 3, d i j i := by
  -- Use fderiv_sum to distribute fderiv over the Finset.sum in divergence
  have hsum := fderiv_sum (fun i _ => hpdiff i i)
  ...
```

## Useful `simp` Lemmas

- `Fin.sum_univ_three` — expands `sum i : Fin 3, f i` to `f 0 + f 1 + f 2`
- `Fin.isValue` — normalizes `Fin.val` applications
- `divergence`, `curl`, `partialDerivComp`, `partialDeriv` — unfold definitions

## Critical Pitfalls

1. **`simpa` vs `simp`**: Use `simpa [d, curl, partialDerivComp] using hsubApply ...` rather than rewriting manually. The `simpa` bridges definitional gaps between the goal and the applied lemma.

2. **Explicit `Fin 3` indices**: After `fin_cases`, you get concrete values `0`, `1`, `2`. The match arms in `curl` need `Fin.isValue` in simp to reduce.

3. **Don't try `omega` or `decide` for Fin arithmetic**: These often don't work. Use `simp [Fin.isValue]` or explicit `norm_num`.

4. **`Fin.sum_univ_three` is essential**: Without it, `divergence` stays as an opaque `Finset.sum` and nothing simplifies.

5. **The proof is unavoidably long**: `curl(curl F) = grad(div F) - nabla^2 F` needs ~100 lines because each of 3 components requires ~4 intermediate `have` statements. Don't try to golf it — clarity wins.
