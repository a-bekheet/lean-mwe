---
name: lean-fderiv-linearity
description: Proving fderiv distributes over addition, subtraction, negation, and scalar multiplication in Lean 4 / Mathlib. Use when proving curl/div/grad linearity or splitting fderiv of compound expressions.
user-invocable: false
---

# fderiv Linearity Proofs

## The Problem

When you have `fderiv R (fun y => f y + g y) x` or `fderiv R (fun y => f y - g y) x`, Lean does NOT automatically distribute `fderiv` over the arithmetic. You must explicitly use `fderiv_add`, `fderiv_sub`, etc., and each requires `DifferentiableAt` proofs.

## Core Lemmas

### fderiv_add
```lean
fderiv_add (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x) :
  fderiv R (fun y => f y + g y) x = fderiv R f x + fderiv R g x
```

### fderiv_sub
```lean
fderiv_sub (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x) :
  fderiv R (fun y => f y - g y) x = fderiv R f x - fderiv R g x
```

### fderiv_neg
```lean
fderiv_neg :
  fderiv R (fun y => -f y) x = -fderiv R f x
-- No differentiability hypothesis needed!
```

### fderiv_const_smul
```lean
fderiv_const_smul (hf : DifferentiableAt R f x) (c : R) :
  fderiv R (fun y => c • f y) x = c • fderiv R f x
```

### fderiv_sum
```lean
fderiv_sum (h : forall i in s, DifferentiableAt R (A i) x) :
  fderiv R (sum i in s, A i) x = sum i in s, fderiv R (A i) x
```

## Extracting Pointwise Values from CLM Equalities

These lemmas give equalities of `ContinuousLinearMap`s. To get scalar equalities (applied to a vector `v`), use:

```lean
-- From CLM equality to pointwise
congrArg (fun L => L v) (fderiv_sub hf hg)
-- This gives: fderiv R (fun y => f y - g y) x v = fderiv R f x v - fderiv R g x v
```

Or define a helper:
```lean
have hsubApply (f g : Vec3 -> R) (hf : DifferentiableAt R f x)
    (hg : DifferentiableAt R g x) (v : Vec3) :
    fderiv R (fun y => f y - g y) x v = fderiv R f x v - fderiv R g x v :=
  congrArg (fun L => L v) (fderiv_sub hf hg)
```

## Pattern: Curl Linearity

The curl components involve `fderiv R (fun y => F y j) x (basisVec i)`. To prove curl distributes over operations:

### curl_neg (no hypotheses needed)
```lean
theorem curl_neg (F : VectorField) (x : Vec3) (j : Fin 3) :
    curl (fun y k => -(F y k)) x j = -(curl F x j) := by
  fin_cases j <;>
    simp only [curl, partialDerivComp, Fin.isValue] <;>
    simp only [show (fun y => -(F y _)) = (-(fun y => F y _)) from rfl,
               fderiv_neg, ContinuousLinearMap.neg_apply] <;>
    ring
```

### curl_add (needs DifferentiableAt)
```lean
theorem curl_add (F G : VectorField) (x : Vec3)
    (hF : forall j, DifferentiableAt R (fun y => F y j) x)
    (hG : forall j, DifferentiableAt R (fun y => G y j) x) (j : Fin 3) :
    curl (fun y k => F y k + G y k) x j = curl F x j + curl G x j := by
  fin_cases j <;>
    simp only [curl, partialDerivComp, Fin.isValue] <;>
    simp only [show forall i : Fin 3, (fun y => F y i + G y i) =
      ((fun y => F y i) + (fun y => G y i)) from fun i => rfl,
      fderiv_add (hF _) (hG _), ContinuousLinearMap.add_apply] <;>
    ring
```

### curl_const_mul (needs DifferentiableAt)
```lean
-- Key trick: rewrite c * f as c • f to use fderiv_const_smul
simp only [show forall i : Fin 3, (fun y => c * F y i) = (c • (fun y => F y i)) from
  fun i => rfl, fderiv_const_smul (hF _),
  ContinuousLinearMap.smul_apply, smul_eq_mul]
```

## The `show ... from rfl` Trick

Lean often needs help seeing that `fun y => f y + g y` is the same as `(fun y => f y) + (fun y => g y)` (Pi.add). The pattern:
```lean
show (fun y => f y + g y) = ((fun y => f y) + (fun y => g y)) from rfl
```
forces the definitional unfolding so that `fderiv_add` can match.

Similarly for scalar multiplication:
```lean
show (fun y => c * f y) = (c • (fun y => f y)) from rfl
```
This works because `SMul R R` is definitionally `(*)` for `R = R`.

## Critical Pitfalls

1. **Always provide DifferentiableAt proofs**: `fderiv_add`, `fderiv_sub`, `fderiv_const_smul` will NOT work without them. See the `lean-differentiability-chain` skill for how to obtain these.

2. **`fderiv_neg` is hypothesis-free**: Unlike add/sub/smul, negation doesn't need differentiability (it's a continuous linear map itself).

3. **`ContinuousLinearMap.*_apply`**: After rewriting with `fderiv_add` etc., you get CLM operations (`+`, `-`, `smul`). Use `.add_apply`, `.sub_apply`, `.neg_apply`, `.smul_apply` to push these through to pointwise application.

4. **`smul_eq_mul`**: After `ContinuousLinearMap.smul_apply`, you get `c • (value : R)`. Use `smul_eq_mul` to convert this back to `c * value`.

5. **Finish with `ring`**: After all the rewrites, the remaining goal is usually a pure algebra identity. `ring` handles it.
