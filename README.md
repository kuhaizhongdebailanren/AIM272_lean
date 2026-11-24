# AIM272_lean

## AIM272

[`AIM272/`](AIM272/) is a self-contained Lake project formalizing the Anderson–Kim positive-recurrence conjecture (AIM Open Applied Problems #272).

Toolchain: Lean 4.24.0, Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

```sh
cd AIM272 && lake exe cache get && lake build
```

What is proved, and what still takes an external hypothesis, is recorded in [`AIM272/README.md`](AIM272/README.md). In particular, `t1` and `t2` are proved inside Lean, while the continuous-time statement `t3` assumes `AIM272.ContinuousTime.NorrisJumpReturn`. The `#print axioms` audit is in [`AIM272/AXIOM_AUDIT.txt`](AIM272/AXIOM_AUDIT.txt): the audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## WACR

[`WACR/WACR.lean`](WACR/WACR.lean) is separate later work. It is not part of the AIM 272 proof and not part of the `AIM272` Lake package. It formalizes a direction theorem for absolute concentration robustness in weakly reversible networks (W-ACR). The final theorems take the positive steady-state existence theorem of Boros (2019, Theorem 1) as a hypothesis. The file header checks it in a Mathlib v4.19.0 project with `lake env lean`.
