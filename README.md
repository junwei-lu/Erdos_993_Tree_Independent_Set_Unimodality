# Erdos problem #993 - a Lean 4 formalization

A complete, machine-checked formalization of 
*Unimodality of independence polynomials for sufficiently large forests* by Ethan X. Fang, Junwei Lu, Eran Nevo, Yuan Yao, and Hailun Zheng, [https://arxiv.org/pdf/2609.20961](https://arxiv.org/pdf/2609.20961),
 in Lean 4 over Mathlib.

The theorem proved here is:

> There is an absolute integer `N0` such that the independence sequence of every
> forest with at least `N0` vertices is unimodal.

The library compiles with **zero `sorry`**, and the headline results audit to
Lean's three standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## The formal statement

In Lean, the two headline forms are:

```lean
theorem main_fin :
    ∃ N₀ : ℕ, ∀ (n : ℕ), N₀ ≤ n → ∀ (G : SimpleGraph (Fin n)), G.IsAcyclic →
      IsUnimodal (icoeff G Finset.univ)

theorem unimodal_of_isAcyclic :
    ∃ N₀ : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.IsAcyclic → N₀ ≤ Fintype.card V → IsUnimodal (icoeff G univ)
```

`main_fin` gives the absolute threshold on `Fin n`; `unimodal_of_isAcyclic`
transfers the same `N₀` to arbitrary finite vertex types.

## Where the main theorem is

The headline statements live in:

- `ErdosProblem993/Main.lean`: `main_fin` (Theorem 1.1 on `Fin n`)
- `ErdosProblem993/Transfer.lean`: `unimodal_of_isAcyclic` (same theorem on any finite type)
- `ErdosProblem993/AxiomCheck.lean`: `#print axioms` audit for all major results

The primitive definitions used in the theorem statement (`icoeff`, `alpha`,
`IsUnimodal`, `Zgen`, graph neighborhood/degree helpers) live in
`ErdosProblem993/Basic.lean`.


## How to certify the proof

Toolchain is pinned in this repository:

- Lean `v4.29.1`
- Mathlib commit `5e932f97dd25535344f80f9dd8da3aab83df0fe6`

Build:

```bash
lake build
```

Check for no actual `sorry` tokens in source:

```bash
rg -n "\bsorry\b" ErdosProblem993
```

Audit the axiom footprint of headline theorems:

```bash
lake env lean ErdosProblem993/AxiomCheck.lean
```

Expected result: each listed theorem depends only on
`propext`, `Classical.choice`, `Quot.sound`, and not `sorryAx`.
