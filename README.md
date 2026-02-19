# pbpl-coq

Formal Coq proofs that the **Physical Brick Programming Language (PBPL)** is Turing-complete.

## What is PBPL?

PBPL is the programming language of the [BrixIT](https://www.drbartha.com/) game console: a hands-on educational toy where children physically snap together coloured bricks to build programs. Each brick encodes a token (variable, number, operator, control-flow), and the chain of bricks attached to the console constitutes the program.

## What does this repo prove?

We prove **Turing-completeness of PBPL** by showing it can simulate any **2-counter Minsky machine**, a well-known minimal model of computation equivalent to a Turing machine.

The proof has two layers:

1. **Physical layer**: The compiled program is representable as a valid brick tree satisfying all physical hardware constraints (`wf_tree`).
2. **Semantic layer**: The small-step operational semantics of the flat PBPL program faithfully simulate every step of the Minsky machine (forward simulation).

The top-level theorem:

```coq
Theorem pbpl_turing_complete :
  forall (mp : minsky_program),
    wf_tree (compile_tree mp) /\
    (forall mc1 mc2,
      minsky_step mp mc1 mc2 ->
      forall pc1, match_config mp mc1 pc1 ->
      exists pc2,
        star (step (compile mp)) pc1 pc2 /\
        match_config mp mc2 pc2).
```

`Print Assumptions pbpl_turing_complete` returns **"Closed under the global context"**: no axioms beyond Coq's built-in logic are used.

## File structure

| File | Contents |
|------|----------|
| `Util.v` | Shared helpers: variable maps (`store`), reflexive-transitive closure (`star`) |
| `BrickTree.v` | Physical brick tree model, well-formedness predicate (`wf_tree`), `flatten` |
| `PBPL.v` | PBPL abstract syntax, `fetch`, small-step semantics (`step`) |
| `Minsky.v` | 2-counter Minsky machine (`minsky_step`) |
| `Compile.v` | Compiler `compile : minsky_program → program`, fetch correctness lemmas |
| `Simulation.v` | Forward simulation proof + `pbpl_turing_complete` |

## Label scheme

Each Minsky instruction `i` compiles to PBPL labels as follows:

| Instruction | Label | PBPL statement |
|-------------|-------|----------------|
| `INC(C, j)` | `2*i` | `SInc var (2*j)` |
| `DEC(C, j, k)` | `2*i` | `SIf var == 0 → (2*k) else (2*i+1)` |
| `DEC(C, j, k)` | `2*i+1` | `SDec var (2*j)` |
| `HALT` | `2*i` | `SHalt` |

## Building

Requires **Coq 8.18+** (tested on 8.20.1).

```bash
# Install Coq (Ubuntu/Debian)
sudo apt install coq

# Build
make

# Verify no axioms
coqc -Q . PBPL -require PBPL.Simulation \
  <<< 'Print Assumptions pbpl_turing_complete.'
```

## About BrixIT

BrixIT is an educational toy designed to teach programming to children through physical block coding and interactive play. Visit [drbartha.com](https://www.drbartha.com/) to learn more.
