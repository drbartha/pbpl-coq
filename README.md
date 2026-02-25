# pbpl-coq

Formal Coq proofs that the **Physical Brick Programming Language (PBPL)** is Turing-complete.

## What is PBPL?

PBPL is the programming language of the [DrBartha Toys](https://www.drbartha.com/) game console: a hands-on educational toy where children physically snap together coloured bricks to build programs. Each brick encodes a token (variable, number, operator, control-flow), and the chain of bricks attached to the console constitutes the program.

## What does this repo prove?

We prove **Turing-completeness of PBPL** by showing it can simulate any **2-counter Minsky machine**, a well-known minimal model of computation equivalent to a Turing machine.

The proof has three layers:

1. **Physical layer**: The compiled program is representable as a valid brick tree satisfying all physical hardware constraints (`wf_tree`), and its tree-level semantics agree with flat token-list evaluation (`compile_btree_tokens_agree`).
2. **Tree–program bridge**: The brick-tree step relation and the flat PBPL step relation are equivalent on compiled programs (`compile_btree_correct`).
3. **Semantic layer**: The small-step operational semantics faithfully simulate every step of the Minsky machine (forward simulation).

### Flat-program theorem (`Simulation.v`)

The abstract PBPL machine (a flat list of labeled statements) simulates any Minsky machine:

```coq
Theorem pbpl_turing_complete :
  forall (mp : minsky_program),
    wf_tree (compile_tree mp) /\
    (forall mc1 mc2,
      minsky_step mp mc1 mc2 ->
      forall pc1, match_config mc1 pc1 ->
      exists pc2,
        star (step (compile mp)) pc1 pc2 /\
        match_config mc2 pc2).
```

### Brick-tree theorem (`BrickSemantics.v`)

The mathematical PBPL machine, where each labeled instruction is an explicit brick subtree, also simulates any Minsky machine:

```coq
Theorem pbpl_machine_tc :
  forall (mp : minsky_program),
    (forall mc1 mc2,
      minsky_step mp mc1 mc2 ->
      forall pc1, match_config mc1 pc1 ->
      exists pc2,
        star (bt_step (compile_btree mp)) pc1 pc2 /\
        match_config mc2 pc2).
```

### Tree ↔ flat-program bridge (`BrickSemantics.v`)

The brick-tree step relation and the flat PBPL step relation coincide on every compiled program - neither model is accidentally more expressive than the other:

```coq
Theorem compile_btree_correct : forall mp l s l' s',
  bt_step (compile_btree mp) (l, s) (l', s') <->
  step (compile mp) (l, s) (l', s').
```

### Physical token-list validation (`BrickSemantics.v`)

`eval_tokens` is the ground-truth physical model: it directly pattern-matches the flat token list that a daisy-chained brick row produces. `eval_tree` is the mathematical tree model. The following corollary proves they always agree on compiled trees, closing the gap between the abstract proof and the physical hardware:

```coq
Corollary compile_btree_tokens_agree : forall mp l t s,
  In (l, t) (compile_btree mp) ->
  eval_tree t s = eval_tokens (flatten t) s.
```

Additionally, every compiled tree is well-formed:

```coq
Lemma compile_btree_entries_wf : forall mp l t,
  In (l, t) (compile_btree mp) -> wf_tree t.
```

All five results return **"Closed under the global context"** under `Print Assumptions`: no axioms beyond Coq's built-in logic are used.

## File structure

| File | Contents |
|------|----------|
| `Util.v` | Shared helpers: variable maps (`store`), reflexive-transitive closure (`star`) |
| `BrickTree.v` | Physical brick tree model, well-formedness predicate (`wf_tree`), `flatten` |
| `PBPL.v` | PBPL abstract syntax, `fetch`, small-step semantics (`step`) |
| `Minsky.v` | 2-counter Minsky machine (`minsky_step`) |
| `Compile.v` | Compiler `compile : minsky_program → program`, fetch correctness lemmas |
| `Simulation.v` | Forward simulation proof + `pbpl_turing_complete` |
| `BrickSemantics.v` | Brick-tree machine (`bt_step`, `compile_btree`, `eval_tree`, `eval_tokens`) + `pbpl_machine_tc` + `compile_btree_correct` + `compile_btree_tokens_agree` |

## Label scheme

Each Minsky instruction `i` compiles to PBPL labels as follows:

| Instruction | Label | PBPL statement |
|-------------|-------|----------------|
| `INC(C, j)` | `2*i` | `SInc var (2*j)` |
| `DEC(C, j, k)` | `2*i` | `SIf var == 0 → (2*k) else (2*i+1)` |
| `DEC(C, j, k)` | `2*i+1` | `SDec var (2*j)` |
| `HALT` | `2*i` | `SHalt` |

## Proof chain summary

```
Minsky machine (Turing-complete by definition)
       │
       │  simulate_bt_step  (forward simulation, 1 or 2 bt_steps per Minsky step)
       v
bt_step on compile_btree   (brick-tree machine)
       │
       │  compile_btree_correct  (<=>  biconditional)
       v
step on compile             (flat PBPL machine)
       │
       │  compile_btree_tokens_agree  (eval_tree = eval_tokens ∘ flatten)
       v
eval_tokens                 (physical token-list model)
```

## Building

Requires **Coq 8.18+** (tested on 8.20.1).

```bash
# Install Coq (Ubuntu/Debian)
sudo apt install coq

# Build
make

# Verify no axioms (all key theorems)
cat > /tmp/chk.v << 'EOF'
Require Import PBPL.Simulation PBPL.BrickSemantics.
Print Assumptions pbpl_turing_complete.
Print Assumptions pbpl_machine_tc.
Print Assumptions compile_btree_correct.
Print Assumptions compile_btree_tokens_agree.
Print Assumptions compile_btree_entries_wf.
EOF
coqc -Q . PBPL /tmp/chk.v
```

## About DrBartha

DrBartha Toys is an educational toy designed to teach programming to children through physical block coding and interactive play. Visit [drbartha.com](https://www.drbartha.com/) to learn more.
