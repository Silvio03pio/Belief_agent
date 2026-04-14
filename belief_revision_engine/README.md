# Belief Revision Engine

DTU 02180 – Introduction to Artificial Intelligence, Spring 2026  
Group Assignment 2: Belief Revision

---

## Overview

A complete belief revision engine implemented in Python 3 using only the standard library.  
Implements the AGM framework for belief change as presented in DTU 02180 lectures 8–9 and AIMA Chapter 7.

---

## How to Run

```bash
python main.py
```

**Requirements:** Python 3.8 or higher.  No external dependencies.

---

## Source Files

| File | Purpose |
|------|---------|
| `formula.py` | Propositional formula AST nodes (`Atom`, `Not`, `And`, `Or`, `Implies`, `Biconditional`), recursive-descent parser, pretty-printer |
| `cnf.py` | Full CNF conversion: eliminate biconditionals → eliminate implications → push negation inward (De Morgan) → distribute OR over AND |
| `resolution.py` | PL-Resolution algorithm (AIMA Fig. 7.13): proof by refutation, consistency check |
| `belief_base.py` | `BeliefBase` class with priority ordering; expansion, contraction (partial meet), revision (Levi Identity) |
| `agm_tests.py` | AGM postulate test suite (R1–R5 for revision) with PASS/FAIL output |
| `main.py` | Full demonstration script — run this |

---

## Formula Syntax

Formulas are written as strings with the following notation:

| Connective | Symbol | Example |
|------------|--------|---------|
| Negation | `~` | `"~p"` |
| Conjunction | `&` | `"(p & q)"` |
| Disjunction | `\|` | `"(p \| q)"` |
| Implication | `=>` | `"(p => q)"` |
| Biconditional | `<=>` | `"(p <=> q)"` |

All binary operators must be parenthesised.  Atoms are lowercase strings.

**Example:**
```python
from formula import parse
f = parse("(p => q)")   # Implies(Atom('p'), Atom('q'))
```

---

## Belief Base and Priority

The belief base is an ordered list `[φ₀, φ₁, ..., φₙ]` where **index 0 = most entrenched** (highest priority).  During contraction, higher-priority beliefs are preferentially retained.

```python
from formula import parse
from belief_base import BeliefBase

p       = parse("p")
q       = parse("q")
p_imp_q = parse("(p => q)")

bb = BeliefBase([p, q, p_imp_q])   # p has highest priority
```

---

## Operations

### Expansion  `B + φ`
```python
bb_new = bb.expand(parse("r"))   # adds r at the end (lowest priority)
```

### Contraction  `B ÷ φ`
```python
bb_new = bb.contract(parse("q"))   # removes q and any beliefs that jointly entail q
```

### Revision  `B * φ`  (Levi Identity)
```python
bb_new = bb.revise(parse("~q"))    # = (B ÷ q) + ~q
```

---

## Example Input/Output

```
B = {p, q, (p=>q)}  (p has highest priority)
Revising with ~q:
  Step 1: Contract by q  →  B ÷ q = {p}
  Step 2: Expand by ~q   →  {p, ~q}
  B * ~q = {p, ~q}
```

---

## AGM Postulate Tests

The file `agm_tests.py` verifies five postulates for the revision operator `B * φ`:

| Postulate | Statement |
|-----------|-----------|
| R1 Success | `φ ∈ Cn(B * φ)` |
| R2 Inclusion | `B * φ ⊆ B + φ` |
| R3 Vacuity | If `¬φ ∉ Cn(B)` then `B * φ = B + φ` |
| R4 Consistency | `B * φ` is consistent (unless `φ` is a contradiction) |
| R5 Extensionality | If `φ ≡ ψ` then `B * φ = B * ψ` |

All 22 tests pass across 5 example belief bases.

Run just the tests:
```bash
python agm_tests.py
```

---

## Implementation Notes

- **No external libraries** — no `sympy`, no SAT solvers. Everything is from scratch.
- **CNF conversion** follows AIMA §7.5.2 exactly (4 steps).
- **Resolution** implements AIMA Figure 7.13 (PL-Resolution proof by refutation).
- **Contraction** uses partial meet contraction with a priority-based selection function.
- **Revision** uses the Levi Identity: `B * φ := (B ÷ ¬φ) + φ`.
