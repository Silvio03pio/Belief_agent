"""
main.py  –  Demonstration script for the Belief Revision Engine.

DTU 02180 Introduction to Artificial Intelligence – Belief Revision Assignment 2026.

This script:
  1. Creates a sample belief base with formulas and assigned priorities.
  2. Demonstrates contraction, expansion, and revision with worked examples.
  3. Runs the complete AGM postulate test suite.
  4. Prints the belief base state at each step.

Run with:
    python main.py
"""

import sys
import os

# Make sure the engine directory is on the path when run from outside it
sys.path.insert(0, os.path.dirname(__file__))

from formula import parse, pretty
from belief_base import BeliefBase
from resolution import pl_resolution, is_consistent
from agm_tests import run_all_tests


# ---------------------------------------------------------------------------
# Pretty-printing helpers
# ---------------------------------------------------------------------------

def section(title: str):
    print("\n" + "=" * 70)
    print(f"  {title}")
    print("=" * 70)


def subsection(title: str):
    print(f"\n--- {title} ---")


def show_bb(label: str, bb: BeliefBase):
    if not bb.beliefs:
        print(f"  {label}: ∅  (empty belief base)")
    else:
        items = ", ".join(str(f) for f in bb.beliefs)
        print(f"  {label}: [{items}]")
        print(f"          (priority: index 0 = most entrenched)")


def show_entailment(label: str, bb: BeliefBase, query):
    result = bb.entails(query)
    sym = "⊨" if result else "⊭"
    print(f"  {label} {sym} {query}  →  {'YES' if result else 'NO'}")


def prompt_formula(prompt: str):
    """Read and parse a single formula from stdin."""
    while True:
        raw = input(prompt).strip()
        if not raw:
            print("  Please enter a formula.")
            continue
        try:
            return parse(raw)
        except ValueError as exc:
            print(f"  Parse error: {exc}")
            print("  Examples: p, ~p, (p & q), (p => q), (p <=> q)")


def prompt_belief_base():
    """Build a belief base from comma-separated user input."""
    while True:
        raw = input("Enter beliefs separated by commas (example: p, (p => q), r): ").strip()
        if not raw:
            return BeliefBase([])
        parts = [part.strip() for part in raw.split(",") if part.strip()]
        try:
            return BeliefBase([parse(part) for part in parts])
        except ValueError as exc:
            print(f"  Parse error: {exc}")
            print("  Please try again with fully parenthesised binary formulas.")


def run_interactive_mode():
    """Simple interactive shell for testing belief change operations."""
    section("INTERACTIVE MODE")
    print("Type your own belief base and try expansion, contraction, revision, or entailment.")
    print("Type 'exit' at the action prompt to leave interactive mode.")

    bb = prompt_belief_base()

    while True:
        print("\nCurrent belief base:")
        show_bb("B", bb)
        print(f"  Consistent? {bb.is_consistent()}")
        action = input("\nChoose action [expand / contract / revise / entails / reset / exit]: ").strip().lower()

        if action == "exit":
            print("Leaving interactive mode.")
            return
        if action == "reset":
            bb = prompt_belief_base()
            continue
        if action == "expand":
            phi = prompt_formula("Enter φ for B + φ: ")
            bb = bb.expand(phi)
            print(f"  Result: B + {phi} = {bb}")
            continue
        if action == "contract":
            phi = prompt_formula("Enter φ for B ÷ φ: ")
            bb = bb.contract(phi)
            print(f"  Result: B ÷ {phi} = {bb}")
            continue
        if action == "revise":
            phi = prompt_formula("Enter φ for B * φ: ")
            bb = bb.revise(phi)
            print(f"  Result: B * {phi} = {bb}")
            continue
        if action == "entails":
            phi = prompt_formula("Enter query φ to test whether B entails φ: ")
            show_entailment("B", bb, phi)
            continue

        print("  Unknown action. Please choose expand, contract, revise, entails, reset, or exit.")


# ---------------------------------------------------------------------------
# Part 1: Basic formula parsing and CNF demonstration
# ---------------------------------------------------------------------------

def demo_parsing():
    section("PART 1: Formula Parsing and CNF Conversion")

    formulas = [
        "p",
        "~p",
        "(p & q)",
        "(p | q)",
        "(p => q)",
        "(p <=> q)",
        "~(p & q)",
        "((p => q) & (q => r))",
        "(p <=> (q | r))",
    ]

    print("\nParsing formula strings into AST objects:")
    for s in formulas:
        f = parse(s)
        print(f"  parse({s!r:25})  →  {f}")

    print("\nCNF clause representations  (each clause is a frozenset of literals):")
    from cnf import to_cnf_clauses
    examples = [
        ("(p => q)",           "p → q  becomes  ¬p ∨ q"),
        ("(p <=> q)",          "p ↔ q  becomes  (¬p ∨ q) ∧ (¬q ∨ p)"),
        ("~(p & q)",           "¬(p ∧ q)  →  ¬p ∨ ¬q"),
        ("(p | (q & r))",      "p ∨ (q ∧ r)  →  (p ∨ q) ∧ (p ∨ r)"),
    ]
    for s, comment in examples:
        clauses = to_cnf_clauses(parse(s))
        clause_str = "  ∧  ".join(
            " ∨ ".join(f"{'' if pol else '¬'}{name}" for name, pol in sorted(c))
            for c in clauses
        )
        print(f"  {s:30}  →  CNF: {clause_str}")
        print(f"    ({comment})")


# ---------------------------------------------------------------------------
# Part 2: Resolution-based entailment demonstration
# ---------------------------------------------------------------------------

def demo_resolution():
    section("PART 2: Resolution-Based Entailment Checker")

    print("\nDemonstrating KB ⊨ α via proof by refutation:")

    # Example from slides9: Bob believes {p, q}, does B ⊨ (p & q) ?
    p, q, r = parse("p"), parse("q"), parse("r")
    p_imp_q = parse("(p => q)")
    neg_q = parse("~q")

    tests = [
        ([p, q],         parse("(p & q)"),     True,  "From {p, q},  ⊨ (p & q)?"),
        ([p, p_imp_q],   q,                    True,  "From {p, (p=>q)},  ⊨ q?  [Modus Ponens]"),
        ([p, q],         r,                    False, "From {p, q},  ⊨ r?  [r not mentioned]"),
        ([p],            parse("(p | q)"),      True,  "From {p},  ⊨ (p | q)?  [weakening]"),
        ([p, neg_q],     parse("(p & ~q)"),     True,  "From {p, ~q},  ⊨ (p & ~q)?"),
        ([],             parse("(p | ~p)"),     True,  "Empty KB  ⊨ (p | ~p)?  [tautology]"),
        ([],             p,                    False, "Empty KB  ⊨ p?  [no]"),
    ]

    for kb, query, expected, desc in tests:
        result = pl_resolution(kb, query)
        status = "✓" if result == expected else "✗ WRONG"
        sym = "⊨" if result else "⊭"
        print(f"  {status}  {desc}")
        print(f"       Answer: {sym}  {query}")


# ---------------------------------------------------------------------------
# Part 3: Belief base demonstration
# ---------------------------------------------------------------------------

def demo_belief_base():
    section("PART 3: Belief Base — Expansion, Contraction, Revision")

    p         = parse("p")
    q         = parse("q")
    r         = parse("r")
    neg_q     = parse("~q")
    p_imp_q   = parse("(p => q)")

    # ----------------------------------------------------------------
    # 3a: Expansion
    # ----------------------------------------------------------------
    subsection("3a: Expansion  B + φ")
    bb = BeliefBase([p, q])
    show_bb("B", bb)
    print(f"\n  Expanding with φ = r ...")
    bb_expanded = bb.expand(r)
    show_bb("B + r", bb_expanded)
    show_entailment("B + r", bb_expanded, r)

    print(f"\n  Note: expansion can introduce inconsistency.")
    bb_incon = bb.expand(neg_q)
    show_bb("B + ~q  (after B = {p,q})", bb_incon)
    print(f"  Consistent? {bb_incon.is_consistent()}  (expected False – both q and ~q present)")

    # ----------------------------------------------------------------
    # 3b: Contraction
    # ----------------------------------------------------------------
    subsection("3b: Contraction  B ÷ φ")
    print("\n  Example from slides9: Bob believes {p, q}, contracts by q.")
    bb = BeliefBase([p, q])
    show_bb("B", bb)
    print(f"\n  Contracting by φ = q ...")
    bb_c = bb.contract(q)
    show_bb("B ÷ q", bb_c)
    show_entailment("B ÷ q", bb_c, q)
    print(f"  (q should no longer be entailed)")

    print()
    print("  Example: B = {p, q, (p=>q)}, contract by q.")
    bb2 = BeliefBase([p, q, p_imp_q])
    show_bb("B", bb2)
    bb2_c = bb2.contract(q)
    show_bb("B ÷ q", bb2_c)
    show_entailment("B ÷ q", bb2_c, q)

    print()
    print("  Vacuous contraction: B = {p}, contract by q (B does not entail q).")
    bb3 = BeliefBase([p])
    show_bb("B", bb3)
    bb3_c = bb3.contract(q)
    show_bb("B ÷ q", bb3_c)
    print("  (B unchanged since B ⊭ q)")

    # ----------------------------------------------------------------
    # 3c: Revision
    # ----------------------------------------------------------------
    subsection("3c: Revision  B * φ  (Levi Identity)")
    print("\n  B * φ := (B ÷ ¬φ) + φ")

    print("\n  Example 1 (slides9): B = {p, q}, revise with ~q.")
    bb = BeliefBase([p, q])
    show_bb("B", bb)
    print(f"\n  Step 1: Contract by ¬(~q) = q ...")
    bb_contracted = bb.contract(q)
    show_bb("  B ÷ q", bb_contracted)
    print(f"  Step 2: Expand with ~q ...")
    bb_revised = bb_contracted.expand(neg_q)
    show_bb("  (B ÷ q) + ~q  =  B * ~q", bb_revised)
    show_entailment("B * ~q", bb_revised, neg_q)
    show_entailment("B * ~q", bb_revised, q)
    print(f"  Consistent? {bb_revised.is_consistent()}")

    print("\n  Example 2: B = {p, q, (p=>q)}, revise with ~q.")
    bb2 = BeliefBase([p, q, p_imp_q])
    show_bb("B", bb2)
    bb2_revised = bb2.revise(neg_q)
    show_bb("B * ~q", bb2_revised)
    show_entailment("B * ~q", bb2_revised, neg_q)
    show_entailment("B * ~q", bb2_revised, q)
    show_entailment("B * ~q", bb2_revised, p)
    print(f"  Consistent? {bb2_revised.is_consistent()}")

    print("\n  Example 3: B = {p, (p=>q), r}, revise with ~q.")
    bb3 = BeliefBase([p, p_imp_q, r])
    show_bb("B", bb3)
    bb3_revised = bb3.revise(neg_q)
    show_bb("B * ~q", bb3_revised)
    show_entailment("B * ~q", bb3_revised, neg_q)
    print(f"  Consistent? {bb3_revised.is_consistent()}")

    print("\n  Example 4 (vacuity): B = {p}, revise with q (no conflict).")
    bb4 = BeliefBase([p])
    show_bb("B", bb4)
    bb4_revised = bb4.revise(q)
    show_bb("B * q", bb4_revised)
    show_entailment("B * q", bb4_revised, q)
    show_entailment("B * q", bb4_revised, p)
    print(f"  Since B ⊭ ~q, this should equal B + q = {{p, q}}")

    # ----------------------------------------------------------------
    # 3d: Consistency check
    # ----------------------------------------------------------------
    subsection("3d: Consistency Check")
    tests = [
        ([p, q],              "consistent"),
        ([p, neg_q],          "consistent"),
        ([p, q, neg_q],       "INCONSISTENT"),
        ([p_imp_q, p, neg_q], "INCONSISTENT"),
        ([],                  "consistent (empty base)"),
    ]
    for formulas, note in tests:
        bb = BeliefBase(formulas)
        c = bb.is_consistent()
        items = "{" + ", ".join(str(f) for f in formulas) + "}"
        print(f"  {items:30}  →  {'consistent' if c else 'INCONSISTENT'}   (expected: {note})")


# ---------------------------------------------------------------------------
# Part 4: AGM postulate test suite
# ---------------------------------------------------------------------------

def demo_agm_tests():
    section("PART 4: AGM Postulate Test Suite")
    run_all_tests()


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("        ══════════════════════════════════════════════════        ")
    print("        BELIEF REVISION ENGINE — DTU 02180 Assignment 2026        ")
    print("        ══════════════════════════════════════════════════        ")

    # Demo functions kept for reference, but disabled for normal use.
    # demo_parsing()
    # demo_resolution()
    # demo_belief_base()
    # demo_agm_tests()
    #
    # print("\n" + "=" * 70)
    # print("  Demo complete.")
    # print("=" * 70)

    if sys.stdin.isatty():
        run_interactive_mode()
