"""
Belief revision engine REPL. Run with: python main.py
"""

import sys
import os

sys.path.insert(0, os.path.dirname(__file__))

# utf-8 output on windows so unicode symbols render correctly
if sys.platform == "win32":
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")
    sys.stdin  = io.TextIOWrapper(sys.stdin.buffer,  encoding="utf-8", errors="replace")

from formula import parse
from belief_base import BeliefBase
from cnf import to_cnf_clauses


def _ansi(code): return f"\033[{code}m"

RESET = _ansi(0)
BOLD = _ansi(1)
DIM = _ansi(2)
CYAN = _ansi(36)
GREEN = _ansi(32)
YELLOW = _ansi(33)
RED = _ansi(31)
BLUE = _ansi(34)
MAGENTA = _ansi(35)

def c(text, *codes): return "".join(codes) + str(text) + RESET
def info(msg):    print(c("  ℹ  " + msg, CYAN))
def ok(msg):      print(c("  ✓  " + msg, GREEN))
def warn(msg):    print(c("  ⚠  " + msg, YELLOW))
def err(msg):     print(c("  ✗  " + msg, RED))
def explain(msg): print(c("     " + msg, DIM))


def hr(char="─", width=68):
    print(c(char * width, DIM))

def header(title):
    print()
    print(c("┌" + "─" * (len(title) + 4) + "┐", CYAN))
    print(c("│  " + title + "  │", CYAN, BOLD))
    print(c("└" + "─" * (len(title) + 4) + "┘", CYAN))

def show_belief_base(bb: BeliefBase, label="Current Belief Base"):
    header(label)
    if not bb.beliefs:
        print(c("  ∅  (empty — no beliefs held)", DIM))
        return
    for i, f in enumerate(bb.beliefs):
        bar  = "█" * (len(bb.beliefs) - i) + "░" * i
        print(f"  {c(f'[{i}]', BOLD)}  {c(str(f), YELLOW)}   {c(bar[:8], DIM)}  priority {i}")
    print()
    consistent = bb.is_consistent()
    status = c("consistent ✓", GREEN) if consistent else c("INCONSISTENT ✗", RED)
    print(f"  Status: {status}")
    if not consistent:
        explain("The belief base contains a contradiction.")
    explain("index 0 = most entrenched, higher index = easier to remove")


def show_syntax():
    header("Input Syntax  (Propositional Logic Grammar)")
    rows = [
        ("Atom",          "R   W   B1   B2",              "capital letter, optional digit"),
        ("Negation",      "~R   ~W   ~(R & W)",           "prefix tilde"),
        ("Conjunction",   "(R & W)   (B1 & B2)",          "AND — needs parens"),
        ("Disjunction",   "(R | W)   (B1 | B2)",          "OR  — needs parens"),
        ("Implication",   "(R => W)   (B1 => B2)",        "IF…THEN — needs parens"),
        ("Biconditional", "(R <=> W)",                    "IF AND ONLY IF"),
        ("Nesting",       "((R => W) & (W => B1))",       "fully parenthesised"),
    ]
    print()
    print(f"  {'Connective':<16}  {'Example':<32}  {'Note'}")
    hr()
    for name, example, note in rows:
        print(f"  {c(name, BOLD):<25}  {c(example, YELLOW):<41}  {c(note, DIM)}")
    print()
    explain("Rule: every binary operator MUST be wrapped in parentheses.")
    print()
    print(c("  Quick examples:", BOLD))
    print(f"    {c('R', YELLOW)}                       just the atom R")
    print(f"    {c('~R', YELLOW)}                      not R")
    print(f"    {c('(R & W)', YELLOW)}                 R AND W")
    print(f"    {c('(R | W)', YELLOW)}                 R OR W")
    print(f"    {c('(R => W)', YELLOW)}                if R then W")
    print(f"    {c('(R <=> W)', YELLOW)}               R if and only if W")
    print(f"    {c('((R => W) & (W => B1))', YELLOW)}  transitivity chain")


def show_help():
    header("Available Commands")
    cmds = [
        ("add <formula> [priority]", "Expand: add φ to belief base (optional position 0..n)"),
        ("remove <formula>",         "Directly remove φ from the belief base"),
        ("contract <formula>",       "Contract: remove φ and its dependents (AGM)"),
        ("revise <formula>",         "Revise: update belief base to accept φ (Levi identity)"),
        ("entails <formula>",        "Check whether B ⊨ φ (resolution-based)"),
        ("cnf <formula>",            "Show the CNF clause representation of φ"),
        ("consistent",               "Check if the current belief base is consistent"),
        ("show",                     "Display the current belief base"),
        ("clear",                    "Reset to an empty belief base"),
        ("demo",                     "Run the automated demonstration"),
        ("tests",                    "Run the full AGM postulate test suite"),
        ("syntax",                   "Show the input syntax cheat sheet"),
        ("help",                     "Show this help message"),
        ("quit / exit",              "Exit the program"),
    ]
    print()
    for cmd, desc in cmds:
        print(f"  {c(cmd, YELLOW):<34}  {desc}")


def safe_parse(text: str):
    text = text.strip()
    if not text:
        err("No formula entered.")
        return None
    try:
        return parse(text)
    except Exception as e:
        err(f"Parse error: {e}")
        explain("Type  syntax  to see valid input examples.")
        return None


def cmd_add(bb: BeliefBase, args: str) -> BeliefBase:
    parts = args.split()
    priority = None

    # check if last token is an integer (priority position)
    if parts and parts[-1].isdigit():
        priority = int(parts[-1])
        formula_str = " ".join(parts[:-1])
    else:
        formula_str = args

    phi = safe_parse(formula_str)
    if phi is None:
        return bb

    print()
    print(c(f"  Operation: Expansion  B + {phi}", BOLD))
    explain("adds phi without checking consistency")
    print()

    if phi in bb.beliefs:
        warn(f"{phi} is already in the belief base. No change.")
        return bb

    new_bb = BeliefBase(list(bb.beliefs))
    new_bb.add(phi, priority)

    ok(f"Added: {phi}")
    if priority is not None:
        explain(f"inserted at priority position {priority} (0 = most entrenched)")
    else:
        explain(f"appended at priority {len(new_bb.beliefs) - 1} (least entrenched)")

    if not new_bb.is_consistent():
        warn("Belief base is now inconsistent.")
        explain("consider using  revise  to maintain consistency")

    show_belief_base(new_bb)
    return new_bb


def cmd_remove(bb: BeliefBase, args: str) -> BeliefBase:
    phi = safe_parse(args)
    if phi is None:
        return bb

    print()
    print(c(f"  Operation: Direct removal of {phi}", BOLD))
    explain("use  contract  for AGM contraction")
    print()

    if phi not in bb.beliefs:
        warn(f"{phi} is not in the belief base. Nothing removed.")
        return bb

    new_bb = BeliefBase([f for f in bb.beliefs if f != phi])
    ok(f"Removed: {phi}")
    show_belief_base(new_bb)
    return new_bb


def cmd_contract(bb: BeliefBase, args: str) -> BeliefBase:
    phi = safe_parse(args)
    if phi is None:
        return bb

    print()
    print(c(f"  Operation: Contraction  B ÷ {phi}", BOLD))
    explain("partial meet contraction: finds max subsets not entailing phi, returns intersection")
    print()

    if not bb.entails(phi):
        warn(f"B does not entail {phi}, contraction is vacuous (B unchanged)")
        return bb

    new_bb = bb.contract(phi)

    if new_bb.entails(phi):
        warn(f"B ÷ {phi} still entails {phi} (may be a tautology or follow from remaining beliefs)")
    else:
        ok(f"Contracted by: {phi}")
        explain(f"B now does NOT entail {phi}.")

    removed = [f for f in bb.beliefs if f not in new_bb.beliefs]
    if removed:
        explain(f"beliefs removed: {', '.join(str(f) for f in removed)}")
    else:
        explain("no beliefs were removed")

    show_belief_base(new_bb)
    return new_bb


def cmd_revise(bb: BeliefBase, args: str) -> BeliefBase:
    phi = safe_parse(args)
    if phi is None:
        return bb

    from formula import Not as FNot
    neg_phi = FNot(phi)

    print()
    print(c(f"  Operation: Revision  B * {phi}", BOLD))
    explain(f"Levi identity: contract by ~phi = {neg_phi}, then add phi")
    print()

    contracted = bb.contract(neg_phi)

    removed = [f for f in bb.beliefs if f not in contracted.beliefs]
    if removed:
        explain(f"  after contraction, removed: {', '.join(str(f) for f in removed)}")
    else:
        explain(f"  contraction was vacuous (B did not entail ~{phi})")

    new_bb = contracted.expand(phi)
    ok(f"Revised by: {phi}")

    if new_bb.entails(phi):
        explain(f"  ✓ B * {phi} now entails {phi}.")
    else:
        warn(f"  B * {phi} does not entail {phi} — unexpected!")

    if new_bb.is_consistent():
        explain(f"  ✓ Result is consistent.")
    else:
        warn(f"  Result is INCONSISTENT — {phi} itself may be a contradiction.")

    show_belief_base(new_bb)
    return new_bb


def cmd_entails(bb: BeliefBase, args: str):
    phi = safe_parse(args)
    if phi is None:
        return

    print()
    print(c(f"  Entailment check:  B ⊨ {phi} ?", BOLD))
    explain(f"adds ~({phi}) to the KB and tries to derive a contradiction")
    print()

    result = bb.entails(phi)
    sym = "⊨" if result else "⊭"
    colour = GREEN if result else YELLOW
    answer = "YES — φ is entailed" if result else "NO  — φ is not entailed"
    print(f"  {c(f'B {sym} {phi}', colour, BOLD)}   →  {c(answer, colour)}")

    if result:
        explain(f"The belief base logically implies {phi}.")
    else:
        explain(f"The belief base does not entail {phi}.")
        if not bb.beliefs:
            explain("(belief base is empty, only tautologies are entailed)")


def cmd_cnf(args: str):
    phi = safe_parse(args)
    if phi is None:
        return

    print()
    print(c(f"  CNF conversion of: {phi}", BOLD))
    explain("conjunction of clauses, each a disjunction of literals")
    print()

    clauses = to_cnf_clauses(phi)
    if not clauses:
        warn("No clauses produced (formula is a tautology).")
        return

    print(f"  {c(str(phi), YELLOW)}  →  CNF:")
    for i, clause in enumerate(clauses):
        literals = []
        for name, pol in sorted(clause):
            lit = name if pol else f"¬{name}"
            literals.append(c(lit, CYAN))
        clause_str = " ∨ ".join(literals) if literals else c("⊥  (empty clause = contradiction)", RED)
        print(f"    Clause {i+1}: {clause_str}")

    if len(clauses) == 1:
        explain("Single clause — formula is already a disjunction of literals.")
    else:
        explain(f"{len(clauses)} clauses connected by ∧ (AND).")


def cmd_consistent(bb: BeliefBase):
    print()
    print(c("  Consistency check", BOLD))
    explain("runs resolution on the KB to check for contradictions")
    print()

    result = bb.is_consistent()
    if result:
        ok("The belief base is CONSISTENT.")
        explain("There exists at least one truth assignment satisfying all beliefs.")
    else:
        err("The belief base is INCONSISTENT.")
        explain("The beliefs contain a contradiction — everything is entailed.")
        explain("Use  revise  or  remove  to restore consistency.")


def run_demo(bb: BeliefBase) -> BeliefBase:
    header("Automated Demonstration")
    print()
    print("  This demo walks through the core belief revision operations")
    print("  using a running example: Bob's weather beliefs.")
    print()
    input(c("  Press Enter to start...", DIM))

    steps = [
        ("add",      "R",         "Bob believes it is raining (R)."),
        ("add",      "W",          "Bob believes the ground is wet (W)."),
        ("add",      "(R => W)", "Bob believes: if R then W."),
        ("entails",  "W",          "Does Bob's belief base entail W?"),
        ("contract", "W",          "Bob is no longer sure about W."),
        ("entails",  "W",          "Does Bob still entail W after contraction?"),
        ("revise",   "~R",        "Bob learns it is NOT raining. Revise!"),
        ("entails",  "~R",        "Does Bob now believe ~R?"),
        ("entails",  "R",         "Does Bob still believe R?"),
    ]

    for op, arg, narration in steps:
        print()
        hr("·")
        print(c(f"  [{op.upper()}]  {narration}", MAGENTA, BOLD))
        hr("·")
        input(c(f"  > {op} {arg}  (press Enter to execute)", DIM))

        if op == "add":
            bb = cmd_add(bb, arg)
        elif op == "entails":
            cmd_entails(bb, arg)
        elif op == "contract":
            bb = cmd_contract(bb, arg)
        elif op == "revise":
            bb = cmd_revise(bb, arg)

    print()
    ok("Demo complete. You can continue exploring in the REPL.")
    return bb


def run_tests():
    header("AGM Postulate Test Suite")
    explain("Running automated tests from agm_tests.py ...")
    print()
    try:
        from agm_tests import run_all_tests
        run_all_tests()
    except Exception as e:
        err(f"Test runner failed: {e}")


def main():
    # enable ANSI on windows
    if sys.platform == "win32":
        os.system("")

    print()
    print(c("╔══════════════════════════════════════════════════════════════════╗", CYAN, BOLD))
    print(c("║                   BELIEF REVISION ENGINE                        ║", CYAN, BOLD))
    print(c("║           Interactive REPL  ·  Type  help  to get started       ║", CYAN))
    print(c("╚══════════════════════════════════════════════════════════════════╝", CYAN, BOLD))
    print()

    show_syntax()
    print()
    print(c("  Type  help  for commands,  demo  for a guided walkthrough,", DIM))
    print(c("  or start adding beliefs with:  add <formula>", DIM))
    print()

    bb = BeliefBase()

    while True:
        n = len(bb.beliefs)
        consistent_marker = c("✓", GREEN) if (n == 0 or bb.is_consistent()) else c("✗", RED)
        beliefs_str = (
            c(f"[{', '.join(str(f) for f in bb.beliefs)}]", YELLOW)
            if bb.beliefs else c("∅", DIM)
        )
        prompt = f"\n{c('B', BOLD)}={beliefs_str} {consistent_marker}  {c('>', CYAN, BOLD)} "

        try:
            raw = input(prompt).strip()
        except (EOFError, KeyboardInterrupt):
            print()
            ok("Goodbye!")
            break

        if not raw:
            continue

        parts = raw.split(None, 1)
        cmd   = parts[0].lower()
        args  = parts[1].strip() if len(parts) > 1 else ""

        if cmd in ("quit", "exit", "q"):
            ok("Goodbye!")
            break

        elif cmd == "help":
            show_help()

        elif cmd == "syntax":
            show_syntax()

        elif cmd == "show":
            show_belief_base(bb)

        elif cmd == "clear":
            bb = BeliefBase()
            ok("Belief base cleared.")

        elif cmd == "consistent":
            cmd_consistent(bb)

        elif cmd == "add":
            if not args:
                err("Usage:  add <formula> [priority]")
                explain("Example:  add (R => W)    or    add R 0")
            else:
                bb = cmd_add(bb, args)

        elif cmd == "remove":
            if not args:
                err("Usage:  remove <formula>")
            else:
                bb = cmd_remove(bb, args)

        elif cmd == "contract":
            if not args:
                err("Usage:  contract <formula>")
                explain("Example:  contract R")
            else:
                bb = cmd_contract(bb, args)

        elif cmd == "revise":
            if not args:
                err("Usage:  revise <formula>")
                explain("Example:  revise ~R")
            else:
                bb = cmd_revise(bb, args)

        elif cmd == "entails":
            if not args:
                err("Usage:  entails <formula>")
                explain("Example:  entails (R & W)")
            else:
                cmd_entails(bb, args)

        elif cmd == "cnf":
            if not args:
                err("Usage:  cnf <formula>")
                explain("Example:  cnf (R => W)")
            else:
                cmd_cnf(args)

        elif cmd == "demo":
            bb = run_demo(bb)

        elif cmd == "tests":
            run_tests()

        else:
            err(f"Unknown command: '{cmd}'")
            explain("Type  help  to see available commands.")


if __name__ == "__main__":
    main()
