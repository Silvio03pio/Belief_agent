"""
AGM Revision Postulate Test Suite
===================================

Tests the five AGM belief-revision postulates:
  R1  Success       B*phi |= phi
  R2  Inclusion     B*phi ⊆ Cn(B + phi)
  R3  Vacuity       if B ⊭ ~phi  then  B*phi ≡ B + phi
  R4  Consistency   B*phi is consistent  (unless phi is a contradiction)
  R5  Extensionality  phi ≡ psi  =>  B*phi ≡ B*psi

Coverage is organised in five sections:

  A. Hand-crafted examples   — five curated scenarios, fully printed
  B. Oracle cross-validation — resolution engine vs truth-table oracle (~15 cases)
  C. Systematic tests        — 22 curated (BB, phi) pairs × 4 postulates (silent unless FAIL)
  D. Edge-case tests         — 15 explicit boundary conditions (silent unless FAIL)
  E. Randomized tests        — fixed-seed random generation, 50 trials (silent unless FAIL)
  Ext. Extensionality tests  — 10 equivalent-pair cases

IMPORTANT CAVEAT
  A passing run increases confidence in the implementation.
  It does NOT formally prove correctness for all possible inputs.
"""

import random

from formula import Formula, Not, parse
from belief_base import BeliefBase
from resolution import pl_resolution, is_consistent
from oracle import oracle_entails

PASS = "PASS"
FAIL = "FAIL"
RANDOM_SEED = 42


# ---------------------------------------------------------------------------
# Result tracker
# ---------------------------------------------------------------------------

class _SectionResults:
    """Lightweight per-section pass/fail counter."""

    def __init__(self, name: str):
        self.name = name
        self.passed = 0
        self.failed = 0
        self.counterexamples: list = []

    def record(self, result: str, context: str = None):
        if result == PASS:
            self.passed += 1
        else:
            self.failed += 1
            if context:
                self.counterexamples.append(context)

    def total(self) -> int:
        return self.passed + self.failed

    def summary_line(self) -> str:
        mark = "✓" if self.failed == 0 else "✗"
        return f"  {mark}  {self.name:<35}  {self.passed}/{self.total()} passed"


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

def _logically_equivalent(f1: Formula, f2: Formula) -> bool:
    return pl_resolution([f1], f2) and pl_resolution([f2], f1)


def _bb_entails_all_of(bb1: BeliefBase, bb2: BeliefBase) -> bool:
    for f in bb2:
        if not pl_resolution(list(bb1), f):
            return False
    return True


def _bb_semantically_equal(bb1: BeliefBase, bb2: BeliefBase) -> bool:
    return _bb_entails_all_of(bb1, bb2) and _bb_entails_all_of(bb2, bb1)


def _is_formula_in_bb(phi: Formula, bb: BeliefBase) -> bool:
    return pl_resolution(list(bb), phi)


def _is_tautology(phi: Formula) -> bool:
    return pl_resolution([], phi)


def _is_contradiction(phi: Formula) -> bool:
    return not is_consistent([phi])


def _print_result(postulate: str, result: str, label: str, msg: str):
    prefix = f"[{label}] " if label else ""
    status = "✓ PASS" if result == PASS else "✗ FAIL"
    print(f"  {status}  {postulate}  {prefix}")
    print(f"         {msg}")


# ---------------------------------------------------------------------------
# AGM postulate test functions
# ---------------------------------------------------------------------------

def test_success(bb: BeliefBase, phi: Formula,
                 label: str = "", _silent: bool = False) -> str:
    """(R1) Success: phi must be entailed by B * phi."""
    revised = bb.revise(phi)
    if _is_formula_in_bb(phi, revised):
        result = PASS
        msg = f"phi={phi} is entailed by B*phi."
    else:
        result = FAIL
        msg = f"phi={phi} is NOT entailed by B*phi={list(revised)}."
    if not _silent or result == FAIL:
        _print_result("R1 Success", result, label, msg)
    return result


def test_inclusion(bb: BeliefBase, phi: Formula,
                   label: str = "", _silent: bool = False) -> str:
    """(R2) Inclusion: B * phi is a subset of Cn(B + phi)."""
    revised  = bb.revise(phi)
    expanded = bb.expand(phi)
    failed_formula = None
    for f in revised:
        if not pl_resolution(list(expanded), f):
            failed_formula = f
            break
    if failed_formula is None:
        result = PASS
        msg = "All beliefs in B*phi are entailed by B+phi."
    else:
        result = FAIL
        msg = f"Formula {failed_formula} in B*phi is NOT entailed by B+phi."
    if not _silent or result == FAIL:
        _print_result("R2 Inclusion", result, label, msg)
    return result


def test_vacuity(bb: BeliefBase, phi: Formula,
                 label: str = "", _silent: bool = False) -> str:
    """(R3) Vacuity: if B does not entail ~phi, then B * phi = B + phi."""
    neg_phi = Not(phi)
    if _is_formula_in_bb(neg_phi, bb):
        result = PASS
        msg = "Vacuity not applicable (~phi IS entailed by B)."
        if not _silent:
            _print_result("R3 Vacuity", result, label, msg)
        return result

    revised  = bb.revise(phi)
    expanded = bb.expand(phi)
    if _bb_semantically_equal(revised, expanded):
        result = PASS
        msg = "~phi not in Cn(B) and B*phi equals B+phi."
    else:
        result = FAIL
        msg = (f"~phi not in Cn(B) but B*phi != B+phi.\n"
               f"    B*phi   = {list(revised)}\n"
               f"    B+phi   = {list(expanded)}")
    if not _silent or result == FAIL:
        _print_result("R3 Vacuity", result, label, msg)
    return result


def test_consistency(bb: BeliefBase, phi: Formula,
                     label: str = "", _silent: bool = False) -> str:
    """(R4) Consistency: B * phi should be consistent (unless phi is a contradiction)."""
    if _is_contradiction(phi):
        result = PASS
        msg = "phi is a contradiction — consistency postulate does not apply."
        if not _silent:
            _print_result("R4 Consistency", result, label, msg)
        return result

    revised = bb.revise(phi)
    if revised.is_consistent():
        result = PASS
        msg = "B*phi is consistent."
    else:
        result = FAIL
        msg = f"B*phi is INCONSISTENT.  B*phi = {list(revised)}"
    if not _silent or result == FAIL:
        _print_result("R4 Consistency", result, label, msg)
    return result


def test_extensionality(bb: BeliefBase, phi: Formula, psi: Formula,
                        label: str = "", _silent: bool = False) -> str:
    """(R5) Extensionality: if phi ≡ psi then B * phi ≡ B * psi."""
    if not _logically_equivalent(phi, psi):
        result = PASS
        msg = f"phi={phi} and psi={psi} are not equivalent — test not applicable."
        if not _silent:
            _print_result("R5 Extensionality", result, label, msg)
        return result

    revised_phi = bb.revise(phi)
    revised_psi = bb.revise(psi)
    if _bb_semantically_equal(revised_phi, revised_psi):
        result = PASS
        msg = "phi ≡ psi and B*phi ≡ B*psi."
    else:
        result = FAIL
        msg = (f"phi ≡ psi but B*phi != B*psi.\n"
               f"    B*phi = {list(revised_phi)}\n"
               f"    B*psi = {list(revised_psi)}")
    if not _silent or result == FAIL:
        _print_result("R5 Extensionality", result, label, msg)
    return result


# ---------------------------------------------------------------------------
# Section A — Hand-crafted examples (existing curated scenarios)
# ---------------------------------------------------------------------------

def _run_section_a() -> _SectionResults:
    sec = _SectionResults("A. Hand-crafted examples")
    print("\n" + "=" * 70)
    print("  SECTION A — Hand-crafted Examples")
    print("=" * 70)

    p       = parse("p")
    q       = parse("q")
    neg_q   = parse("~q")
    p_imp_q = parse("(p => q)")

    # --- Example 1 ---
    print("\n--- Ex1: B = {p, q}, revise with ~q ---")
    bb1 = BeliefBase([p, q])
    print(f"  B = {list(bb1)}  →  B*~q = {list(bb1.revise(neg_q))}")
    psi_ex1 = parse("(~q & (p | ~p))")
    for r in [
        test_success(bb1, neg_q, "Ex1"),
        test_inclusion(bb1, neg_q, "Ex1"),
        test_vacuity(bb1, neg_q, "Ex1"),
        test_consistency(bb1, neg_q, "Ex1"),
        test_extensionality(bb1, neg_q, psi_ex1, "Ex1"),
    ]:
        sec.record(r)

    # --- Example 2 ---
    print("\n--- Ex2: B = {p, q, (p=>q)}, revise with ~q ---")
    bb2 = BeliefBase([p, q, p_imp_q])
    print(f"  B = {list(bb2)}  →  B*~q = {list(bb2.revise(neg_q))}")
    for r in [
        test_success(bb2, neg_q, "Ex2"),
        test_inclusion(bb2, neg_q, "Ex2"),
        test_vacuity(bb2, neg_q, "Ex2"),
        test_consistency(bb2, neg_q, "Ex2"),
        test_extensionality(bb2, neg_q, psi_ex1, "Ex2"),
    ]:
        sec.record(r)

    # --- Example 3: vacuity case ---
    print("\n--- Ex3: B = {p}, revise with q  (vacuity case) ---")
    bb3 = BeliefBase([p])
    for r in [
        test_success(bb3, q, "Ex3"),
        test_inclusion(bb3, q, "Ex3"),
        test_vacuity(bb3, q, "Ex3"),
        test_consistency(bb3, q, "Ex3"),
        test_extensionality(bb3, q, parse("(q & (p | ~p))"), "Ex3"),
    ]:
        sec.record(r)

    # --- Example 4: revise with contradiction ---
    print("\n--- Ex4: B = {p}, revise with (q & ~q)  [contradiction] ---")
    bb4     = BeliefBase([p])
    contra  = parse("(q & ~q)")
    for r in [
        test_success(bb4, contra, "Ex4"),
        test_consistency(bb4, contra, "Ex4"),
    ]:
        sec.record(r)

    # --- Example 5 ---
    print("\n--- Ex5: B = {p, (p=>q), r}, revise with ~q ---")
    r_atom = parse("r")
    bb5    = BeliefBase([p, p_imp_q, r_atom])
    print(f"  B = {list(bb5)}  →  B*~q = {list(bb5.revise(neg_q))}")
    for r in [
        test_success(bb5, neg_q, "Ex5"),
        test_inclusion(bb5, neg_q, "Ex5"),
        test_vacuity(bb5, neg_q, "Ex5"),
        test_consistency(bb5, neg_q, "Ex5"),
        test_extensionality(bb5, neg_q, psi_ex1, "Ex5"),
    ]:
        sec.record(r)

    return sec


# ---------------------------------------------------------------------------
# Section B — Oracle cross-validation
# ---------------------------------------------------------------------------

# Each entry: (label, kb_formula_strings, query_string, expected_result)
_ORACLE_CASES = [
    ("B01", ["p"],                       "p",           True),
    ("B02", ["p", "q"],                  "(p & q)",     True),
    ("B03", ["p", "(p => q)"],           "q",           True),   # modus ponens
    ("B04", ["(p => q)", "(q => r)", "p"], "r",         True),   # hyp. syllogism
    ("B05", ["(p | q)", "~p"],           "q",           True),   # disj. syllogism
    ("B06", ["(p <=> q)", "p"],          "q",           True),   # bicond. MP
    ("B07", ["(p <=> q)", "~p"],         "~q",          True),   # bicond. MT
    ("B08", ["p", "~p"],                 "q",           True),   # explosion
    ("B09", [],                          "(p | ~p)",    True),   # tautology
    ("B10", [],                          "p",           False),  # not tautology
    ("B11", ["(p => q)"],                "p",           False),  # affirming consequent
    ("B12", ["p"],                       "q",           False),  # unrelated
    ("B13", ["(p | q)"],                 "p",           False),  # weaker premise
    ("B14", ["~(p & q)"],               "~p",           False),  # not sufficient
    ("B15", ["(p & q)"],                 "(p | r)",     True),   # weakening
]


def _run_section_b() -> _SectionResults:
    sec = _SectionResults("B. Oracle cross-validation")
    print("\n" + "=" * 70)
    print("  SECTION B — Oracle Cross-Validation")
    print("  Checking resolution engine agrees with truth-table oracle.")
    print("=" * 70)
    print()

    for label, kb_strs, query_str, expected in _ORACLE_CASES:
        kb    = [parse(s) for s in kb_strs]
        query = parse(query_str)

        res_result    = pl_resolution(kb, query)
        oracle_result = oracle_entails(kb, query)

        # Both should agree with each other and with the expected value
        res_ok    = (res_result    == expected)
        oracle_ok = (oracle_result == expected)
        agree     = (res_result    == oracle_result)

        if res_ok and oracle_ok:
            result = PASS
            print(f"  ✓ PASS  {label}  KB={kb_strs!r} |= {query_str!r}  →  {expected}")
        else:
            result = FAIL
            print(f"  ✗ FAIL  {label}  KB={kb_strs!r} |= {query_str!r}")
            if not agree:
                print(f"         DISCREPANCY: resolution={res_result}, "
                      f"oracle={oracle_result}, expected={expected}")
            elif not res_ok:
                print(f"         resolution gave {res_result}, expected {expected}")
            else:
                print(f"         oracle gave {oracle_result}, expected {expected}")

        ctx = (f"{label}: KB={kb_strs}, query={query_str}, "
               f"resolution={res_result}, oracle={oracle_result}, expected={expected}")
        sec.record(result, ctx if result == FAIL else None)

    return sec


# ---------------------------------------------------------------------------
# Section C — Systematic postulate tests
# ---------------------------------------------------------------------------

# Each entry: (label, bb_formula_strings, phi_string)
_SYSTEMATIC_CASES = [
    # Vacuous cases — B does not entail ~phi
    ("Sys01", [],                           "p"),
    ("Sys02", ["p"],                        "q"),
    ("Sys03", ["p"],                        "(p | q)"),
    ("Sys04", ["(p => q)"],                 "p"),
    ("Sys05", ["(p => q)"],                 "r"),
    ("Sys06", ["(p | q)"],                  "(p | r)"),

    # Direct conflict
    ("Sys07", ["p"],                        "~p"),
    ("Sys08", ["p", "q"],                   "~p"),
    ("Sys09", ["p", "q"],                   "~q"),
    ("Sys10", ["(p & q)"],                  "~p"),

    # Indirect / chained conflict
    ("Sys11", ["p", "(p => q)"],            "~q"),
    ("Sys12", ["p", "(p => q)", "r"],       "~q"),
    ("Sys13", ["(p => q)", "(q => r)", "p"], "~r"),
    ("Sys14", ["(p | q)", "~p"],            "~q"),

    # Tautology and contradiction as revision formula
    ("Sys15", ["p"],                        "(q | ~q)"),
    ("Sys16", ["p"],                        "(q & ~q)"),
    ("Sys17", [],                           "(q & ~q)"),

    # Compound base
    ("Sys18", ["(p <=> q)", "q"],           "~p"),
    ("Sys19", ["p", "q", "r"],             "~r"),
    ("Sys20", ["(p => q)", "(q => r)"],    "~q"),
    ("Sys21", ["~p", "~q"],               "p"),
    ("Sys22", ["~p", "(p | q)"],           "~q"),
]


def _run_section_c() -> _SectionResults:
    sec = _SectionResults("C. Systematic postulate tests")
    print("\n" + "=" * 70)
    print("  SECTION C — Systematic Postulate Tests")
    print(f"  {len(_SYSTEMATIC_CASES)} curated cases × 4 postulates "
          f"= {len(_SYSTEMATIC_CASES) * 4} assertions  (silent unless FAIL)")
    print("=" * 70)

    for label, bb_strs, phi_str in _SYSTEMATIC_CASES:
        bb  = BeliefBase([parse(s) for s in bb_strs])
        phi = parse(phi_str)
        ctx = f"BB={bb_strs}, phi={phi_str!r}"
        for test_fn in (test_success, test_inclusion, test_vacuity, test_consistency):
            r = test_fn(bb, phi, label, _silent=True)
            sec.record(r, ctx if r == FAIL else None)

    if sec.counterexamples:
        print()
        for cx in sec.counterexamples:
            print(f"  ✗ COUNTEREXAMPLE: {cx}")
    else:
        print(f"\n  All {sec.total()} assertions passed.")

    return sec


# ---------------------------------------------------------------------------
# Section D — Edge cases
# ---------------------------------------------------------------------------

# Each entry: (label, description, bb_formula_strings, phi_string)
_EDGE_CASES = [
    ("Edge01", "empty base, atom",                  [],            "p"),
    ("Edge02", "empty base, compound",              [],            "(p & q)"),
    ("Edge03", "empty base, tautology",             [],            "(p | ~p)"),
    ("Edge04", "empty base, contradiction",         [],            "(p & ~p)"),
    ("Edge05", "single belief, revise by same",     ["p"],         "p"),
    ("Edge06", "single belief, revise by negation", ["p"],         "~p"),
    ("Edge07", "single belief, tautology phi",      ["p"],         "(q | ~q)"),
    ("Edge08", "single belief, contradiction phi",  ["p"],         "(q & ~q)"),
    ("Edge09", "revise with already-entailed phi",  ["p", "q"],    "(p | q)"),
    ("Edge10", "triple negation ~~~p ≡ ~p",         ["p"],         "~~~p"),
    ("Edge11", "double negation ~~p ≡ p",           ["~p"],        "~~p"),
    ("Edge12", "implication, vacuous ~p case",      ["(p => q)"],  "~p"),
    ("Edge13", "inconsistent base, revise",         ["p", "~p"],   "q"),
    ("Edge14", "mixed connectives chain",
                ["((p => q) & (q => r))"],                         "~r"),
    ("Edge15", "biconditional then negate one side",
                ["(p <=> q)", "~q"],                               "p"),
]


def _run_section_d() -> _SectionResults:
    sec = _SectionResults("D. Edge-case tests")
    print("\n" + "=" * 70)
    print("  SECTION D — Edge-Case Tests")
    print(f"  {len(_EDGE_CASES)} cases × 4 postulates = {len(_EDGE_CASES) * 4} assertions"
          "  (silent unless FAIL)")
    print("=" * 70)

    for label, desc, bb_strs, phi_str in _EDGE_CASES:
        bb  = BeliefBase([parse(s) for s in bb_strs])
        phi = parse(phi_str)
        ctx = f"{label} ({desc}): BB={bb_strs}, phi={phi_str!r}"
        for test_fn in (test_success, test_inclusion, test_vacuity, test_consistency):
            r = test_fn(bb, phi, label, _silent=True)
            sec.record(r, ctx if r == FAIL else None)

    if sec.counterexamples:
        print()
        for cx in sec.counterexamples:
            print(f"  ✗ COUNTEREXAMPLE: {cx}")
    else:
        print(f"\n  All {sec.total()} assertions passed.")

    return sec


# ---------------------------------------------------------------------------
# Section Ext — Extensionality tests with explicitly equivalent formula pairs
# ---------------------------------------------------------------------------

# Each entry: (label, bb_formula_strings, phi_string, psi_string)
# phi and psi must be logically equivalent (verified by the test function itself)
_EXT_CASES = [
    ("Ext01", [],         "(p => q)",            "(~p | q)"),
    ("Ext02", ["r"],      "(p => q)",            "(~p | q)"),
    ("Ext03", ["p"],      "(p => q)",            "(~p | q)"),
    ("Ext04", [],         "~~p",                 "p"),
    ("Ext05", ["q"],      "~~p",                 "p"),
    ("Ext06", [],         "(p & q)",             "(q & p)"),
    ("Ext07", ["r"],      "(p & q)",             "(q & p)"),
    ("Ext08", [],         "~(p & q)",            "(~p | ~q)"),
    ("Ext09", ["p"],      "~(p & q)",            "(~p | ~q)"),
    ("Ext10", [],         "(p <=> q)",           "((p => q) & (q => p))"),
]


def _run_section_ext() -> _SectionResults:
    sec = _SectionResults("Ext. Extensionality tests")
    print("\n" + "=" * 70)
    print("  SECTION Ext — Extensionality Tests  (R5)")
    print(f"  {len(_EXT_CASES)} equivalent-pair cases  (silent unless FAIL)")
    print("=" * 70)

    for label, bb_strs, phi_str, psi_str in _EXT_CASES:
        bb  = BeliefBase([parse(s) for s in bb_strs])
        phi = parse(phi_str)
        psi = parse(psi_str)
        ctx = f"{label}: BB={bb_strs}, phi={phi_str!r}, psi={psi_str!r}"
        r   = test_extensionality(bb, phi, psi, label, _silent=True)
        sec.record(r, ctx if r == FAIL else None)

    if sec.counterexamples:
        print()
        for cx in sec.counterexamples:
            print(f"  ✗ COUNTEREXAMPLE: {cx}")
    else:
        print(f"\n  All {sec.total()} assertions passed.")

    return sec


# ---------------------------------------------------------------------------
# Section E — Randomized tests
# ---------------------------------------------------------------------------

def _make_formula_pool() -> list:
    """A fixed pool of small formulas over {p, q, r} for random generation."""
    return [parse(s) for s in [
        "p", "q", "r",
        "~p", "~q", "~r",
        "(p & q)", "(p | q)", "(p => q)", "(p <=> q)",
        "(q & r)", "(q | r)", "(q => r)",
        "(p & r)", "(p | r)", "(p => r)",
        "~(p & q)", "(~p | ~q)",
        "((p => q) & (q => r))",
        "(p | (q & r))",
        "((p & q) => r)",
    ]]


def _run_section_e(n_trials: int = 50) -> _SectionResults:
    sec = _SectionResults(f"E. Randomized tests (seed={RANDOM_SEED})")
    print("\n" + "=" * 70)
    print(f"  SECTION E — Randomized Tests  (seed={RANDOM_SEED})")
    print(f"  {n_trials} random trials × 4 postulates = {n_trials * 4} assertions"
          "  (silent unless FAIL)")
    print("=" * 70)

    rng  = random.Random(RANDOM_SEED)
    pool = _make_formula_pool()

    for trial in range(n_trials):
        bb_size = rng.randint(0, 3)
        # sample without replacement so no exact syntactic duplicates in one trial
        bb_formulas = rng.sample(pool, bb_size)
        phi         = rng.choice(pool)

        bb  = BeliefBase(list(bb_formulas))
        ctx = f"Trial {trial+1}: BB={[str(f) for f in bb_formulas]}, phi={phi}"

        for test_fn in (test_success, test_inclusion, test_vacuity, test_consistency):
            r = test_fn(bb, phi, f"E{trial+1:02d}", _silent=True)
            sec.record(r, ctx if r == FAIL else None)

    if sec.counterexamples:
        print()
        # Deduplicate context lines (multiple postulates may fail for same trial)
        seen = set()
        for cx in sec.counterexamples:
            base = cx.split(",")[0]  # "Trial N: ..."
            if base not in seen:
                seen.add(base)
                print(f"  ✗ COUNTEREXAMPLE: {cx}")
    else:
        print(f"\n  All {sec.total()} assertions passed.")

    return sec


# ---------------------------------------------------------------------------
# Top-level runner
# ---------------------------------------------------------------------------

def run_all_tests():
    """Run the complete AGM postulate test suite and print a summary."""
    print()
    print("=" * 70)
    print("  AGM REVISION POSTULATE TEST SUITE")
    print("=" * 70)

    sections = [
        _run_section_a(),
        _run_section_b(),
        _run_section_c(),
        _run_section_d(),
        _run_section_ext(),
        _run_section_e(),
    ]

    total_pass = sum(s.passed for s in sections)
    total_fail = sum(s.failed for s in sections)
    total_all  = total_pass + total_fail

    print()
    print("=" * 70)
    print("  SUMMARY")
    print("=" * 70)
    for s in sections:
        print(s.summary_line())
    print("  " + "─" * 50)
    overall_mark = "✓" if total_fail == 0 else "✗"
    print(f"  {overall_mark}  {'TOTAL':<35}  {total_pass}/{total_all} passed")
    if total_fail > 0:
        print()
        print("  FAILURES DETECTED — see COUNTEREXAMPLE lines above.")
        for s in sections:
            for cx in s.counterexamples:
                print(f"    • {cx}")
    print()
    print("  NOTE: A passing run provides empirical validation, not a formal proof.")
    print(f"        Random tests used seed={RANDOM_SEED} — results are reproducible.")
    print("=" * 70)
    print()


if __name__ == "__main__":
    import sys as _sys
    if _sys.platform == "win32":
        import io as _io
        _sys.stdout = _io.TextIOWrapper(_sys.stdout.buffer, encoding="utf-8", errors="replace")
    run_all_tests()
