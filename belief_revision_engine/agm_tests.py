"""
agm_tests.py  –  AGM postulate test suite for the revision operator B * φ.

Tests the five AGM revision postulates for the revision operator as presented in
DTU 02180 slides9 and the Gärdenfors (1988) AGM framework:

  (R1) Success      φ ∈ B * φ
  (R2) Inclusion    B * φ ⊆ B + φ
  (R3) Vacuity      If ¬φ ∉ Cn(B), then B * φ = B + φ
  (R4) Consistency  B * φ is consistent  (unless φ is a contradiction)
  (R5) Extensionality  If φ ≡ ψ then B * φ = B * ψ

Each test is run on concrete example belief bases derived from the course material
(the "Bob" examples from slides9) and prints PASS / FAIL with an explanation.

Note on postulate R2 (Inclusion):
  The postulate states  B * φ ⊆ B + φ  at the level of *logical consequences*:
  every formula entailed by B * φ is also entailed by B + φ.
  In our finite syntactic representation we check this as:
  every formula in B * φ is either in B or equals φ (i.e. it came from B or was
  the expansion formula).

Note on postulate R3 (Vacuity):
  B * φ = B + φ  means they entail exactly the same formulas.  In our syntactic
  implementation we check that the two belief bases entail each other (mutual
  entailment of each member).

Note on postulate R5 (Extensionality):
  φ ≡ ψ  is checked using the resolution-based entailment checker:
  φ ≡ ψ  iff  φ ⊨ ψ  and  ψ ⊨ φ.
  B * φ = B * ψ  is checked as mutual entailment.
"""

from formula import Formula, Not, parse
from belief_base import BeliefBase
from resolution import pl_resolution, is_consistent


PASS = "PASS"
FAIL = "FAIL"


# ---------------------------------------------------------------------------
# Helper utilities
# ---------------------------------------------------------------------------

def _logically_equivalent(f1: Formula, f2: Formula) -> bool:
    """Check φ ≡ ψ using resolution: both φ ⊨ ψ and ψ ⊨ φ."""
    return pl_resolution([f1], f2) and pl_resolution([f2], f1)


def _bb_entails_all_of(bb1: BeliefBase, bb2: BeliefBase) -> bool:
    """Return True if every formula in bb2 is entailed by bb1."""
    for f in bb2:
        if not pl_resolution(list(bb1), f):
            return False
    return True


def _bb_semantically_equal(bb1: BeliefBase, bb2: BeliefBase) -> bool:
    """Return True if bb1 and bb2 are semantically equivalent belief bases."""
    return _bb_entails_all_of(bb1, bb2) and _bb_entails_all_of(bb2, bb1)


def _is_formula_in_bb(phi: Formula, bb: BeliefBase) -> bool:
    """Return True if φ is entailed by the belief base bb."""
    return pl_resolution(list(bb), phi)


def _is_tautology(phi: Formula) -> bool:
    """Return True if phi is a tautology (entailed by empty KB)."""
    return pl_resolution([], phi)


def _is_contradiction(phi: Formula) -> bool:
    """Return True if phi is a contradiction (unsatisfiable)."""
    return not is_consistent([phi])


# ---------------------------------------------------------------------------
# Postulate testers
# ---------------------------------------------------------------------------

def test_success(bb: BeliefBase, phi: Formula, label: str = "") -> str:
    """(R1) Success: φ ∈ B * φ  (the new information is in the revised base).

    After revision, φ must be entailed by B * φ.
    """
    revised = bb.revise(phi)
    if _is_formula_in_bb(phi, revised):
        result = PASS
        msg = f"φ={phi} is entailed by B*φ."
    else:
        result = FAIL
        msg = f"φ={phi} is NOT entailed by B*φ={revised}."
    _print_result("R1 Success", result, label, msg)
    return result


def test_inclusion(bb: BeliefBase, phi: Formula, label: str = "") -> str:
    """(R2) Inclusion: B * φ ⊆ B + φ.

    Every formula entailed by B * φ is also entailed by B + φ.
    We check syntactically: every formula in B * φ is entailed by B + φ.
    """
    revised  = bb.revise(phi)
    expanded = bb.expand(phi)
    # Check every belief in revised is also in expanded (semantically)
    failed_formula = None
    for f in revised:
        if not pl_resolution(list(expanded), f):
            failed_formula = f
            break
    if failed_formula is None:
        result = PASS
        msg = "All beliefs in B*φ are entailed by B+φ."
    else:
        result = FAIL
        msg = f"Formula {failed_formula} in B*φ is NOT entailed by B+φ."
    _print_result("R2 Inclusion", result, label, msg)
    return result


def test_vacuity(bb: BeliefBase, phi: Formula, label: str = "") -> str:
    """(R3) Vacuity: If ¬φ ∉ Cn(B), then B * φ = B + φ.

    If the current belief base does not entail ¬φ, then revision by φ
    should coincide with simple expansion by φ.
    """
    neg_phi = Not(phi)
    if _is_formula_in_bb(neg_phi, bb):
        # Condition not applicable – skip the test
        result = PASS
        msg = f"Vacuity not applicable (¬φ IS entailed by B); condition vacuously met."
        _print_result("R3 Vacuity", result, label, msg)
        return result

    revised  = bb.revise(phi)
    expanded = bb.expand(phi)
    if _bb_semantically_equal(revised, expanded):
        result = PASS
        msg = "¬φ ∉ Cn(B) and B*φ ≡ B+φ (as required)."
    else:
        result = FAIL
        msg = f"¬φ ∉ Cn(B) but B*φ ≠ B+φ.\n    B*φ = {revised}\n    B+φ = {expanded}"
    _print_result("R3 Vacuity", result, label, msg)
    return result


def test_consistency(bb: BeliefBase, phi: Formula, label: str = "") -> str:
    """(R4) Consistency: B * φ is consistent (unless φ is a contradiction).

    The revised belief base should be consistent, provided φ itself is consistent.
    """
    if _is_contradiction(phi):
        result = PASS
        msg = "φ is a contradiction; consistency not required by AGM."
        _print_result("R4 Consistency", result, label, msg)
        return result

    revised = bb.revise(phi)
    if revised.is_consistent():
        result = PASS
        msg = "B*φ is consistent."
    else:
        result = FAIL
        msg = f"B*φ is INCONSISTENT. B*φ = {revised}"
    _print_result("R4 Consistency", result, label, msg)
    return result


def test_extensionality(bb: BeliefBase, phi: Formula, psi: Formula,
                        label: str = "") -> str:
    """(R5) Extensionality: If φ ≡ ψ then B * φ = B * ψ.

    If two formulas are logically equivalent, revision by either should
    yield semantically equivalent belief bases.
    """
    if not _logically_equivalent(phi, psi):
        # Cannot test: φ and ψ are not equivalent
        result = PASS
        msg = f"φ={phi} and ψ={psi} are not logically equivalent; test not applicable."
        _print_result("R5 Extensionality", result, label, msg)
        return result

    revised_phi = bb.revise(phi)
    revised_psi = bb.revise(psi)
    if _bb_semantically_equal(revised_phi, revised_psi):
        result = PASS
        msg = f"φ≡ψ and B*φ ≡ B*ψ."
    else:
        result = FAIL
        msg = (f"φ≡ψ but B*φ ≠ B*ψ.\n"
               f"    B*φ = {revised_phi}\n"
               f"    B*ψ = {revised_psi}")
    _print_result("R5 Extensionality", result, label, msg)
    return result


# ---------------------------------------------------------------------------
# Print helper
# ---------------------------------------------------------------------------

def _print_result(postulate: str, result: str, label: str, msg: str):
    prefix = f"[{label}] " if label else ""
    status = "✓ PASS" if result == PASS else "✗ FAIL"
    print(f"  {status}  {postulate}  {prefix}")
    print(f"         {msg}")


# ---------------------------------------------------------------------------
# Full test suite
# ---------------------------------------------------------------------------

def run_all_tests():
    """Run the complete AGM postulate test suite on several example belief bases."""

    print("=" * 70)
    print("  AGM REVISION POSTULATE TEST SUITE")
    print("  (Using examples from DTU 02180 slides9 and AIMA Chapter 7)")
    print("=" * 70)

    results = []

    # ------------------------------------------------------------------
    # Example 1 – Bob's basic belief revision (slides9)
    # B = {p, q},  revise with ¬q
    # ------------------------------------------------------------------
    print("\n--- Example 1: Bob believes {p, q}, revises with ~q ---")
    p   = parse("p")
    q   = parse("q")
    neg_q = parse("~q")

    bb1 = BeliefBase([p, q])
    print(f"  Belief base B = {bb1}")
    print(f"  Revising with φ = {neg_q}")
    revised1 = bb1.revise(neg_q)
    print(f"  B * ~q = {revised1}")

    results.append(test_success(bb1, neg_q, "Ex1"))
    results.append(test_inclusion(bb1, neg_q, "Ex1"))
    results.append(test_vacuity(bb1, neg_q, "Ex1"))
    results.append(test_consistency(bb1, neg_q, "Ex1"))

    # For extensionality: ~q ≡ ~q (trivially), or use ~~(~q) ≡ ~q
    neg_neg_neg_q = parse("~~q")  # note: this is equivalent to q, not ~q
    # Better: use ~q ≡ ~q (a formula logically equivalent to ~q)
    # We construct ~~(~q) which should equal ~q
    # Actually let's use a direct example: "(p | ~p)" is a tautology
    # For extensionality test, use phi ≡ psi where psi = "(~q | ~~q)" wait...
    # Let's use two equivalent formulas: ~q and ~(~~q) ... hmm, tricky to build
    # Use: phi = ~q,  psi = "(~q | ~~q)" => no, that's a tautology
    # Simplest: phi = ~q, psi = "(~q & (p | ~p))" ≡ ~q
    psi_ex1 = parse("(~q & (p | ~p))")   # logically equivalent to ~q
    results.append(test_extensionality(bb1, neg_q, psi_ex1, "Ex1"))

    # ------------------------------------------------------------------
    # Example 2 – Bob with implication (slides9)
    # B = {p, q, p→q},  revise with ¬q
    # ------------------------------------------------------------------
    print("\n--- Example 2: Bob believes {p, q, (p=>q)}, revises with ~q ---")
    p_imp_q = parse("(p => q)")
    bb2 = BeliefBase([p, q, p_imp_q])
    print(f"  Belief base B = {bb2}")
    print(f"  Revising with φ = {neg_q}")
    revised2 = bb2.revise(neg_q)
    print(f"  B * ~q = {revised2}")

    results.append(test_success(bb2, neg_q, "Ex2"))
    results.append(test_inclusion(bb2, neg_q, "Ex2"))
    results.append(test_vacuity(bb2, neg_q, "Ex2"))
    results.append(test_consistency(bb2, neg_q, "Ex2"))
    # Extensionality: ~q ≡ ~(~~q) in terms of semantic equivalence
    results.append(test_extensionality(bb2, neg_q, psi_ex1, "Ex2"))

    # ------------------------------------------------------------------
    # Example 3 – Vacuity applies (B does not entail ¬φ)
    # B = {p},  revise with q  (B does not entail ~q, so B*q = B+q)
    # ------------------------------------------------------------------
    print("\n--- Example 3: B = {p}, revising with q (vacuity case) ---")
    bb3 = BeliefBase([p])
    print(f"  Belief base B = {bb3}")
    print(f"  Revising with φ = {q}")
    results.append(test_success(bb3, q, "Ex3"))
    results.append(test_inclusion(bb3, q, "Ex3"))
    results.append(test_vacuity(bb3, q, "Ex3"))     # Should apply: B ⊭ ~q
    results.append(test_consistency(bb3, q, "Ex3"))
    results.append(test_extensionality(bb3, q,
                                       parse("(q & (p | ~p))"), "Ex3"))

    # ------------------------------------------------------------------
    # Example 4 – Contradiction input (consistency postulate edge case)
    # B = {p},  revise with (q & ~q)  – contradiction
    # ------------------------------------------------------------------
    print("\n--- Example 4: Revising with a contradiction (q & ~q) ---")
    bb4 = BeliefBase([p])
    phi_contra = parse("(q & ~q)")
    print(f"  Belief base B = {bb4}")
    print(f"  Revising with φ = {phi_contra}  [contradiction]")
    results.append(test_success(bb4, phi_contra, "Ex4"))
    results.append(test_consistency(bb4, phi_contra, "Ex4"))  # should note exception

    # ------------------------------------------------------------------
    # Example 5 – Three-formula belief base with priority
    # B = {p, (p=>q), r},  revise with ~q
    # ------------------------------------------------------------------
    print("\n--- Example 5: B = {p, (p=>q), r}, revising with ~q ---")
    r = parse("r")
    bb5 = BeliefBase([p, p_imp_q, r])
    print(f"  Belief base B = {bb5}")
    print(f"  Revising with φ = {neg_q}")
    revised5 = bb5.revise(neg_q)
    print(f"  B * ~q = {revised5}")
    results.append(test_success(bb5, neg_q, "Ex5"))
    results.append(test_inclusion(bb5, neg_q, "Ex5"))
    results.append(test_vacuity(bb5, neg_q, "Ex5"))
    results.append(test_consistency(bb5, neg_q, "Ex5"))
    results.append(test_extensionality(bb5, neg_q, psi_ex1, "Ex5"))

    # ------------------------------------------------------------------
    # Summary
    # ------------------------------------------------------------------
    n_pass = sum(1 for r in results if r == PASS)
    n_fail = sum(1 for r in results if r == FAIL)
    print("\n" + "=" * 70)
    print(f"  RESULTS:  {n_pass} PASS  /  {n_fail} FAIL  /  {len(results)} total")
    print("=" * 70)


if __name__ == "__main__":
    run_all_tests()
