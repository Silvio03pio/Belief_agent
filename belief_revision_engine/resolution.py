"""
resolution.py  –  Resolution-based propositional entailment checker.

Implements the PL-Resolution algorithm from AIMA Chapter 7, Figure 7.13:

    function PL-RESOLUTION(KB, α) returns true or false
        clauses ← CNF(KB ∧ ¬α)
        new ← {}
        while true do
            for each pair (Ci, Cj) in clauses do
                resolvents ← PL-RESOLVE(Ci, Cj)
                if resolvents contains the empty clause then return true
                new ← new ∪ resolvents
            if new ⊆ clauses then return false
            clauses ← clauses ∪ new

To check KB ⊨ α we show that (KB ∧ ¬α) is unsatisfiable by deriving the
empty clause (a contradiction) via repeated application of the resolution rule:

    From  (l ∨ C1)  and  (¬l ∨ C2)  derive  (C1 ∨ C2).

Soundness: any resolvent is a logical consequence of its parent clauses.
Completeness: the Ground Resolution Theorem (AIMA §7.5.2) guarantees that
if a set of clauses is unsatisfiable then the resolution closure contains the
empty clause – so PL-Resolution is both sound and complete.

Clauses are represented as frozensets of (atom_name, polarity) pairs (see cnf.py).
"""

from formula import Formula, Not
from cnf import formulas_to_cnf_clauses, to_cnf_clauses


# ---------------------------------------------------------------------------
# Core resolution rule
# ---------------------------------------------------------------------------

def pl_resolve(clause1: frozenset, clause2: frozenset) -> list:
    """Apply the resolution rule to two clauses.

    Returns a list of all possible resolvent clauses obtained by resolving one
    complementary literal pair at a time (as per AIMA: resolve only one pair).

    Each resolvent has tautological clauses removed.  A resolvent that contains
    both  (p, True)  and  (p, False)  for any atom  p  is tautological and
    is excluded from the output (it carries no information).

    Parameters
    ----------
    clause1, clause2 : frozenset
        Two CNF clauses represented as frozensets of (name, polarity) literals.

    Returns
    -------
    list[frozenset]
        All non-tautological resolvents.  May be empty if no complementary
        literals exist.  May contain the empty frozenset (the empty clause).
    """
    resolvents = []
    for name, pol in clause1:
        complement = (name, not pol)
        if complement in clause2:
            # Resolve on this literal: merge the two clauses, remove the pair
            new_clause = (clause1 - {(name, pol)}) | (clause2 - {complement})
            # Check for tautology (both p and ~p present)
            pos_atoms = {n for n, p in new_clause if p}
            neg_atoms = {n for n, p in new_clause if not p}
            if pos_atoms & neg_atoms:
                continue   # tautological – discard
            resolvents.append(frozenset(new_clause))
    return resolvents


# ---------------------------------------------------------------------------
# Main entailment procedure
# ---------------------------------------------------------------------------

def pl_resolution(kb_formulas: list, query: Formula) -> bool:
    """Check whether the knowledge base entails the query:  KB ⊨ query.

    Uses the PL-Resolution algorithm (proof by refutation):
    convert  (KB ∧ ¬query)  to CNF and derive the empty clause.

    Parameters
    ----------
    kb_formulas : list[Formula]
        The knowledge base as a list of propositional Formula objects.
    query : Formula
        The formula whose entailment is to be tested.

    Returns
    -------
    bool
        True  if  KB ⊨ query  (the empty clause is derived),
        False if  KB ⊭ query  (no new clauses can be derived).
    """
    # Negate the query
    negated_query = Not(query)

    # Convert KB ∧ ¬query to CNF clause set
    clauses = set()
    kb_clauses = formulas_to_cnf_clauses(kb_formulas)
    for c in kb_clauses:
        clauses.add(c)
    for c in to_cnf_clauses(negated_query):
        clauses.add(c)

    # Check immediately for the empty clause in the initial set
    if frozenset() in clauses:
        return True

    # Iteratively apply resolution until fixpoint or empty clause
    while True:
        new = set()
        clause_list = list(clauses)

        for i in range(len(clause_list)):
            for j in range(i + 1, len(clause_list)):
                resolvents = pl_resolve(clause_list[i], clause_list[j])
                for res in resolvents:
                    if len(res) == 0:          # empty clause  →  contradiction
                        return True
                    if res not in clauses:
                        new.add(res)

        if not new:
            # No new clauses were produced: fixpoint reached → not entailed
            return False

        clauses = clauses | new


# ---------------------------------------------------------------------------
# Consistency check
# ---------------------------------------------------------------------------

def is_consistent(formulas: list) -> bool:
    """Return True if the set of formulas is consistent (satisfiable).

    A set of formulas is consistent iff it does not entail  False,
    equivalently iff  (KB ∧ False)  =  KB is satisfiable.

    We use the fact that an inconsistent KB entails everything, including any
    atom  p  and its negation  ~p.  We check consistency by attempting to
    derive a contradiction from the clauses alone (without adding a negated
    query – i.e., we run resolution on the KB directly and check for the
    empty clause).
    """
    clauses = set(formulas_to_cnf_clauses(formulas))
    if frozenset() in clauses:
        return False

    while True:
        new = set()
        clause_list = list(clauses)
        for i in range(len(clause_list)):
            for j in range(i + 1, len(clause_list)):
                resolvents = pl_resolve(clause_list[i], clause_list[j])
                for res in resolvents:
                    if len(res) == 0:
                        return False
                    if res not in clauses:
                        new.add(res)
        if not new:
            return True
        clauses = clauses | new
