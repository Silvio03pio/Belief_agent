"""
Resolution-based entailment checker.

To check KB |= query, add ~query to the KB, convert to CNF,
and try to derive the empty clause (proof by refutation).
"""

from formula import Formula, Not
from cnf import formulas_to_cnf_clauses, to_cnf_clauses


def pl_resolve(clause1: frozenset, clause2: frozenset) -> list:
    """Apply the resolution rule to two clauses.

    Returns all non-tautological resolvents. May include the empty clause.
    """
    resolvents = []
    for name, pol in clause1:
        complement = (name, not pol)
        if complement in clause2:
            new_clause = (clause1 - {(name, pol)}) | (clause2 - {complement})
            pos_atoms = {n for n, p in new_clause if p}
            neg_atoms = {n for n, p in new_clause if not p}
            if pos_atoms & neg_atoms:
                continue  # tautological
            resolvents.append(frozenset(new_clause))
    return resolvents


def pl_resolution(kb_formulas: list, query: Formula) -> bool:
    """Check KB |= query using proof by refutation.

    Returns True if the empty clause is derived (query is entailed).
    """
    negated_query = Not(query)

    clauses = set()
    for c in formulas_to_cnf_clauses(kb_formulas):
        clauses.add(c)
    for c in to_cnf_clauses(negated_query):
        clauses.add(c)

    if frozenset() in clauses:
        return True

    while True:
        new = set()
        clause_list = list(clauses)
        for i in range(len(clause_list)):
            for j in range(i + 1, len(clause_list)):
                resolvents = pl_resolve(clause_list[i], clause_list[j])
                for res in resolvents:
                    if len(res) == 0:
                        return True
                    if res not in clauses:
                        new.add(res)
        if not new:
            return False
        clauses = clauses | new


def is_consistent(formulas: list) -> bool:
    """Return True if the set of formulas is satisfiable."""
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
