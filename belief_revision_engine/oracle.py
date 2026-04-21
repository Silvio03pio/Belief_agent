"""
Truth-table semantic oracle for propositional logic.

Used ONLY in the test suite to cross-check the resolution-based engine.
This is NOT a replacement for the production resolution engine.

Practical limit: keep atom vocabularies at 4 or fewer (<=16 truth assignments).
"""

from itertools import product
from formula import Formula, Atom, Not, And, Or, Implies, Biconditional
from formula import atoms as _formula_atoms


def _eval(formula: Formula, assignment: dict) -> bool:
    """Evaluate a formula under a truth assignment {atom_name: bool}."""
    if isinstance(formula, Atom):
        return assignment.get(formula.name, False)
    elif isinstance(formula, Not):
        return not _eval(formula.operand, assignment)
    elif isinstance(formula, And):
        return _eval(formula.left, assignment) and _eval(formula.right, assignment)
    elif isinstance(formula, Or):
        return _eval(formula.left, assignment) or _eval(formula.right, assignment)
    elif isinstance(formula, Implies):
        return not _eval(formula.antecedent, assignment) or _eval(formula.consequent, assignment)
    elif isinstance(formula, Biconditional):
        return _eval(formula.left, assignment) == _eval(formula.right, assignment)
    raise TypeError(f"Unknown formula type: {type(formula)}")


def _all_atoms(formulas: list) -> list:
    """Return sorted list of all atom names appearing in a list of formulas."""
    names = set()
    for f in formulas:
        names |= _formula_atoms(f)
    return sorted(names)


def oracle_entails(kb_formulas: list, query: Formula) -> bool:
    """
    Check KB |= query by exhaustive truth-table enumeration.

    Returns True iff every model (truth assignment) satisfying all formulas
    in kb_formulas also satisfies query.
    """
    atom_names = _all_atoms(list(kb_formulas) + [query])
    for values in product((True, False), repeat=len(atom_names)):
        assignment = dict(zip(atom_names, values))
        if all(_eval(f, assignment) for f in kb_formulas):
            if not _eval(query, assignment):
                return False  # found a KB-model that falsifies query
    return True


def oracle_is_tautology(formula: Formula) -> bool:
    """Return True if formula is true under every truth assignment."""
    atom_names = sorted(_formula_atoms(formula))
    for values in product((True, False), repeat=len(atom_names)):
        assignment = dict(zip(atom_names, values))
        if not _eval(formula, assignment):
            return False
    return True


def oracle_is_contradiction(formula: Formula) -> bool:
    """Return True if formula is false under every truth assignment."""
    atom_names = sorted(_formula_atoms(formula))
    for values in product((True, False), repeat=len(atom_names)):
        assignment = dict(zip(atom_names, values))
        if _eval(formula, assignment):
            return False
    return True


def oracle_is_consistent(formulas: list) -> bool:
    """Return True if there exists a truth assignment satisfying all formulas."""
    atom_names = _all_atoms(formulas)
    for values in product((True, False), repeat=len(atom_names)):
        assignment = dict(zip(atom_names, values))
        if all(_eval(f, assignment) for f in formulas):
            return True
    return False


def oracle_equivalent(f1: Formula, f2: Formula) -> bool:
    """Return True if f1 and f2 have identical truth values under every assignment."""
    return oracle_entails([f1], f2) and oracle_entails([f2], f1)
