"""
Converts propositional formulas to CNF clause sets.

Steps: eliminate biconditionals, eliminate implications,
move negation inward (De Morgan), distribute OR over AND.
Output is a list of frozensets, each a set of (atom_name, polarity) literals.
"""

from formula import Formula, Atom, Not, And, Or, Implies, Biconditional


def _elim_biconditional(f: Formula) -> Formula:
    if isinstance(f, Atom):
        return f
    elif isinstance(f, Not):
        return Not(_elim_biconditional(f.operand))
    elif isinstance(f, And):
        return And(_elim_biconditional(f.left), _elim_biconditional(f.right))
    elif isinstance(f, Or):
        return Or(_elim_biconditional(f.left), _elim_biconditional(f.right))
    elif isinstance(f, Implies):
        return Implies(_elim_biconditional(f.antecedent),
                       _elim_biconditional(f.consequent))
    elif isinstance(f, Biconditional):
        a = _elim_biconditional(f.left)
        b = _elim_biconditional(f.right)
        return And(Implies(a, b), Implies(b, a))
    raise TypeError(f"Unknown formula type: {type(f)}")


def _elim_implication(f: Formula) -> Formula:
    if isinstance(f, Atom):
        return f
    elif isinstance(f, Not):
        return Not(_elim_implication(f.operand))
    elif isinstance(f, And):
        return And(_elim_implication(f.left), _elim_implication(f.right))
    elif isinstance(f, Or):
        return Or(_elim_implication(f.left), _elim_implication(f.right))
    elif isinstance(f, Implies):
        a = _elim_implication(f.antecedent)
        b = _elim_implication(f.consequent)
        return Or(Not(a), b)
    raise TypeError(f"Unknown formula type: {type(f)}")


def _move_not_inward(f: Formula) -> Formula:
    """Apply De Morgan and double negation until negation only touches atoms."""
    if isinstance(f, Atom):
        return f
    elif isinstance(f, Not):
        inner = f.operand
        if isinstance(inner, Atom):
            return f
        elif isinstance(inner, Not):
            return _move_not_inward(inner.operand)
        elif isinstance(inner, And):
            return Or(_move_not_inward(Not(inner.left)),
                      _move_not_inward(Not(inner.right)))
        elif isinstance(inner, Or):
            return And(_move_not_inward(Not(inner.left)),
                       _move_not_inward(Not(inner.right)))
        else:
            raise TypeError(f"Unexpected type inside Not after step 2: {type(inner)}")
    elif isinstance(f, And):
        return And(_move_not_inward(f.left), _move_not_inward(f.right))
    elif isinstance(f, Or):
        return Or(_move_not_inward(f.left), _move_not_inward(f.right))
    raise TypeError(f"Unknown formula type in move_not_inward: {type(f)}")


def _distribute_or_over_and(f: Formula) -> Formula:
    if isinstance(f, Atom) or isinstance(f, Not):
        return f
    elif isinstance(f, And):
        return And(_distribute_or_over_and(f.left),
                   _distribute_or_over_and(f.right))
    elif isinstance(f, Or):
        left = _distribute_or_over_and(f.left)
        right = _distribute_or_over_and(f.right)
        if isinstance(left, And):
            return And(_distribute_or_over_and(Or(left.left, right)),
                       _distribute_or_over_and(Or(left.right, right)))
        elif isinstance(right, And):
            return And(_distribute_or_over_and(Or(left, right.left)),
                       _distribute_or_over_and(Or(left, right.right)))
        else:
            return Or(left, right)
    raise TypeError(f"Unknown formula type in distribute_or: {type(f)}")


def _formula_to_cnf_formula(f: Formula) -> Formula:
    f = _elim_biconditional(f)
    f = _elim_implication(f)
    f = _move_not_inward(f)
    f = _distribute_or_over_and(f)
    return f


def _collect_clauses(f: Formula) -> list:
    if isinstance(f, And):
        return _collect_clauses(f.left) + _collect_clauses(f.right)
    else:
        return [_collect_literals(f)]


def _collect_literals(f: Formula) -> frozenset:
    if isinstance(f, Or):
        return _collect_literals(f.left) | _collect_literals(f.right)
    elif isinstance(f, Atom):
        return frozenset({(f.name, True)})
    elif isinstance(f, Not):
        if isinstance(f.operand, Atom):
            return frozenset({(f.operand.name, False)})
        else:
            raise ValueError(f"Negation of non-atom found after CNF conversion: {f}")
    else:
        raise ValueError(f"Unexpected formula type in clause: {type(f)}: {f}")


def to_cnf_clauses(formula: Formula) -> list:
    """Convert a formula to a list of CNF clauses (frozensets of literals)."""
    cnf_formula = _formula_to_cnf_formula(formula)
    clauses = _collect_clauses(cnf_formula)
    result = []
    for clause in clauses:
        pos = {name for name, pol in clause if pol}
        neg = {name for name, pol in clause if not pol}
        if pos & neg:
            continue  # tautological clause, skip
        result.append(clause)
    return result


def formulas_to_cnf_clauses(formulas) -> list:
    """Convert a list of formulas to a combined CNF clause set."""
    all_clauses = []
    for f in formulas:
        all_clauses.extend(to_cnf_clauses(f))
    return all_clauses
