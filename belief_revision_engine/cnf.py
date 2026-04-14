"""
cnf.py  –  Conversion of propositional formulas to Conjunctive Normal Form (CNF).

The algorithm follows AIMA Chapter 7, Section 7.5.2 (Figure 7.12) exactly:

  Step 1 – Eliminate biconditionals:
               (α <=> β)  →  (α => β) & (β => α)

  Step 2 – Eliminate implications:
               (α => β)   →  (~α | β)

  Step 3 – Move negation inward (De Morgan's laws + double-negation elimination):
               ~~α        →  α
               ~(α & β)   →  (~α | ~β)
               ~(α | β)   →  (~α & ~β)

  Step 4 – Distribute OR over AND:
               (α | (β & γ))  →  (α | β) & (α | γ)
               ((β & γ) | α)  →  (β | α) & (γ | α)

The output is a list of clauses.  Each clause is a frozenset of literals.
A literal is a pair  (atom_name: str, polarity: bool)  where polarity=True means
the positive literal (the atom itself) and polarity=False means the negative literal.

For example,  (p | ~q)  is represented as  frozenset({('p', True), ('q', False)}).
"""

from formula import Formula, Atom, Not, And, Or, Implies, Biconditional


# ---------------------------------------------------------------------------
# Step 1: eliminate biconditionals
# ---------------------------------------------------------------------------

def _elim_biconditional(f: Formula) -> Formula:
    """Replace every <=> with a pair of implications (both directions)."""
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
        # (a <=> b)  →  (a => b) & (b => a)
        return And(Implies(a, b), Implies(b, a))
    raise TypeError(f"Unknown formula type: {type(f)}")


# ---------------------------------------------------------------------------
# Step 2: eliminate implications
# ---------------------------------------------------------------------------

def _elim_implication(f: Formula) -> Formula:
    """Replace every => with a disjunction.  Assumes biconditionals are gone."""
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
        # (a => b)  →  (~a | b)
        return Or(Not(a), b)
    raise TypeError(f"Unknown formula type: {type(f)}")


# ---------------------------------------------------------------------------
# Step 3: move negation inward
# ---------------------------------------------------------------------------

def _move_not_inward(f: Formula) -> Formula:
    """Apply De Morgan and double-negation until negation only applies to atoms."""
    if isinstance(f, Atom):
        return f
    elif isinstance(f, Not):
        inner = f.operand
        if isinstance(inner, Atom):
            return f   # already a literal
        elif isinstance(inner, Not):
            # ~~α  →  α
            return _move_not_inward(inner.operand)
        elif isinstance(inner, And):
            # ~(α & β)  →  (~α | ~β)
            return Or(_move_not_inward(Not(inner.left)),
                      _move_not_inward(Not(inner.right)))
        elif isinstance(inner, Or):
            # ~(α | β)  →  (~α & ~β)
            return And(_move_not_inward(Not(inner.left)),
                       _move_not_inward(Not(inner.right)))
        else:
            raise TypeError(f"Unexpected type inside Not after step 2: {type(inner)}")
    elif isinstance(f, And):
        return And(_move_not_inward(f.left), _move_not_inward(f.right))
    elif isinstance(f, Or):
        return Or(_move_not_inward(f.left), _move_not_inward(f.right))
    raise TypeError(f"Unknown formula type in move_not_inward: {type(f)}")


# ---------------------------------------------------------------------------
# Step 4: distribute OR over AND
# ---------------------------------------------------------------------------

def _distribute_or_over_and(f: Formula) -> Formula:
    """Distribute OR over AND repeatedly until the formula is in CNF."""
    if isinstance(f, Atom) or isinstance(f, Not):
        return f   # already a literal
    elif isinstance(f, And):
        return And(_distribute_or_over_and(f.left),
                   _distribute_or_over_and(f.right))
    elif isinstance(f, Or):
        # Recursively convert both sides first
        left  = _distribute_or_over_and(f.left)
        right = _distribute_or_over_and(f.right)
        # Apply distributivity if one side is a conjunction
        if isinstance(left, And):
            # (α & β) | γ  →  (α | γ) & (β | γ)
            return And(_distribute_or_over_and(Or(left.left,  right)),
                       _distribute_or_over_and(Or(left.right, right)))
        elif isinstance(right, And):
            # α | (β & γ)  →  (α | β) & (α | γ)
            return And(_distribute_or_over_and(Or(left, right.left)),
                       _distribute_or_over_and(Or(left, right.right)))
        else:
            return Or(left, right)
    raise TypeError(f"Unknown formula type in distribute_or: {type(f)}")


# ---------------------------------------------------------------------------
# Conversion: Formula → list of clause frozensets
# ---------------------------------------------------------------------------

def _formula_to_cnf_formula(f: Formula) -> Formula:
    """Apply all four CNF steps and return the CNF formula (And of Ors of literals)."""
    f = _elim_biconditional(f)
    f = _elim_implication(f)
    f = _move_not_inward(f)
    f = _distribute_or_over_and(f)
    return f


def _collect_clauses(f: Formula) -> list:
    """Flatten a CNF formula (conjunction of disjunctions) into a list of clauses.

    Each clause is collected as a frozenset of literals.
    """
    if isinstance(f, And):
        return _collect_clauses(f.left) + _collect_clauses(f.right)
    else:
        # It must be a single clause (Or of literals, or a single literal)
        clause = _collect_literals(f)
        return [clause]


def _collect_literals(f: Formula) -> frozenset:
    """Return a frozenset of literals from a clause (Or of literals, or a literal)."""
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
    """Convert a Formula to a list of clauses in CNF.

    Returns a list of frozensets.  Each frozenset represents a clause (disjunction
    of literals).  Each literal is a pair  (atom_name: str, positive: bool).

    Tautological clauses (containing both  p  and  ~p) are discarded as an
    optimisation, since they add no information to the clause set.

    Parameters
    ----------
    formula : Formula
        Any well-formed propositional formula.

    Returns
    -------
    list[frozenset]
        The CNF clause set representing the formula.
    """
    cnf_formula = _formula_to_cnf_formula(formula)
    clauses = _collect_clauses(cnf_formula)
    # Remove tautological clauses: a clause containing both (p, True) and (p, False)
    result = []
    for clause in clauses:
        atom_names_pos = {name for name, pol in clause if pol}
        atom_names_neg = {name for name, pol in clause if not pol}
        if atom_names_pos & atom_names_neg:
            continue   # tautological clause – skip
        result.append(clause)
    return result


def formulas_to_cnf_clauses(formulas) -> list:
    """Convert a list of formulas to a combined CNF clause set.

    Concatenates the clause sets of each formula (their conjunction in CNF).
    """
    all_clauses = []
    for f in formulas:
        all_clauses.extend(to_cnf_clauses(f))
    return all_clauses
