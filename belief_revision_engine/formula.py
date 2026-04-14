"""
formula.py  –  Propositional formula representation, parser, and pretty-printer.

Formula classes (AST nodes) follow the syntax of propositional logic as presented
in AIMA Chapter 7 (Russell & Norvig) and DTU course 02180, slides 08 and 09.

Supported input syntax (strings passed to parse()):
    Atoms       : single lowercase letters or words,  e.g.  "p",  "rain"
    Negation    : "~p"
    Conjunction : "(p & q)"
    Disjunction : "(p | q)"
    Implication : "(p => q)"
    Biconditional: "(p <=> q)"

All binary operators must be fully parenthesised when parsed from a string.
Negation may be applied without extra parentheses: "~p", "~(p & q)".
"""


# ---------------------------------------------------------------------------
# AST node classes
# ---------------------------------------------------------------------------

class Formula:
    """Abstract base class for all propositional formulas."""
    pass


class Atom(Formula):
    """An atomic proposition symbol, e.g. Atom('p')."""

    def __init__(self, name: str):
        self.name = name

    def __repr__(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, Atom) and self.name == other.name

    def __hash__(self):
        return hash(('Atom', self.name))


class Not(Formula):
    """Negation:  ~operand."""

    def __init__(self, operand: Formula):
        self.operand = operand

    def __repr__(self):
        return f"~{self.operand}"

    def __eq__(self, other):
        return isinstance(other, Not) and self.operand == other.operand

    def __hash__(self):
        return hash(('Not', self.operand))


class And(Formula):
    """Conjunction:  (left & right)."""

    def __init__(self, left: Formula, right: Formula):
        self.left = left
        self.right = right

    def __repr__(self):
        return f"({self.left} & {self.right})"

    def __eq__(self, other):
        return isinstance(other, And) and self.left == other.left and self.right == other.right

    def __hash__(self):
        return hash(('And', self.left, self.right))


class Or(Formula):
    """Disjunction:  (left | right)."""

    def __init__(self, left: Formula, right: Formula):
        self.left = left
        self.right = right

    def __repr__(self):
        return f"({self.left} | {self.right})"

    def __eq__(self, other):
        return isinstance(other, Or) and self.left == other.left and self.right == other.right

    def __hash__(self):
        return hash(('Or', self.left, self.right))


class Implies(Formula):
    """Implication:  (antecedent => consequent)."""

    def __init__(self, antecedent: Formula, consequent: Formula):
        self.antecedent = antecedent
        self.consequent = consequent

    def __repr__(self):
        return f"({self.antecedent} => {self.consequent})"

    def __eq__(self, other):
        return (isinstance(other, Implies)
                and self.antecedent == other.antecedent
                and self.consequent == other.consequent)

    def __hash__(self):
        return hash(('Implies', self.antecedent, self.consequent))


class Biconditional(Formula):
    """Biconditional:  (left <=> right)."""

    def __init__(self, left: Formula, right: Formula):
        self.left = left
        self.right = right

    def __repr__(self):
        return f"({self.left} <=> {self.right})"

    def __eq__(self, other):
        return (isinstance(other, Biconditional)
                and self.left == other.left
                and self.right == other.right)

    def __hash__(self):
        return hash(('Biconditional', self.left, self.right))


# ---------------------------------------------------------------------------
# Tokeniser
# ---------------------------------------------------------------------------

def _tokenise(text: str):
    """Return a list of tokens from a formula string.

    Tokens are: '(', ')', '~', '&', '|', '=>', '<=>', and atom names.
    """
    tokens = []
    i = 0
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
        elif c == '(':
            tokens.append('(')
            i += 1
        elif c == ')':
            tokens.append(')')
            i += 1
        elif c == '~':
            tokens.append('~')
            i += 1
        elif c == '&':
            tokens.append('&')
            i += 1
        elif c == '|':
            tokens.append('|')
            i += 1
        elif text[i:i+3] == '<=>':
            tokens.append('<=>')
            i += 3
        elif text[i:i+2] == '=>':
            tokens.append('=>')
            i += 2
        elif c.isalpha() or c == '_':
            j = i
            while j < len(text) and (text[j].isalnum() or text[j] == '_'):
                j += 1
            tokens.append(text[i:j])
            i = j
        else:
            raise ValueError(f"Unexpected character '{c}' in formula: {text!r}")
    return tokens


# ---------------------------------------------------------------------------
# Recursive-descent parser
# ---------------------------------------------------------------------------

class _Parser:
    """LL(1) recursive-descent parser for propositional formulas."""

    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def consume(self, expected=None):
        tok = self.tokens[self.pos]
        if expected is not None and tok != expected:
            raise ValueError(f"Expected '{expected}', got '{tok}'")
        self.pos += 1
        return tok

    def parse(self) -> Formula:
        result = self._parse_formula()
        if self.pos != len(self.tokens):
            raise ValueError(f"Unexpected token '{self.peek()}' after formula")
        return result

    def _parse_formula(self) -> Formula:
        """Parse a complete formula."""
        tok = self.peek()

        if tok == '~':
            # Negation: ~<formula>
            self.consume('~')
            operand = self._parse_atom_or_paren()
            return Not(operand)
        elif tok == '(':
            return self._parse_paren()
        elif tok is not None and (tok.isalpha() or tok[0] == '_'):
            # Atom
            name = self.consume()
            return Atom(name)
        else:
            raise ValueError(f"Unexpected token '{tok}'")

    def _parse_atom_or_paren(self) -> Formula:
        """Parse either an atom, a parenthesised formula, or another negation."""
        tok = self.peek()
        if tok == '(':
            return self._parse_paren()
        elif tok == '~':
            self.consume('~')
            operand = self._parse_atom_or_paren()
            return Not(operand)
        elif tok is not None and (tok[0].isalpha() or tok[0] == '_'):
            name = self.consume()
            return Atom(name)
        else:
            raise ValueError(f"Unexpected token '{tok}' in atom/paren position")

    def _parse_paren(self) -> Formula:
        """Parse a parenthesised binary formula: ( LHS OP RHS )."""
        self.consume('(')
        left = self._parse_formula()
        op = self.peek()

        if op in ('&', '|', '=>', '<=>'):
            self.consume(op)
            right = self._parse_formula()
            self.consume(')')
            if op == '&':
                return And(left, right)
            elif op == '|':
                return Or(left, right)
            elif op == '=>':
                return Implies(left, right)
            else:  # '<=>'
                return Biconditional(left, right)
        elif op == ')':
            # (formula) — just grouping
            self.consume(')')
            return left
        else:
            raise ValueError(f"Expected binary operator inside parentheses, got '{op}'")


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def parse(text: str) -> Formula:
    """Parse a formula string into a Formula AST.

    Examples
    --------
    >>> parse("p")
    p
    >>> parse("~p")
    ~p
    >>> parse("(p & q)")
    (p & q)
    >>> parse("(p => q)")
    (p => q)
    >>> parse("(p <=> q)")
    (p <=> q)
    """
    tokens = _tokenise(text.strip())
    if not tokens:
        raise ValueError("Empty formula string")
    parser = _Parser(tokens)
    return parser.parse()


def pretty(formula: Formula) -> str:
    """Return a human-readable string for *formula* (same as repr for now)."""
    return repr(formula)


def atoms(formula: Formula) -> set:
    """Return the set of all atom names occurring in *formula*."""
    if isinstance(formula, Atom):
        return {formula.name}
    elif isinstance(formula, Not):
        return atoms(formula.operand)
    elif isinstance(formula, (And, Or, Implies, Biconditional)):
        left = formula.left if hasattr(formula, 'left') else formula.antecedent
        right = formula.right if hasattr(formula, 'right') else formula.consequent
        return atoms(left) | atoms(right)
    return set()


def logically_equivalent(f1: Formula, f2: Formula) -> bool:
    """Check whether f1 and f2 are logically equivalent by checking f1 <=> f2 is a tautology.

    Uses the resolution-based entailment checker from resolution.py.
    Imported lazily to avoid circular imports.
    """
    from resolution import pl_resolution
    # f1 ≡ f2  iff  |= (f1 <=> f2)
    # which is equivalent to: {} |= (f1 <=> f2)
    # i.e., (f1 <=> f2) is a tautology
    # We check: ~(f1 <=> f2) is unsatisfiable, i.e., entailed by empty KB
    return pl_resolution([], Biconditional(f1, f2))
