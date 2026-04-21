"""
Belief base with priority ordering and AGM belief change operations.

beliefs[0] is the most entrenched formula, beliefs[-1] is least entrenched.
Contraction uses partial meet: finds all maximal subsets not entailing phi,
selects those keeping the most entrenched beliefs, returns their intersection.
Revision uses the Levi identity: B * phi = (B / ~phi) + phi.
"""

from formula import Formula, Not, parse
from resolution import pl_resolution, is_consistent


def _entails(formulas: list, query: Formula) -> bool:
    return pl_resolution(formulas, query)


class BeliefBase:
    """Ordered belief base with AGM belief change operations."""

    def __init__(self, formulas=None):
        self.beliefs = list(formulas) if formulas else []

    def __repr__(self):
        if not self.beliefs:
            return "BeliefBase(empty)"
        items = "\n".join(
            f"  [{i}] {f}  (priority {i})" for i, f in enumerate(self.beliefs)
        )
        return f"BeliefBase([\n{items}\n])"

    def __len__(self):
        return len(self.beliefs)

    def __iter__(self):
        return iter(self.beliefs)

    def __contains__(self, formula: Formula):
        return formula in self.beliefs

    def display(self):
        print(repr(self))

    def entails(self, query: Formula) -> bool:
        return _entails(self.beliefs, query)

    def is_consistent(self) -> bool:
        return is_consistent(self.beliefs)

    def expand(self, phi: Formula) -> 'BeliefBase':
        """Return B + phi (add phi, no consistency check)."""
        new_beliefs = list(self.beliefs)
        if phi not in new_beliefs:
            new_beliefs.append(phi)
        return BeliefBase(new_beliefs)

    def contract(self, phi: Formula) -> 'BeliefBase':
        """Partial meet contraction: return B without entailing phi."""
        if not _entails(self.beliefs, phi):
            return BeliefBase(list(self.beliefs))

        remainders = _compute_remainders(self.beliefs, phi)
        if not remainders:
            return BeliefBase([])

        selected = _select_remainders(remainders, self.beliefs)
        if not selected:
            return BeliefBase([])

        # preserve original priority order in the intersection
        intersection_set = set.intersection(*[set(r) for r in selected])
        result = [f for f in self.beliefs if f in intersection_set]
        return BeliefBase(result)

    def revise(self, phi: Formula) -> 'BeliefBase':
        """Revision via Levi identity: B * phi = (B / ~phi) + phi."""
        neg_phi = Not(phi)
        contracted = self.contract(neg_phi)
        return contracted.expand(phi)

    def add(self, formula: Formula, priority: int = None):
        """Add formula at given priority (0 = highest), or append if None."""
        if formula in self.beliefs:
            return
        if priority is None:
            self.beliefs.append(formula)
        else:
            self.beliefs.insert(priority, formula)

    def remove(self, formula: Formula):
        if formula in self.beliefs:
            self.beliefs.remove(formula)


def _compute_remainders(beliefs: list, phi: Formula) -> list:
    """Return all maximal subsets of beliefs that do not entail phi."""
    remainders = []
    _remainder_search(beliefs, phi, list(range(len(beliefs))), remainders, set())
    return remainders


def _remainder_search(beliefs, phi, indices, remainders, seen):
    key = frozenset(indices)
    if key in seen:
        return
    seen.add(key)

    subset = [beliefs[i] for i in indices]
    if not _entails(subset, phi):
        _add_remainder_if_maximal(subset, remainders)
        return

    for idx in indices:
        smaller_indices = [i for i in indices if i != idx]
        _remainder_search(beliefs, phi, smaller_indices, remainders, seen)


def _add_remainder_if_maximal(candidate: list, remainders: list):
    candidate_set = set(id(f) for f in candidate)
    for existing in remainders:
        existing_set = set(id(f) for f in existing)
        if candidate_set <= existing_set:
            return  # subsumed by existing
        if existing_set <= candidate_set:
            remainders.remove(existing)
            break
    remainders.append(candidate)


def _select_remainders(remainders: list, original_beliefs: list) -> list:
    """Pick remainders that retain the most entrenched beliefs."""
    priority = {id(f): i for i, f in enumerate(original_beliefs)}

    def score(remainder):
        # lower indices = more entrenched = better
        return tuple(sorted(priority[id(f)] for f in remainder))

    best_score = min(score(r) for r in remainders)
    return [r for r in remainders if score(r) == best_score]
