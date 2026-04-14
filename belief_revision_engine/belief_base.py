"""
belief_base.py  –  Belief base with priority ordering and AGM belief change operations.

The belief base B is an ordered list of propositional formulas
    B = [φ₁, φ₂, …, φₙ]
where lower index means *higher priority* (more entrenched).  φ₁ is the most
entrenched belief and φₙ is the least entrenched.

Three core operations are implemented:

    Expansion   B + φ   – simply add φ to the belief base (AIMA §7.3, slides9)
    Contraction B ÷ φ   – partial meet contraction based on priority ordering
    Revision    B * φ   – via the Levi Identity:  B * φ = (B ÷ ¬φ) + φ

Contraction algorithm (partial meet contraction, slides9 / Gärdenfors 1988):
  1. Compute all maximal subsets of B that do NOT entail φ  (the "remainders" B ⊥ φ).
  2. Apply the selection function γ: prefer subsets that retain the highest-priority
     formulas, i.e., rank subsets by the smallest index of their lowest-priority
     formula, and keep all subsets that tie for best.
  3. Return the intersection of the selected remainders.

References
----------
  AIMA Chapter 7 (Russell & Norvig)   – entailment, CNF, resolution
  DTU 02180 slides9                   – belief revision, Levi Identity, AGM postulates
  Gärdenfors (1988)                   – AGM framework (as presented in slides9)
"""

from formula import Formula, Not, parse
from resolution import pl_resolution, is_consistent


# ---------------------------------------------------------------------------
# Helper: check entailment from a list of formulas
# ---------------------------------------------------------------------------

def _entails(formulas: list, query: Formula) -> bool:
    """Return True if the conjunction of *formulas* entails *query*."""
    return pl_resolution(formulas, query)


# ---------------------------------------------------------------------------
# BeliefBase class
# ---------------------------------------------------------------------------

class BeliefBase:
    """An ordered belief base with AGM-style belief change operations.

    Attributes
    ----------
    beliefs : list[Formula]
        The current belief base.  beliefs[0] is the most entrenched formula.
    """

    def __init__(self, formulas=None):
        """Initialise the belief base, optionally from a list of Formula objects."""
        self.beliefs = list(formulas) if formulas else []

    # ------------------------------------------------------------------
    # Basic inspection
    # ------------------------------------------------------------------

    def __repr__(self):
        if not self.beliefs:
            return "BeliefBase(∅)"
        items = "\n".join(
            f"  [{i}] {f}  (priority {i})" for i, f in enumerate(self.beliefs)
        )
        return f"BeliefBase([\n{items}\n])"

    def __len__(self):
        return len(self.beliefs)

    def __iter__(self):
        return iter(self.beliefs)

    def __contains__(self, formula: Formula):
        """Check membership by identity/equality of formula objects."""
        return formula in self.beliefs

    def display(self):
        """Print the belief base to stdout in a human-readable format."""
        print(repr(self))

    def entails(self, query: Formula) -> bool:
        """Return True if this belief base entails *query*."""
        return _entails(self.beliefs, query)

    def is_consistent(self) -> bool:
        """Return True if this belief base is consistent."""
        return is_consistent(self.beliefs)

    # ------------------------------------------------------------------
    # Expansion:  B + φ
    # ------------------------------------------------------------------

    def expand(self, phi: Formula) -> 'BeliefBase':
        """Return a new belief base that is the expansion B + φ.

        Expansion adds φ to the belief base (appended at the end, i.e.
        with the lowest priority among current beliefs).
        Expansion may introduce inconsistency.

        B + φ = Cn(B ∪ {φ})

        In a finite syntactic representation, we simply add φ if it is
        not already present.
        """
        new_beliefs = list(self.beliefs)
        if phi not in new_beliefs:
            new_beliefs.append(phi)
        return BeliefBase(new_beliefs)

    # ------------------------------------------------------------------
    # Contraction:  B ÷ φ
    # ------------------------------------------------------------------

    def contract(self, phi: Formula) -> 'BeliefBase':
        """Return a new belief base that is the partial meet contraction B ÷ φ.

        Algorithm:
          1. If  B ⊭ φ  (belief base does not entail φ), return B unchanged
             (contraction is vacuous — Failure postulate).
          2. Find all maximal subsets of B that do not entail φ
             (the "remainder set"  B ⊥ φ).
          3. Apply selection function based on priority:
             - Each candidate subset is scored by the index of its
               lowest-priority element (highest index = least entrenched).
             - We prefer subsets with the *highest* minimum priority
               (i.e., lowest index of their weakest element).
             - Among all subsets, we select those that retain the most
               highly-entrenched formulas.  Concretely, we compare candidates
               using a lexicographic ordering on their sorted priority indices.
          4. Return the intersection of the selected remainder subsets.

        If B ⊥ φ is empty (e.g. φ is a tautology that every subset entails),
        the contraction returns the empty belief base.
        """
        # -- Vacuity check --
        if not _entails(self.beliefs, phi):
            return BeliefBase(list(self.beliefs))

        # -- Find all maximal non-entailing subsets (remainders) --
        remainders = _compute_remainders(self.beliefs, phi)

        if not remainders:
            # Every subset entails φ (e.g. φ is a tautology)
            return BeliefBase([])

        # -- Selection function: prefer subsets retaining higher-priority beliefs --
        selected = _select_remainders(remainders, self.beliefs)

        # -- Intersection of selected remainders --
        if not selected:
            return BeliefBase([])

        # Preserve the original priority ordering in the intersection
        intersection_set = set.intersection(*[set(r) for r in selected])
        result = [f for f in self.beliefs if f in intersection_set]
        return BeliefBase(result)

    # ------------------------------------------------------------------
    # Revision:  B * φ  (Levi Identity)
    # ------------------------------------------------------------------

    def revise(self, phi: Formula) -> 'BeliefBase':
        """Return a new belief base that is the revision B * φ.

        Implements the Levi Identity (slides9):
            B * φ  :=  (B ÷ ¬φ) + φ

        Rationale: first remove any beliefs that are inconsistent with φ
        (contraction by ¬φ), then add φ (expansion with φ).  This guarantees
        that φ is in the result and the result is consistent (as long as φ
        itself is consistent).
        """
        neg_phi = Not(phi)
        contracted = self.contract(neg_phi)
        return contracted.expand(phi)

    # ------------------------------------------------------------------
    # Mutation helpers (for interactive use)
    # ------------------------------------------------------------------

    def add(self, formula: Formula, priority: int = None):
        """Add a formula to the belief base at the given priority position.

        Parameters
        ----------
        formula : Formula
        priority : int, optional
            0 = highest priority.  If None, appended at the end (lowest priority).
        """
        if formula in self.beliefs:
            return
        if priority is None:
            self.beliefs.append(formula)
        else:
            self.beliefs.insert(priority, formula)

    def remove(self, formula: Formula):
        """Remove a formula from the belief base (if present)."""
        if formula in self.beliefs:
            self.beliefs.remove(formula)


# ---------------------------------------------------------------------------
# Remainder-set computation
# ---------------------------------------------------------------------------

def _compute_remainders(beliefs: list, phi: Formula) -> list:
    """Compute the remainder set  B ⊥ φ.

    Returns all maximal subsets of *beliefs* (as lists preserving order)
    that do not entail *phi*.

    The algorithm starts from the full belief base and removes formulas
    one at a time (from least entrenched, i.e. highest index, to most
    entrenched) until the subset no longer entails φ.  We enumerate all
    such maximal subsets.

    We use a recursive enumeration:
      - Base case: the full subset does not entail φ → it is a remainder.
      - Inductive step: if the subset entails φ, try removing each element
        to get subsets that might not entail φ.
    """
    remainders = []
    _remainder_search(beliefs, phi, list(range(len(beliefs))), remainders, set())
    return remainders


def _remainder_search(beliefs, phi, indices, remainders, seen):
    """Recursive DFS to find all maximal subsets of beliefs[indices] not entailing phi."""
    key = frozenset(indices)
    if key in seen:
        return
    seen.add(key)

    subset = [beliefs[i] for i in indices]

    if not _entails(subset, phi):
        # This subset does not entail phi; it is maximal if none of its supersets
        # (with the removed elements re-added) would also not entail phi and be larger.
        # Since we only arrive here by removing elements, this is already maximal
        # w.r.t. what was removed so far.  Check that it is not subsumed.
        _add_remainder_if_maximal(subset, remainders)
        return

    # Subset entails phi: try removing each element to find a non-entailing subset
    for idx in indices:
        smaller_indices = [i for i in indices if i != idx]
        _remainder_search(beliefs, phi, smaller_indices, remainders, seen)


def _add_remainder_if_maximal(candidate: list, remainders: list):
    """Add *candidate* to *remainders* only if it is not subsumed by an existing entry."""
    candidate_set = set(id(f) for f in candidate)
    for existing in remainders:
        existing_set = set(id(f) for f in existing)
        if candidate_set <= existing_set:
            return   # candidate is a subset of an existing remainder → not maximal
        if existing_set <= candidate_set:
            remainders.remove(existing)
            break
    remainders.append(candidate)


# ---------------------------------------------------------------------------
# Selection function
# ---------------------------------------------------------------------------

def _select_remainders(remainders: list, original_beliefs: list) -> list:
    """Select the best remainders according to the priority ordering.

    The selection function scores each remainder subset by the *priority
    vector* of its elements: the sorted list of priority indices of its
    members (in ascending order of priority, i.e. most-entrenched first).

    We prefer a subset S over T if S contains a higher-priority belief
    that T does not, i.e. lexicographically S's sorted index list is
    "better" (smaller values = higher entrenchment = preferred).

    Concretely, we compute for each remainder the sorted tuple of its
    members' original indices, then select all remainders that share
    the maximum score (lex-minimum tuple — lower indices are preferred).
    """
    # Map formula id → index in original belief base
    priority = {id(f): i for i, f in enumerate(original_beliefs)}

    def score(remainder):
        # Sorted list of priorities (lower = more entrenched = better)
        return tuple(sorted(priority[id(f)] for f in remainder))

    # Lex-min score is best (retains most entrenched beliefs)
    best_score = min(score(r) for r in remainders)
    return [r for r in remainders if score(r) == best_score]
