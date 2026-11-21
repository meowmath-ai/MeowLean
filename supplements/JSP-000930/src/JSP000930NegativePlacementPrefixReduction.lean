import JSP000930NegativeExplicitPlacementBook
import JSP000933GroundKappaTraceEnum

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
  JSP000933.PreparedModel JSP000930.Positive.Cohen

variable {N : Type}

def TraceBelow (scope : N → Finset GroundContinuumSuccIndex)
    (a : GroundContinuumSuccIndex) (t : N) : Prop :=
  ∀ b ∈ scope t,b < a

structure PlacementPrefixSystem (Q : ValuedPoset PreparedBA N) where
  scope : N → Finset GroundContinuumSuccIndex
  Trace : GroundContinuumSuccIndex → Type
  poset : ∀ a, ValuedPoset PreparedBA (Trace a)
  into : ∀ a, CompleteValueMap (TotalBA (poset a)) (TotalBA Q)
  earlierTrace : ∀ a t, TraceBelow scope a t → Trace a
  rectangle : ∀ a t h (m : PreparedBA),
    (into a).toFun (traceRectangle (poset a) (earlierTrace a t h) m) =
      traceRectangle Q t m

theorem PlacementBook.two_initialScopes (F : PlacementBook N)
    (scope : N → Finset GroundContinuumSuccIndex) (i j : PlacementTableIndex) :
    ∃ a : GroundContinuumSuccIndex,
      (∀ t : ClosedKappaCut i.1,TraceBelow scope a (F.trace t.val)) ∧
      (∀ t : ClosedKappaCut j.1,TraceBelow scope a (F.trace t.val)) := by
  obtain ⟨c⟩ := kappa_above_nonempty (max i.1 j.1)
  obtain ⟨a,ha⟩ := groundKappaEnumeration_prefixStages_bounded_r477 F.trace scope c.val
  exact ⟨a,fun t => ha t.val
    (t.property.trans_lt ((le_max_left _ _).trans_lt c.property)),
    fun t => ha t.val (t.property.trans_lt ((le_max_right _ _).trans_lt c.property))⟩

noncomputable def PlacementPrefixSystem.localRow
    {Q : ValuedPoset PreparedBA N} (P : PlacementPrefixSystem Q)
    (F : PlacementBook N) (i : PlacementTableIndex) (a : GroundContinuumSuccIndex)
    (h : ∀ t : ClosedKappaCut i.1,TraceBelow P.scope a (F.trace t.val)) :
    ℕ → TotalBA (P.poset a) :=
  placementTableReal (P.poset a) (F.mixed i.1)
    (fun t : ClosedKappaCut i.1 => P.earlierTrace a (F.trace t.val) (h t))
    i.2.1 (decodeCutCode i.2.1 (F.preparedReals i.2.2))

theorem PlacementPrefixSystem.localRow_commutes
    {Q : ValuedPoset PreparedBA N} (P : PlacementPrefixSystem Q)
    (F : PlacementBook N) (i : PlacementTableIndex) (a : GroundContinuumSuccIndex)
    (h : ∀ t : ClosedKappaCut i.1,TraceBelow P.scope a (F.trace t.val)) (n : ℕ) :
    (P.into a).toFun (P.localRow F i a h n) = F.row Q i n := by
  simp only [PlacementPrefixSystem.localRow,PlacementBook.row,placementTableReal,
    (P.into a).map_iSup,P.rectangle]

theorem PlacementPrefixSystem.two_actualRows_in_prefix
    {Q : ValuedPoset PreparedBA N} (P : PlacementPrefixSystem Q)
    (F : PlacementBook N) (i j : PlacementTableIndex) :
    ∃ (a : GroundContinuumSuccIndex) (x y : ℕ → TotalBA (P.poset a)),
      (∀ n,(P.into a).toFun (x n) = F.row Q i n) ∧
      (∀ n,(P.into a).toFun (y n) = F.row Q j n) := by
  obtain ⟨a,hi,hj⟩ := F.two_initialScopes P.scope i j
  exact ⟨a,P.localRow F i a hi,P.localRow F j a hj,
    P.localRow_commutes F i a hi,P.localRow_commutes F j a hj⟩

end JSP000930.Negative
