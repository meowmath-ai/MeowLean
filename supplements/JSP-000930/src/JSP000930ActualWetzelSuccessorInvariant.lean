import JSP000930ActualLiveSiteNames
import JSP000930NegativeActualArbitraryRowCountableExpansion

open bSet
open scoped bSet Flypitch

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA

abbrev ActualWetzelPrefixCCC (a : GroundContinuumSuccIndex) : Prop :=
  ProjectedAntichainCCC (prefixMaskRealization actualWetzelTail (wetzel_bot_lt_work a)).project

def ActualWetzelJointCCC (a : GroundContinuumSuccIndex) : Prop :=
  ∀ s : Finset GroundContinuumSuccIndex,(∀ r ∈ s,a≤r) →
    ForcesRelativeCCC (actualSurvivorProduct a s)

def survivorDomainAdded (a : GroundContinuumSuccIndex) (u : Finset GroundContinuumSuccIndex)
    (r j : GroundContinuumSuccIndex) : Prop :=
  j<a ∨ (r∈u ∧ j=a)

private theorem survivorDomainAdded_bound {a r j : GroundContinuumSuccIndex}
    {u : Finset GroundContinuumSuccIndex} (h : survivorDomainAdded a u r j) :
    j<wetzelGroundNext a :=
  (wetzelGroundNext_spec a j).mpr (h.elim (fun hlt => hlt.le) (fun he => he.2.le))

theorem actualSuccessor_add_all_live_fibres (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex)
    (hPrev : ∀ b≤a,ActualWetzelPrefixCCC b) (hNext : ActualWetzelPrefixCCC (wetzelGroundNext a))
    (hOld : ForcesRelativeCCC (actualSurvivorOldDomainProduct a s)) :
    ForcesRelativeCCC (actualSurvivorProduct (wetzelGroundNext a) s) := by
  classical
  let b := wetzelGroundNext a
  let site := (actualWorkingInputs b).site
  let H : (↑s : Type) → GroundContinuumSuccIndex → ℕ → ComplexBits (ActualWorkBA b) :=
    fun r => actualWetzelRowPalette b r.val
  let A (u : Finset GroundContinuumSuccIndex) (r : s) := survivorDomainAdded a u r.val
  have hOmega := actualWorkingPrefix_boundsOmegaOne b hNext
  have hK (j : GroundContinuumSuccIndex) (hj : j<b) : BoundsSmallKappaNames (ActualWorkBA j) :=
    nativeWetzelPrefix_boundsKappa actualWetzelRest j (hPrev j ((wetzelGroundNext_spec a j).mp hj))
  have hSite (j : GroundContinuumSuccIndex) : (site j).CutOn ⊤ := actualWorkingSite_proper b j
  have hH (r : s) (j : GroundContinuumSuccIndex) (n : ℕ) : (H r j n).CutOn ⊤ :=
    actualWetzelRowPalette_proper b r.val j n
  have hCCC (u : Finset GroundContinuumSuccIndex) (hu : u⊆s) :
      ForcesRelativeCCC (rowProductQ (fun r : s => supportedSymbolicQ site (H r) (A u r))) := by
    induction u using Finset.induction_on with
    | empty =>
      have he : A ∅ = fun _ => WorkingDomain a := by
        funext r j
        apply propext
        simp [A,survivorDomainAdded]
      rw [he]
      exact hOld
    | @insert r u hr ih =>
      let k : s := ⟨r,hu (Finset.mem_insert_self r u)⟩
      have hU : u⊆s := fun _ hx => hu (Finset.mem_insert_of_mem hx)
      apply symbolicRowProduct_oneFibre_at site H (A u) (A (insert r u)) k a
        _ _ hOmega hSite hH _ (ih hU)
      · intro j
        change ((j<a ∨ (r∈u ∧ j=a)) ∨ j=a) ↔
          (j<a ∨ (r∈insert r u ∧ j=a))
        simp only [hr,false_and,or_false,Finset.mem_insert_self,true_and]
      · intro i hik j
        have hne : i.val≠r := fun h => hik (Subtype.ext h)
        simp only [A,survivorDomainAdded,Finset.mem_insert,hne,false_or]
      · intro i j hi hj hij
        have he := actualWorkingSite_supportApart b hK
          (survivorDomainAdded_bound hi) (survivorDomainAdded_bound hj) hij
        rw [he,compl_bot] <;> exact le_rfl
  have hf : A s = fun _ => WorkingDomain b := by
    funext r j
    apply propext
    change (j<a ∨ (r.val∈s ∧ j=a)) ↔ j<b
    rw [wetzelGroundNext_spec]
    exact ⟨fun h => h.elim (fun hlt => hlt.le) (fun he => he.2.le),
      fun h => (lt_or_eq_of_le h).elim Or.inl (fun he => Or.inr ⟨r.property,he⟩)⟩
  have h := hCCC s (fun _ h => h)
  rw [hf] at h
  exact h

theorem actualWetzelSuccessor_both (a : GroundContinuumSuccIndex)
    (hPrev : ∀ b≤a,ActualWetzelPrefixCCC b) (hJoint : ActualWetzelJointCCC a) :
    ActualWetzelPrefixCCC (wetzelGroundNext a) ∧ ActualWetzelJointCCC (wetzelGroundNext a) := by
  classical
  have hA : ForcesRelativeCCC ((actualWorkingInputs a).row a) :=
    actualChosenRowCCC_of_singleton a (hJoint {a} (fun i hi =>
      (Finset.mem_singleton.mp hi).ge))
  have hNext : ActualWetzelPrefixCCC (wetzelGroundNext a) :=
    actualWorkingSuccessor_projectedCCC a (hPrev a le_rfl) hA
  refine ⟨hNext,?_⟩
  intro s hs
  have hap : a<wetzelGroundNext a := (wetzelGroundNext_spec a a).mpr le_rfl
  have ha : a∉s := fun hm => hap.not_ge (hs a hm)
  have hBig : ForcesRelativeCCC (actualSurvivorProduct a (insert a s)) :=
    hJoint _ (fun r hr => (Finset.mem_insert.mp hr).elim Eq.ge
      (fun hr => hap.le.trans (hs r hr)))
  exact actualSuccessor_add_all_live_fibres a s hPrev hNext
    (actualWorkingSuccessor_survivorsOldCCC a s (hPrev a le_rfl) hA ha hBig)

end JSP000930.Negative
