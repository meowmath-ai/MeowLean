import JSP000930ActualInitialJointCCC

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.PreparedModel JSP000933.RelativeOCA

variable {I N B : Type} [CompleteBooleanAlgebra B]

noncomputable def insertRowChart (a : I) (s : Finset I) (ha : a∉s) [DecidableEq I] :
    ((↑(insert a s) : Type) → N) ≃ (N × ((↑s : Type) → N)) where
  toFun x := (x ⟨a,Finset.mem_insert_self _ _⟩,fun i => x ⟨i.val,Finset.mem_insert_of_mem i.2⟩)
  invFun p := fun i => if h : i.val=a then p.1 else
    p.2 ⟨i.val,(Finset.mem_insert.mp i.2).resolve_left h⟩
  left_inv := by
    intro x
    funext i
    by_cases hi : i.val=a
    · simp only [dite_eq_left hi]
      exact congrArg x (Subtype.ext hi.symm)
    · simp only [dite_eq_right hi]
  right_inv := by
    intro x
    apply Prod.ext
    · simp
    · funext i
      have h : i.val≠a := fun he => ha (he ▸ i.property)
      simp only [dite_eq_right h]

theorem iInf_finset_insert930 [DecidableEq I] (a : I) (s : Finset I)
    (f : (↑(insert a s) : Type) → B) :
    (⨅ i,f i) = f ⟨a,Finset.mem_insert_self _ _⟩ ⊓
      (⨅ i : s,f ⟨i.val,Finset.mem_insert_of_mem i.property⟩) := by
  apply le_antisymm
  · exact le_inf (iInf_le f ⟨a,Finset.mem_insert_self _ _⟩) (le_iInf (fun i => iInf_le f ⟨i.val,Finset.mem_insert_of_mem i.property⟩))
  · apply le_iInf
    intro i
    rcases Finset.mem_insert.mp i.property with hi|hi
    · have h : (⟨a,Finset.mem_insert_self a s⟩ : (↑(insert a s) : Type))=i :=
        Subtype.ext hi.symm
      exact inf_le_left.trans_eq (congrArg f h)
    · let j : s := ⟨i.val,hi⟩
      exact inf_le_right.trans (iInf_le_of_le j le_rfl)

theorem finiteRows_insert_factorCCC [DecidableEq I] (Q : I → ValuedPoset B N)
    (a : I) (s : Finset I) (ha : a∉s)
    (h : ForcesRelativeCCC (rowProductQ (fun i : (↑(insert a s) : Type) => Q i.val))) :
    ForcesRelativeCCC (valuedPair (Q a) (rowProductQ (fun i : s => Q i.val))) := by
  let E : ((↑(insert a s) : Type) → N) ≃ (N × ((↑s : Type) → N)) := insertRowChart a s ha
  let S := rowProductQ (fun i : (↑(insert a s) : Type) => Q i.val)
  let T := valuedPair (Q a) (rowProductQ (fun i : s => Q i.val))
  have hV (x : (↑(insert a s) : Type)→N) : S.valid x = T.valid (E x) :=
    iInf_finset_insert930 a s (fun i => (Q i.val).valid (x i))
  have hR (x y : (↑(insert a s) : Type)→N) : S.refines x y = T.refines (E x) (E y) :=
    iInf_finset_insert930 a s (fun i => (Q i.val).refines (x i) (y i))
  apply relCCC_of_labelEquiv T S E.symm _ _ h
  · intro p
    rw [hV,E.apply_symm_apply]
  · intro p q
    rw [hR,E.apply_symm_apply,E.apply_symm_apply]

theorem actualSurvivingRows_factorCCC (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (ha : a ∉ s)
    (h : ForcesRelativeCCC (actualSurvivorProduct a (insert a s))) :
    ForcesRelativeCCC (valuedPair ((actualWorkingInputs a).row a) (actualSurvivorProduct a s)) := by
  rw [← actualSurvivorRow_self a]
  exact finiteRows_insert_factorCCC (actualSurvivorRow a) a s ha h

end JSP000930.Negative
