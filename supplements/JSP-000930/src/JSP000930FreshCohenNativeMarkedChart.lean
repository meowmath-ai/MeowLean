import JSP000930FreshCohenToActualStage

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive JSP000930.Negative.Cohen
open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.ForcingTransport

private theorem newDomain_iff930 (a j : GroundContinuumSuccIndex) :
    (WorkingDomain a j ∨ j=a) ↔ WorkingDomain (wetzelGroundNext a) j := by
  change (j<a ∨ j=a) ↔ j<wetzelGroundNext a
  rw [wetzelGroundNext_spec]
  exact ⟨fun h => h.elim (fun h => h.le) Eq.le,lt_or_eq_of_le⟩

def freshCohenLabelChart (a : GroundContinuumSuccIndex) (s : Finset GroundContinuumSuccIndex) :
    ((↥s : Type) → SupportedSymbolic GroundContinuumSuccIndex (fun j => WorkingDomain a j ∨ j=a)) ≃
      ActualSurvivorLabels (wetzelGroundNext a) s where
  toFun p r := includeSymbolicSupport (fun j => (newDomain_iff930 a j).mp) (p r)
  invFun p r := includeSymbolicSupport (fun j => (newDomain_iff930 a j).mpr) (p r)
  left_inv p := funext fun _ => Subtype.ext rfl
  right_inv p := funext fun _ => Subtype.ext rfl

noncomputable def freshCohenToNativeChart (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) :
    WeightedPosetChart (freshCohenTest a s) (actualSurvivorProduct (wetzelGroundNext a) s) where
  values := createdCohenIsoToHistory a
  label := freshCohenLabelChart a s
  valid p := by
    rw [createdCohenIsoToHistory_apply]
    change (createdCohenToHistory a).toFun
      (⨅ r : s,(supportedSymbolicQ (cohenSiteLift (beforeFreshSite a))
          (extendActualPalette (beforeFreshPalette a s) (fun t : s => actualWorkPaletteLabel a t.val) a r)
          (fun j => WorkingDomain a j ∨ j=a)).valid (p r)) = _
    rw [(createdCohenToHistory a).map_iInf]
    apply iInf_congr
    intro r
    exact symbolicLabel_partial_map (createdCohenToHistory a) _ _ _ _
      (fun j hj => freshCohenSite_to_native a j (hj.elim (fun h => h.le) Eq.le))
      (fun j hj n => freshCohenPalette_to_native a s r j (hj.elim (fun h => h.le) Eq.le) n)
      (p r).val (p r).2
  refines p q := by
    rw [createdCohenIsoToHistory_apply]
    change (createdCohenToHistory a).toFun
      (⨅ r : s,(supportedSymbolicQ (cohenSiteLift (beforeFreshSite a))
          (extendActualPalette (beforeFreshPalette a s) (fun t : s => actualWorkPaletteLabel a t.val) a r)
          (fun j => WorkingDomain a j ∨ j=a)).refines (p r) (q r)) = _
    rw [(createdCohenToHistory a).map_iInf]
    apply iInf_congr
    intro r
    exact symbolicLabel_refines_partial_map (createdCohenToHistory a) _ _ _ _
      (fun j hj => freshCohenSite_to_native a j (hj.elim (fun h => h.le) Eq.le))
      (fun j hj n => freshCohenPalette_to_native a s r j (hj.elim (fun h => h.le) Eq.le) n)
      (p r).val (q r).val (p r).2 (q r).2

noncomputable def freshCohenToNativeMarked (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA) :
    MaskedCondition (freshCohenTest a s)
      ((stageCohenMap (LiveRowModel a)).toFun ((actualWorkPreparedAfterRow a).toFun u)) ≃o
    MaskedCondition (actualSurvivorProduct (wetzelGroundNext a) s)
      ((actualPreparedAt (wetzelGroundNext a)).toFun u) :=
  {
    toFun := fun p => ⟨(freshCohenToNativeChart a s).totalIso p.val,
      ((createdCohenIsoToHistory a).monotone p.property).trans_eq (freshCohen_at_native_mark a u)⟩
    invFun := fun p => ⟨(freshCohenToNativeChart a s).totalIso.symm p.val,by
      change (createdCohenIsoToHistory a).symm p.val.mask ≤
        (stageCohenMap (LiveRowModel a)).toFun ((actualWorkPreparedAfterRow a).toFun u)
      apply (createdCohenIsoToHistory a).le_iff_le.mp
      rw [OrderIso.apply_symm_apply,freshCohen_at_native_mark]
      exact p.property⟩
    left_inv := fun p => Subtype.ext ((freshCohenToNativeChart a s).totalIso.symm_apply_apply p.val)
    right_inv := fun p => Subtype.ext ((freshCohenToNativeChart a s).totalIso.apply_symm_apply p.val)
    map_rel_iff' := (freshCohenToNativeChart a s).totalIso.le_iff_le
  }

theorem freshCohenToNativeMarked_data (a : GroundContinuumSuccIndex) (s : Finset GroundContinuumSuccIndex)
    (u : PreparedBA) (p : MaskedCondition (freshCohenTest a s)
      ((stageCohenMap (LiveRowModel a)).toFun ((actualWorkPreparedAfterRow a).toFun u))) :
    (freshCohenToNativeMarked a s u p).val = (freshCohenToNativeChart a s).totalIso p.val := rfl

end JSP000930.Negative
