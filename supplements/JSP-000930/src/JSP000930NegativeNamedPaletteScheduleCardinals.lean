import JSP000930NegativeSmallNamedPaletteImages
import JSP000930PositiveNativeGrowthNaturality
import JSP000930AnalyticTaylorLimit

open bSet Cardinal Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.BooleanNames JSP000933.BooleanCompletion
  JSP000933.OpenGraphForcing JSP000933.RelativeOCA JSP000930.Positive JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure NamedPaletteSchedule (B : Type) [NontrivialCompleteBooleanAlgebra B] where
  code : GroundContinuumSuccIndex → TaylorSlot → B
  site : GroundContinuumSuccIndex → ComplexBits B
  palette : GroundContinuumSuccIndex → OmegaOneIndex → ℕ → bSet B
  codeCut : ∀ i n,(complexCoeffBits (code i) n).CutOn ⊤
  codeGrowth : ∀ i,GrowthOn ⊤ (complexCoeffBits (code i))
  siteCutOn : ∀ i,(site i).CutOn ⊤
  codeApart : ∀ i j,i ≠ j → (taylorCodeName (code i) =ᴮ taylorCodeName (code j)) = ⊥
  sitesCover : ∀ (z : ComplexBits B) (p : B), z.CutOn p →
    p ≤ ⨆ j,z.name =ᴮ (site j).name
  late : ∀ i j,j < i → (⊤ : B) ≤ ⨆ r : OmegaOneIndex,⨆ n : ℕ,
      (taylorLimitBits (complexCoeffBits (code i)) (site j)).name =ᴮ palette j r n

noncomputable def NamedPaletteSchedule.family (S : NamedPaletteSchedule B) : bSet B :=
  familyName (fun i => taylorCodeName (S.code i)) (fun _ => ⊤)

noncomputable def NamedPaletteSchedule.evalAtSite (S : NamedPaletteSchedule B)
    (i j : GroundContinuumSuccIndex) : bSet B :=
  (taylorLimitBits (complexCoeffBits (S.code i)) (S.site j)).name

noncomputable def NamedPaletteSchedule.siteImage (S : NamedPaletteSchedule B)
    (j : GroundContinuumSuccIndex) : bSet B :=
  familyName (fun i => S.evalAtSite i j) (fun _ => ⊤)

abbrev SiteCapIndex (j : GroundContinuumSuccIndex) := ClosedKappaCut j ⊕ (OmegaOneIndex × ℕ)

instance (j : GroundContinuumSuccIndex) : Nonempty (SiteCapIndex j) :=
  ⟨Sum.inl ⟨j,le_rfl⟩⟩

theorem siteCapIndex_card (j : GroundContinuumSuccIndex) : Cardinal.mk (SiteCapIndex j) ≤ 𝔠 := by
  simp only [SiteCapIndex,Cardinal.mk_sum,Cardinal.mk_prod,Cardinal.lift_id,
    Cardinal.mk_nat,mk_OmegaOneIndex_r61]
  exact Cardinal.add_le_of_le Cardinal.aleph0_le_continuum (closedKappaCut_card j)
    (Cardinal.mul_le_of_le Cardinal.aleph0_le_continuum Cardinal.aleph_one_le_continuum
      Cardinal.aleph0_le_continuum)

noncomputable def NamedPaletteSchedule.capCandidates (S : NamedPaletteSchedule B)
    (j : GroundContinuumSuccIndex) : SiteCapIndex j → bSet B
  | Sum.inl i => S.evalAtSite i.val j
  | Sum.inr (r,n) => S.palette j r n

theorem NamedPaletteSchedule.siteImage_cover (S : NamedPaletteSchedule B)
    (j : GroundContinuumSuccIndex) (a : bSet B) :
    (a ∈ᴮ S.siteImage j) ≤ ⨆ t,a =ᴮ S.capCandidates j t := by
  simp only [NamedPaletteSchedule.siteImage,mem_familyName_r70,top_inf_eq]
  apply iSup_le
  intro i
  by_cases h : i ≤ j
  · exact le_iSup (fun t => a =ᴮ S.capCandidates j t) (Sum.inl ⟨i,h⟩)
  · apply (le_inf le_rfl (le_top.trans (S.late i j (lt_of_not_ge h)))).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro r
    rw [inf_iSup_eq]
    apply iSup_le
    intro n
    exact le_iSup_of_le (Sum.inr (r,n)) (bv_trans inf_le_left inf_le_right)

theorem NamedPaletteSchedule.siteImage_injects_omegaOne (S : NamedPaletteSchedule B)
    (F : CompleteValueMap PreparedBA B) (j : GroundContinuumSuccIndex) :
    (⊤ : B) ≤ injects_into (S.siteImage j) (check BaseOmegaOne) :=
  prepared_smallNamedFamily_injects_omegaOne F (siteCapIndex_card j)
    (S.capCandidates j) (S.siteImage j) (S.siteImage_cover j)

theorem NamedPaletteSchedule.checkedKappa_injects_family (S : NamedPaletteSchedule B) :
    (⊤ : B) ≤ injects_into (check BaseSuccPSet) S.family := by
  exact injects_into_of_named_cover preparedOrdinalEntry (fun i => taylorCodeName (S.code i))
    _ _ checkedKappa_named_entries_cover
    (fun i => bSet.mem_mk (fun j => taylorCodeName (S.code j)) (fun _ => (⊤ : B)) i)
    S.codeApart

theorem NamedPaletteSchedule.family_notInject_omegaOne (S : NamedPaletteSchedule B)
    (hB : BoundsSmallKappaNames B) :
    injects_into S.family (check BaseOmegaOne) = ⊥ := by
  have hSmall : Cardinal.mk BaseOmegaOne.Type < GroundContinuumSucc := by
    rw [baseOmegaOne_type_card_r391]
    exact Cardinal.aleph_one_le_continuum.trans_lt (Order.lt_succ _)
  apply le_bot_iff.mp
  have h := injects_into_trans (le_top.trans S.checkedKappa_injects_family)
    (le_refl (injects_into S.family (check BaseOmegaOne)))
  simpa only [checkedSmall_notInject_kappa hB BaseOmegaOne hSmall] using h

end JSP000930.Negative
