import JSP000933CoverCodePacking

open scoped Cardinal

namespace JSP000933
namespace CantorCodes

open FiniteSupport BooleanCompletion OpenGraphForcing

variable {N : OmegaTwoIndex → Type} {R : Rules N}

theorem exists_stage_below_of_cof_r116 (a : OmegaTwoIndex)
    (hcf : (ℵ₀ : Cardinal) < (omegaTwoOrdinal a).cof) : ∃ i, i < a := by
  let o := (Order.succ (ℵ₁ : Cardinal)).ord
  let e := Ordinal.ToType.mk (o := o)
  have hz : 0 < (e.symm a).1 := Ordinal.cof_pos.mp (Cardinal.aleph0_pos.trans hcf)
  have hzo : 0 < o := hz.trans (e.symm a).2
  have hh : (⟨0,hzo⟩ : ↥(Set.Iio o)) < e.symm a := hz
  have ht := e.strictMono hh
  rw [e.apply_symm_apply a] at ht
  exact ⟨e ⟨0,hzo⟩,ht⟩

structure ReflectedNoCover (a : OmegaTwoIndex) (S : ReflectingNameSchedule R)
    (D : OmegaTwoIndex → RO (Condition R)) (K : Word × Word → RO (Condition R))
    (p : RO (Condition R)) where
  x : ↥(Set.Iio a) → ℕ → RO (Before R a)
  d : ↥(Set.Iio a) → RO (Before R a)
  k : Word × Word → RO (Before R a)
  cond : RO (Before R a)
  cond_nonzero : cond ≠ ⊥
  x_agrees : ∀ i, liftBitsToWhole a (x i) = S.enumerate i.1
  d_agrees : ∀ i, (wholeReduction a).boolPullback (d i) = D i.1
  k_agrees : ∀ w, (wholeReduction a).boolPullback (k w) = K w
  cond_agrees : (wholeReduction a).boolPullback cond = p
  noCover : ∀ c : CoverCode (RO (Before R a)), cond ≤ (goodCoverValue x d k c)ᶜ

theorem exists_club_reflects_noCover_r116
    (hCCC : HasCountableAntichains (Condition R)) (S : ReflectingNameSchedule R)
    (D : OmegaTwoIndex → RO (Condition R)) (K : Word × Word → RO (Condition R))
    (p : RO (Condition R)) (hp : p ≠ ⊥)
    (hNo : ∀ c : CoverCode (RO (Condition R)), p ≤ (goodCoverValue S.enumerate D K c)ᶜ) :
    ∃ C : Set OmegaTwoIndex, OrdinalClub C ∧
      ∀ a ∈ C, (ℵ₀ : Cardinal) < (omegaTwoOrdinal a).cof →
        Nonempty (ReflectedNoCover a S D K p) := by
  classical
  let code (j : OmegaTwoIndex) := unpackCover (S.enumerate j)
  have hBool := booleanCCC_of_conditionCCC_r66 hCCC
  obtain ⟨guardM,hM⟩ := exists_witnessCaptureGuard_r113 hBool missFoot
    (fun j => missedPoint S.enumerate D (code j))
  obtain ⟨guardE,hE⟩ := exists_witnessCaptureGuard_r113 hBool edgeFoot
    (fun j => badEdge S.enumerate D K (code j))
  let all : Unit ⊕ (Word × Word) → RO (Condition R) :=
    fun q => Sum.elim (fun _ => p) K q
  obtain ⟨base,bv,hb⟩ := exists_properStage_for_countable_values_r101 hCCC all
  have hd (i : OmegaTwoIndex) : ∃ a : OmegaTwoIndex, ∃ v : RO (Before R a),
      (wholeReduction a).boolPullback v = D i := by
    obtain ⟨a,g,hg⟩ := exists_properStage_for_countable_values_r101 hCCC (fun _ : Unit => D i)
    exact ⟨a,g (),hg ()⟩
  choose stageD atD hD using hd
  have hCap (i : OmegaTwoIndex) : ∃ b, S.guard i < b ∧ stageD i < b ∧
      guardM i < b ∧ guardE i < b ∧ base < b := by
    obtain ⟨b,hh⟩ := OmegaTwoIndex_finite_bounded_r89 {S.guard i,stageD i,guardM i,guardE i,base}
    exact ⟨b,hh _ (by simp),hh _ (by simp),hh _ (by simp),hh _ (by simp),hh _ (by simp)⟩
  choose guard hGuard using hCap
  let C := stageClosedUnder guard
  refine ⟨C,stageClosedUnder_isClub_r108 guard,fun a ha hcf => ?_⟩
  obtain ⟨i,hi⟩ := exists_stage_below_of_cof_r116 a hcf
  have hBase : base < a := (hGuard i).2.2.2.2.trans (ha i hi)
  have hC : a ∈ S.club := by
    rw [S.club_eq]
    exact fun j hj => (hGuard j).1.trans (ha j hj)
  let x (i : ↥(Set.Iio a)) := canonicalStageDecode S.code S.stageEnumerate a i.1
  have hX (i : ↥(Set.Iio a)) : liftBitsToWhole a (x i) = S.enumerate i.1 :=
    S.localDecode_agrees a hC i.1 i.2
  let dLocal (i : ↥(Set.Iio a)) : RO (Before R a) :=
    let hs : stageD i.1 < a := (hGuard i.1).2.1.trans (ha i.1 i.2)
    (prefixReduction hs.le).boolPullback (atD i.1)
  have hDLocal (i : ↥(Set.Iio a)) : (wholeReduction a).boolPullback (dLocal i) = D i.1 :=
    (wholeReduction_coherent_r110 ((hGuard i.1).2.1.trans (ha i.1 i.2)).le (atD i.1)).trans (hD i.1)
  let kLocal (w : Word × Word) := (prefixReduction hBase.le).boolPullback (bv (.inr w))
  let pLocal := (prefixReduction hBase.le).boolPullback (bv (.inl ()))
  have hK (w : Word × Word) : (wholeReduction a).boolPullback (kLocal w) = K w :=
    (wholeReduction_coherent_r110 hBase.le (bv (.inr w))).trans (hb (.inr w))
  have hpLocal : (wholeReduction a).boolPullback pLocal = p :=
    (wholeReduction_coherent_r110 hBase.le (bv (.inl ()))).trans (hb (.inl ()))
  let F := (wholeReduction a (R := R)).completeValueMap
  have hNon : pLocal ≠ ⊥ := fun h => hp (hpLocal.symm.trans ((congrArg F.toFun h).trans F.map_bot))
  refine ⟨⟨x,dLocal,kLocal,pLocal,hNon,hX,hDLocal,hK,hpLocal,?_⟩⟩
  intro c
  obtain ⟨j,hja,hj⟩ := S.entry_for_every_local a hC hcf (packCover c)
  have hC' (n : ℕ) (w : Word) : F.toFun (c n w) = code j n w := by
    rw [show c = unpackCover (packCover c) from (unpack_packCover_r115 c).symm, map_unpackCover_r115]
    change unpackCover (liftBitsToWhole a (packCover c)) n w = _
    rw [← hj]
  have hEq := map_goodCover_of_captured_r114 F a x dLocal kLocal c S.enumerate D K (code j)
    (fun i n => congrFun (hX i) n) hDLocal hK hC'
    (hM a j ((hGuard j).2.2.1.trans (ha j hja)))
    (hE a j ((hGuard j).2.2.2.1.trans (ha j hja)))
  apply F.reflect_le_r93
  rw [F.map_compl,hEq]
  change (wholeReduction a).boolPullback pLocal ≤ _
  rw [hpLocal]
  exact hNo (code j)

end CantorCodes
end JSP000933
