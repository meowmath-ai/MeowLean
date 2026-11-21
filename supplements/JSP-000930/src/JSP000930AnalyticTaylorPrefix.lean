import JSP000930AnalyticComplexPower

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem forces_partialTaylorStep_weighted {n : ℕ} (v : DVec (V B) n)
    (prm : Fin 2 → STerm n) (I C W : STerm n) (i : ℕ) (g : bSet B)
    (a z c d : ComplexBits B) (p : B)
    (hG : bTerm v (prm 0) = g) (hZ : bTerm v (prm 1) = z.name)
    (hI : bTerm v I = bSet.of_nat i) (hC : bTerm v C = c.name)
    (hW : bTerm v W = d.name) (hd : d = c.add (a.mul (z.power i)))
    (ha : a.CutOn p) (hz : z.CutOn p) (hc : c.CutOn p)
    (hvalue : p ≤ bSet.pair (bSet.of_nat i) a.name ∈ᴮ g) :
    p ≤ bTruth v (partialTaylorStep_f prm I C W) := by
  let h := z.power i
  let t := a.mul h
  let v1 : DVec (V B) (n+1) := DVec.cons a.name v
  let v2 : DVec (V B) (n+2) := DVec.cons h.name v1
  let v3 : DVec (V B) (n+3) := DVec.cons t.name v2
  let A0 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let H0 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let T0 : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  have hI' : bTerm v3 (up3 I) = bSet.of_nat i := (bTerm_up3_r181 v a.name h.name t.name I).trans hI
  have hZ' : bTerm v3 (up3 (prm 1)) = z.name := (bTerm_up3_r181 v a.name h.name t.name _).trans hZ
  have hA : bTerm v3 (up2 A0) = a.name := by
    exact (bTerm_up2_r181 v1 h.name t.name A0).trans (bTerm_current_r181 v a.name)
  have hH : bTerm v3 (up H0) = h.name := by
    exact (bTerm_up_r181 v2 t.name H0).trans (bTerm_current_r181 v1 h.name)
  have hT : bTerm v3 T0 = t.name := bTerm_current_r181 v2 t.name
  have hC' : bTerm v3 (up3 C) = c.name := (bTerm_up3_r181 v a.name h.name t.name C).trans hC
  have hW' : bTerm v3 (up3 W) = d.name := (bTerm_up3_r181 v a.name h.name t.name W).trans hW
  have hh : h.CutOn p := ComplexBits.power_cutOn hz i
  have ht : t.CutOn p := ComplexBits.mul_cutOn ha hh
  unfold partialTaylorStep_f
  simp only [bTruth_sEx_r181]
  apply le_iSup_of_le a.name
  apply le_iSup_of_le h.name
  apply le_iSup_of_le t.name
  simp only [bTruth_and_eq]
  refine le_inf ?_ (le_inf ?_ (le_inf (forces_complexBits_name v3 T0 t p hT ht) (le_inf ?_ ?_)))
  · rw [bTruth_value,hI',hA,(bTerm_up3_r181 v a.name h.name t.name _).trans hG]
    exact hvalue
  · exact forces_complexPow_weighted v3 (up3 (prm 1)) (up3 I) (up H0) z i p hZ' hI' hH hz
  · apply forces_of_inf_eq_eqname
    exact bTruth_complexMul_weighted v3 (up2 A0) (up H0) T0 a h t p hA hH hT ha hh ht
  · have hd' : d.CutOn p := by
      rw [hd]
      exact ComplexBits.add_cutOn hc ht
    apply forces_of_inf_eq_eqname
    exact (bTruth_complexAdd_weighted v3 (up3 C) T0 (up3 W) c t d p hC' hT hW' hc ht hd').trans
      (by rw [hd])

theorem forces_partialTaylorSum_weighted {n : ℕ} (v : DVec (V B) n)
    (A Z M W : STerm n) (g : bSet B) (a : ℕ → ComplexBits B) (z : ComplexBits B)
    (m : ℕ) (p : B)
    (hA : bTerm v A = g) (hZ : bTerm v Z = z.name) (hM : bTerm v M = bSet.of_nat m)
    (hW : bTerm v W = (taylorPrefixBits a z m).name)
    (ha : ∀ i < m, (a i).CutOn p) (hz : z.CutOn p)
    (hvalue : ∀ i < m, p ≤ bSet.pair (bSet.of_nat i) (a i).name ∈ᴮ g) :
    p ≤ bTruth v (partialTaylorSum_f A Z M W) := by
  let f := taylorPrefixBits a z
  let base := (f 0).name
  let v1 : DVec (V B) (n+1) := DVec.cons base v
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let P : Fin 2 → STerm (n+1) := fun j => if j = 0 then up A else up Z
  let V : Fin 2 → bSet B := fun j => if j = 0 then g else z.name
  have hP : ∀ j, bTerm v1 (P j) = V j := by
    intro j
    by_cases hj : j = 0
    · simp only [P,V,ite_eq_left hj]
      exact (bTerm_up_r181 v base A).trans hA
    · simp only [P,V,ite_eq_right hj]
      exact (bTerm_up_r181 v base Z).trans hZ
  unfold partialTaylorSum_f
  rw [bTruth_sEx_r181]
  apply le_iSup_of_le base
  rw [bTruth_and_eq]
  apply le_inf
  · apply forces_of_inf_eq_eqname
    exact bTruth_complexNat_weighted v1 zero T (ComplexBits.ofNat 0) 0 p
      (bTerm_zero_checked_r192 v1) (bTerm_current_r181 v base) (ComplexBits.ofNat_cutOn 0 p)
  · apply forces_complexRecursion_graph v1 (up M) T (up W) P
      (fun ps i c d => partialTaylorStep_f ps i c d) m f p V
    · exact (bTerm_up_r181 v base M).trans hM
    · exact bTerm_current_r181 v base
    · exact (bTerm_up_r181 v base W).trans hW
    · exact hP
    · exact taylorPrefixBits_cutOn hz ha
    · intro d w ps i c d0 j hj hps hi hc hd
      have hG' : bTerm w (ps 0) = g := by simpa [V] using hps 0
      have hZ' : bTerm w (ps 1) = z.name := by simpa [V] using hps 1
      exact forces_partialTaylorStep_weighted w ps i c d0 j g (a j) z (f j) (f (j+1)) p
        hG' hZ' hi hc hd rfl (ha j hj) hz
        (taylorPrefixBits_cutOn hz ha j hj.le) (hvalue j hj)

end JSP000930.AnalyticSyntax
