import PEqualNP.Outside.L_meta_2069
namespace BadOrbit5206
open PEqualNP.Outside.L_meta_2069
abbrev V := Fin 26
def move : Fin 6 → V → V := ![![0,1,2,9,10,6,5,11,8,3,4,7,12,13,14,19,22,23,18,15,21,20,16,17,24,25],![0,1,2,9,4,7,11,5,12,3,10,6,8,13,14,19,21,17,24,15,22,16,20,23,18,25],![0,1,4,3,10,6,8,11,5,9,2,12,7,13,14,16,20,23,18,21,15,22,19,25,24,17],![0,1,5,3,8,2,10,12,4,9,6,11,7,13,18,15,20,25,14,22,16,21,19,23,24,17],![0,3,2,1,5,4,6,7,12,9,11,10,8,13,15,14,18,17,16,19,24,22,21,23,20,25],![13,25,24,23,22,21,20,19,18,17,16,15,14,0,12,11,10,9,8,7,6,5,4,3,2,1]]
def rep (u v : V) : Bool := (u==0 && v==0) || (u==0 && v==1) || (u==0 && v==2) || (u==0 && v==14) || (u==1 && v==1) || (u==1 && v==2) || (u==1 && v==3) || (u==1 && v==15) || (u==1 && v==17) || (u==2 && v==2) || (u==2 && v==4) || (u==2 && v==8) || (u==2 && v==16)
def dist : V → V → Nat := ![![0,0,0,1,2,1,2,2,2,2,1,2,3,0,0,1,2,0,1,2,2,3,3,0,2,0],![0,0,0,0,2,1,2,2,2,1,1,3,3,0,0,0,2,0,0,1,1,2,2,1,0,1],![0,0,0,1,0,1,2,2,0,2,1,2,1,3,0,0,0,4,1,0,2,1,1,3,2,0],![1,0,1,1,2,2,3,3,3,2,2,2,3,0,1,0,0,1,2,2,0,3,3,2,2,2],![2,2,0,2,2,1,3,2,3,3,2,4,2,3,0,3,0,0,3,2,2,0,3,3,2,3],![1,1,1,2,1,1,2,2,1,3,3,3,3,3,2,0,3,0,0,2,1,2,0,3,2,3],![2,2,2,3,3,2,2,4,2,3,1,2,3,3,3,2,0,3,0,0,3,2,3,0,2,2],![2,2,2,3,2,2,4,2,3,3,3,3,2,2,3,3,3,0,3,0,0,3,2,2,0,2],![2,2,0,3,3,1,2,3,2,4,2,4,3,2,3,4,2,4,0,3,0,0,3,3,2,0],![2,1,2,2,3,3,3,3,4,2,3,4,4,0,2,3,4,2,3,0,4,0,0,2,3,1],![1,1,1,2,2,3,1,3,2,3,1,2,3,3,0,1,3,3,2,2,0,2,0,0,1,2],![2,3,2,2,4,3,2,3,4,4,2,2,3,2,2,0,2,2,3,3,2,0,3,0,0,1],![3,3,1,3,2,3,3,2,3,4,3,3,3,1,4,3,0,3,3,3,3,3,0,2,0,0],![0,0,3,0,3,3,3,2,2,0,3,2,1,1,3,3,2,2,2,3,2,2,3,2,1,1],![0,0,0,1,0,2,3,3,3,2,0,2,4,3,3,4,3,3,3,3,4,3,3,4,2,4],![1,0,0,0,3,0,2,3,4,3,1,0,3,3,4,3,3,4,3,4,3,4,4,3,3,4],![2,2,0,0,0,3,0,3,2,4,3,2,0,2,3,3,2,3,3,3,2,3,3,3,2,2],![0,0,4,1,0,0,3,0,4,2,3,2,3,2,3,4,3,2,3,4,3,3,4,2,2,2],![1,0,1,2,3,0,0,3,0,3,2,3,3,2,3,3,3,3,2,3,2,2,4,3,1,2],![2,1,0,2,2,2,0,0,3,0,2,3,3,3,3,4,3,4,3,3,3,3,3,3,2,3],![2,1,2,0,2,1,3,0,0,4,0,2,3,2,4,3,2,3,2,3,2,2,3,3,3,2],![3,2,1,3,0,2,2,3,0,0,2,0,3,2,3,4,3,3,2,3,2,2,2,3,2,2],![3,2,1,3,3,0,3,2,3,0,0,3,0,3,3,4,3,4,4,3,3,2,3,3,1,3],![0,1,3,2,3,3,0,2,3,2,0,0,2,2,4,3,3,2,3,3,3,3,3,2,2,1],![2,0,2,2,2,2,2,0,2,3,1,0,0,1,2,3,2,2,1,2,3,2,1,2,1,1],![0,1,0,2,3,3,2,2,0,1,2,1,0,1,4,4,2,2,2,3,2,2,3,1,1,1]]

set_option maxHeartbeats 4000000
def Autom (f : V → V) : Prop :=
  Function.Injective f ∧
  (((f 0=0) ∧ (f 13=13)) ∨ ((f 0=13) ∧ (f 13=0))) ∧
  ∀ u v, adjb (f u) (f v) = adjb u v
lemma idAuto : Autom id := ⟨Function.injective_id,Or.inl ⟨rfl,rfl⟩,fun _ _ => rfl⟩
lemma compose {f g : V → V} (hf : Autom f) (hg : Autom g) : Autom (g ∘ f) := by
  refine ⟨hg.1.comp hf.1,?_,fun u v => (hg.2.2 (f u) (f v)).trans (hf.2.2 u v)⟩
  rcases hf.2.1 with ⟨ha,hb⟩|⟨ha,hb⟩ <;> rcases hg.2.1 with ⟨hc,hd⟩|⟨hc,hd⟩ <;>
    simp [Function.comp_apply,ha,hb,hc,hd]
lemma good (g : Fin 6) : Autom (move g) := by
  revert g
  unfold Autom Function.Injective
  decide +kernel
lemma next : ∀ u v : V, u≤v → adjb u v=false → rep u v=true ∨
  ∃ g, dist (min (move g u) (move g v)) (max (move g u) (move g v)) < dist u v := by decide +kernel

theorem representatives (a b : V) (nonedge : adjb a b=false) :
    ∃ f : V → V, Autom f ∧ rep (min (f a) (f b)) (max (f a) (f b))=true := by
  suffices sorted : ∀ (n : Nat) (u v : V), dist u v=n → u≤v → adjb u v=false →
      ∃ f : V → V, Autom f ∧ rep (min (f u) (f v)) (max (f u) (f v))=true by
    rcases le_total a b with h|h
    · exact sorted _ a b rfl h nonedge
    · obtain ⟨f,hf,hr⟩ := sorted _ b a rfl h ((adj_symm b a).trans nonedge)
      exact ⟨f,hf,by simpa [min_comm,max_comm] using hr⟩
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro u v e h non
    rcases next u v h non with done|⟨g,lt⟩
    · exact ⟨id,idAuto,by simpa [min_eq_left h,max_eq_right h] using done⟩
    · let c := move g u
      let d := move g v
      have gh := good g
      have cd : adjb c d = false := (gh.2.2 u v).trans non
      have old := (show min c d ≤ max c d from (min_le_left _ _).trans (le_max_left _ _))
      have neg : adjb (min c d) (max c d)=false := by
        rcases le_total c d with h|h
        · simpa [min_eq_left h,max_eq_right h] using cd
        · simpa [min_eq_right h,max_eq_left h] using (adj_symm d c).trans cd
      obtain ⟨f,hf,hr⟩ := ih _ (lt.trans_le e.le) (min c d) (max c d) rfl old neg
      refine ⟨f ∘ move g,compose gh hf,?_⟩
      change rep (min (f c) (f d)) (max (f c) (f d))=true
      rcases le_total c d with h|h
      · simpa [min_eq_left h,max_eq_right h] using hr
      · simpa [min_eq_right h,max_eq_left h,min_comm,max_comm] using hr
end BadOrbit5206
