import Mathlib
import PEqualNP.Defs
namespace Three3722
open PEqualNP.TopForm
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def bits (m : Fin 512) (p l : Fin 3) : Bool := m.val.testBit (3*p.val+l.val)
def cross (m : Fin 512) (u v : Fin 6) : Bool :=
  if u.val<3 then if 3≤v.val then m.val.testBit (3*u.val+(v.val-3)) else false
  else if v.val<3 then m.val.testBit (3*v.val+(u.val-3)) else false
def code (B : Fin 3→Fin 3→Bool) : Fin 512 :=
  ⟨((if B 0 0 then 1 else 0)+(if B 0 1 then 2 else 0)+(if B 0 2 then 4 else 0)+(if B 1 0 then 8 else 0)+(if B 1 1 then 16 else 0)+(if B 1 2 then 32 else 0)+(if B 2 0 then 64 else 0)+(if B 2 1 then 128 else 0)+(if B 2 2 then 256 else 0))%512,Nat.mod_lt _ (by decide)⟩
theorem coding : ∀ B : Fin 3→Fin 3→Bool,∀ p l,bits (code B) p l=B p l := by decide +kernel

def data : Array Nat := #[21396,21396,21396,23720,21396,23720,40100,40100,21396,21396,21396,23720,21396,23720,40100,40100,21396,21396,21396,23720,21396,23720,40100,40100,23636,23636,23636,8994,23636,71012,42340,8994,21396,21396,21396,23720,21396,23720,40100,40100,23636,23636,23636,70956,23636,11042,42340,11042,39988,39988,39988,42284,39988,42284,11298,11298,39988,39988,39988,8994,39988,11042,11298,8994,21396,21396,21396,23720,21396,23720,40100,40100,21396,21396,21396,23720,21396,23720,40100,40100,21396,21396,21396,23720,21396,23720,40100,40100,23636,23636,23636,8994,23636,71012,42340,8994,21396,21396,21396,23720,21396,23720,40100,40100,23636,23636,23636,70956,23636,11042,42340,11042,39988,39988,39988,42284,39988,42284,11298,11298,39988,39988,39988,8994,39988,11042,11298,8994,21396,21396,21396,23720,21396,23720,40100,40100,21396,21396,21396,23720,21396,23720,40100,40100,21396,21396,21396,23720,21396,23720,40100,40100,23636,23636,23636,8994,23636,71012,42340,8994,21396,21396,21396,23720,21396,23720,40100,40100,23636,23636,23636,70956,23636,11042,42340,11042,39988,39988,39988,42284,39988,42284,11298,11298,39988,39988,39988,8994,39988,11042,11298,8994,23188,23188,23188,9026,23188,70564,41892,9026,23188,23188,23188,9026,23188,70564,41892,9026,23188,23188,23188,9026,23188,70564,41892,9026,9030,9030,9030,8994,9030,9030,9030,8994,23188,23188,23188,9026,23188,70564,41892,9026,70452,70452,70452,9026,70452,11042,1,11042,41780,41780,41780,9026,41780,1,11298,11298,9030,9030,9030,8994,9030,11042,11298,8994,21396,21396,21396,23720,21396,23720,40100,40100,21396,21396,21396,23720,21396,23720,40100,40100,21396,21396,21396,23720,21396,23720,40100,40100,23636,23636,23636,8994,23636,71012,42340,8994,21396,21396,21396,23720,21396,23720,40100,40100,23636,23636,23636,70956,23636,11042,42340,11042,39988,39988,39988,42284,39988,42284,11298,11298,39988,39988,39988,8994,39988,11042,11298,8994,23188,23188,23188,70060,23188,11074,41892,11074,23188,23188,23188,70060,23188,11074,41892,11074,23188,23188,23188,70060,23188,11074,41892,11074,70004,70004,70004,8994,70004,11074,1,8994,23188,23188,23188,70060,23188,11074,41892,11074,11078,11078,11078,11078,11078,11042,11078,11042,41780,41780,41780,1,41780,11074,11298,11298,11078,11078,11078,8994,11078,11042,11298,8994,39316,39316,39316,41388,39316,41388,11330,11330,39316,39316,39316,41388,39316,41388,11330,11330,39316,39316,39316,41388,39316,41388,11330,11330,41332,41332,41332,8994,41332,1,11330,8994,39316,39316,39316,41388,39316,41388,11330,11330,41332,41332,41332,1,41332,11042,11330,11042,11334,11334,11334,11334,11334,11334,11298,11298,11334,11334,11334,8994,11334,11042,11298,8994,39316,39316,39316,9026,39316,11074,11330,9026,39316,39316,39316,9026,39316,11074,11330,9026,39316,39316,39316,9026,39316,11074,11330,9026,9030,9030,9030,8994,9030,11074,11330,8994,39316,39316,39316,9026,39316,11074,11330,9026,11078,11078,11078,9026,11078,11042,11330,11042,11334,11334,11334,9026,11334,11074,11298,11298,9030,9030,9030,8994,9030,11042,11298,8994]
def packed (m : Fin 512) := data[m.val]!
def entry (m : Fin 512) (i : Nat) := ((packed m / 4) >>> (3*i)) % 8
def rect (m : Fin 512) (i : Nat) : Fin 6 := ⟨entry m i % 6,Nat.mod_lt _ (by decide)⟩
def check (m : Fin 512) : Prop :=
  if packed m % 4=0 then
    ∀ x u v : Fin 6, cross m x u=true → cross m x v=true → u≠v →
      entry m x < entry m u ∨ entry m x < entry m v
  else if packed m % 4=1 then
    ∀ x : Fin 6, (Finset.univ.filter (fun y=>cross m x y)).card=2
  else
    rect m 0≠rect m 1 ∧ rect m 2≠rect m 3 ∧ cross m (rect m 0) (rect m 2)=true ∧
    cross m (rect m 0) (rect m 3)=true ∧ cross m (rect m 1) (rect m 2)=true ∧
    cross m (rect m 1) (rect m 3)=true
instance (m : Fin 512) : Decidable (check m) := by
  unfold check
  split
  · infer_instance
  · split <;> infer_instance
theorem tab0 : ∀ r : Fin 8,check ⟨0+r.val, by omega⟩ := by decide +kernel
theorem tab1 : ∀ r : Fin 8,check ⟨8+r.val, by omega⟩ := by decide +kernel
theorem tab2 : ∀ r : Fin 8,check ⟨16+r.val, by omega⟩ := by decide +kernel
theorem tab3 : ∀ r : Fin 8,check ⟨24+r.val, by omega⟩ := by decide +kernel
theorem tab4 : ∀ r : Fin 8,check ⟨32+r.val, by omega⟩ := by decide +kernel
theorem tab5 : ∀ r : Fin 8,check ⟨40+r.val, by omega⟩ := by decide +kernel
theorem tab6 : ∀ r : Fin 8,check ⟨48+r.val, by omega⟩ := by decide +kernel
theorem tab7 : ∀ r : Fin 8,check ⟨56+r.val, by omega⟩ := by decide +kernel
theorem tab8 : ∀ r : Fin 8,check ⟨64+r.val, by omega⟩ := by decide +kernel
theorem tab9 : ∀ r : Fin 8,check ⟨72+r.val, by omega⟩ := by decide +kernel
theorem tab10 : ∀ r : Fin 8,check ⟨80+r.val, by omega⟩ := by decide +kernel
theorem tab11 : ∀ r : Fin 8,check ⟨88+r.val, by omega⟩ := by decide +kernel
theorem tab12 : ∀ r : Fin 8,check ⟨96+r.val, by omega⟩ := by decide +kernel
theorem tab13 : ∀ r : Fin 8,check ⟨104+r.val, by omega⟩ := by decide +kernel
theorem tab14 : ∀ r : Fin 8,check ⟨112+r.val, by omega⟩ := by decide +kernel
theorem tab15 : ∀ r : Fin 8,check ⟨120+r.val, by omega⟩ := by decide +kernel
theorem tab16 : ∀ r : Fin 8,check ⟨128+r.val, by omega⟩ := by decide +kernel
theorem tab17 : ∀ r : Fin 8,check ⟨136+r.val, by omega⟩ := by decide +kernel
theorem tab18 : ∀ r : Fin 8,check ⟨144+r.val, by omega⟩ := by decide +kernel
theorem tab19 : ∀ r : Fin 8,check ⟨152+r.val, by omega⟩ := by decide +kernel
theorem tab20 : ∀ r : Fin 8,check ⟨160+r.val, by omega⟩ := by decide +kernel
theorem tab21 : ∀ r : Fin 8,check ⟨168+r.val, by omega⟩ := by decide +kernel
theorem tab22 : ∀ r : Fin 8,check ⟨176+r.val, by omega⟩ := by decide +kernel
theorem tab23 : ∀ r : Fin 8,check ⟨184+r.val, by omega⟩ := by decide +kernel
theorem tab24 : ∀ r : Fin 8,check ⟨192+r.val, by omega⟩ := by decide +kernel
theorem tab25 : ∀ r : Fin 8,check ⟨200+r.val, by omega⟩ := by decide +kernel
theorem tab26 : ∀ r : Fin 8,check ⟨208+r.val, by omega⟩ := by decide +kernel
theorem tab27 : ∀ r : Fin 8,check ⟨216+r.val, by omega⟩ := by decide +kernel
theorem tab28 : ∀ r : Fin 8,check ⟨224+r.val, by omega⟩ := by decide +kernel
theorem tab29 : ∀ r : Fin 8,check ⟨232+r.val, by omega⟩ := by decide +kernel
theorem tab30 : ∀ r : Fin 8,check ⟨240+r.val, by omega⟩ := by decide +kernel
theorem tab31 : ∀ r : Fin 8,check ⟨248+r.val, by omega⟩ := by decide +kernel
theorem tab32 : ∀ r : Fin 8,check ⟨256+r.val, by omega⟩ := by decide +kernel
theorem tab33 : ∀ r : Fin 8,check ⟨264+r.val, by omega⟩ := by decide +kernel
theorem tab34 : ∀ r : Fin 8,check ⟨272+r.val, by omega⟩ := by decide +kernel
theorem tab35 : ∀ r : Fin 8,check ⟨280+r.val, by omega⟩ := by decide +kernel
theorem tab36 : ∀ r : Fin 8,check ⟨288+r.val, by omega⟩ := by decide +kernel
theorem tab37 : ∀ r : Fin 8,check ⟨296+r.val, by omega⟩ := by decide +kernel
theorem tab38 : ∀ r : Fin 8,check ⟨304+r.val, by omega⟩ := by decide +kernel
theorem tab39 : ∀ r : Fin 8,check ⟨312+r.val, by omega⟩ := by decide +kernel
theorem tab40 : ∀ r : Fin 8,check ⟨320+r.val, by omega⟩ := by decide +kernel
theorem tab41 : ∀ r : Fin 8,check ⟨328+r.val, by omega⟩ := by decide +kernel
theorem tab42 : ∀ r : Fin 8,check ⟨336+r.val, by omega⟩ := by decide +kernel
theorem tab43 : ∀ r : Fin 8,check ⟨344+r.val, by omega⟩ := by decide +kernel
theorem tab44 : ∀ r : Fin 8,check ⟨352+r.val, by omega⟩ := by decide +kernel
theorem tab45 : ∀ r : Fin 8,check ⟨360+r.val, by omega⟩ := by decide +kernel
theorem tab46 : ∀ r : Fin 8,check ⟨368+r.val, by omega⟩ := by decide +kernel
theorem tab47 : ∀ r : Fin 8,check ⟨376+r.val, by omega⟩ := by decide +kernel
theorem tab48 : ∀ r : Fin 8,check ⟨384+r.val, by omega⟩ := by decide +kernel
theorem tab49 : ∀ r : Fin 8,check ⟨392+r.val, by omega⟩ := by decide +kernel
theorem tab50 : ∀ r : Fin 8,check ⟨400+r.val, by omega⟩ := by decide +kernel
theorem tab51 : ∀ r : Fin 8,check ⟨408+r.val, by omega⟩ := by decide +kernel
theorem tab52 : ∀ r : Fin 8,check ⟨416+r.val, by omega⟩ := by decide +kernel
theorem tab53 : ∀ r : Fin 8,check ⟨424+r.val, by omega⟩ := by decide +kernel
theorem tab54 : ∀ r : Fin 8,check ⟨432+r.val, by omega⟩ := by decide +kernel
theorem tab55 : ∀ r : Fin 8,check ⟨440+r.val, by omega⟩ := by decide +kernel
theorem tab56 : ∀ r : Fin 8,check ⟨448+r.val, by omega⟩ := by decide +kernel
theorem tab57 : ∀ r : Fin 8,check ⟨456+r.val, by omega⟩ := by decide +kernel
theorem tab58 : ∀ r : Fin 8,check ⟨464+r.val, by omega⟩ := by decide +kernel
theorem tab59 : ∀ r : Fin 8,check ⟨472+r.val, by omega⟩ := by decide +kernel
theorem tab60 : ∀ r : Fin 8,check ⟨480+r.val, by omega⟩ := by decide +kernel
theorem tab61 : ∀ r : Fin 8,check ⟨488+r.val, by omega⟩ := by decide +kernel
theorem tab62 : ∀ r : Fin 8,check ⟨496+r.val, by omega⟩ := by decide +kernel
theorem tab63 : ∀ r : Fin 8,check ⟨504+r.val, by omega⟩ := by decide +kernel
theorem checked (m : Fin 512) : check m := by
  let q : Fin 64 := ⟨m.val/8,by omega⟩
  let r : Fin 8 := ⟨m.val%8,by omega⟩
  have group (j : Fin 64) : check ⟨8*j.val+r.val,by have := j.isLt; have := r.isLt; omega⟩ := by
    fin_cases j
    · exact tab0 r
    · exact tab1 r
    · exact tab2 r
    · exact tab3 r
    · exact tab4 r
    · exact tab5 r
    · exact tab6 r
    · exact tab7 r
    · exact tab8 r
    · exact tab9 r
    · exact tab10 r
    · exact tab11 r
    · exact tab12 r
    · exact tab13 r
    · exact tab14 r
    · exact tab15 r
    · exact tab16 r
    · exact tab17 r
    · exact tab18 r
    · exact tab19 r
    · exact tab20 r
    · exact tab21 r
    · exact tab22 r
    · exact tab23 r
    · exact tab24 r
    · exact tab25 r
    · exact tab26 r
    · exact tab27 r
    · exact tab28 r
    · exact tab29 r
    · exact tab30 r
    · exact tab31 r
    · exact tab32 r
    · exact tab33 r
    · exact tab34 r
    · exact tab35 r
    · exact tab36 r
    · exact tab37 r
    · exact tab38 r
    · exact tab39 r
    · exact tab40 r
    · exact tab41 r
    · exact tab42 r
    · exact tab43 r
    · exact tab44 r
    · exact tab45 r
    · exact tab46 r
    · exact tab47 r
    · exact tab48 r
    · exact tab49 r
    · exact tab50 r
    · exact tab51 r
    · exact tab52 r
    · exact tab53 r
    · exact tab54 r
    · exact tab55 r
    · exact tab56 r
    · exact tab57 r
    · exact tab58 r
    · exact tab59 r
    · exact tab60 r
    · exact tab61 r
    · exact tab62 r
    · exact tab63 r
  have eq : (⟨8*q.val+r.val,by have := q.isLt; have := r.isLt; omega⟩ : Fin 512)=m :=
    Fin.ext (by dsimp [q,r];omega)
  exact eq ▸ group q

-- The maximum-support argument is the rank version of L_meta_903.acyc_of_lt.
theorem forestOfRank {n : Nat} (H : SimpleGraph (Fin n)) (rank : Fin n→ℕ)
    (h : ∀ x u v,H.Adj x u → H.Adj x v → u≠v → rank x<rank u ∨ rank x<rank v) : H.IsAcyclic := by
  classical
  intro z w cyc
  obtain ⟨m,hm,mx⟩ := w.support.toFinset.exists_max_image rank ⟨z,by simp⟩
  have hm' : m∈w.support := by simpa using hm
  have c := cyc.rotate hm'
  let q := w.rotate m hm'
  have qa : q.snd∈w.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff w m hm']; exact SimpleGraph.Walk.getVert_mem_support _ _
  have qb : q.penultimate∈w.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff w m hm']; exact SimpleGraph.Walk.getVert_mem_support _ _
  have a := mx _ (by simpa using qa)
  have b := mx _ (by simpa using qb)
  rcases h m _ _ (q.adj_snd c.not_nil) (q.adj_penultimate c.not_nil).symm c.snd_ne_penultimate with g|g
  · exact (not_lt_of_ge a) g
  · exact (not_lt_of_ge b) g

theorem classify (m : Fin 512) (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (eq : ∀u v,G.Adj u v ↔ cross m u v=true) (no4 : NoFourCycle G) :
    G.IsAcyclic ∨ (∀ u, G.degree u=2) := by
  have good := checked m
  unfold check at good
  split at good
  · left
    exact forestOfRank G (fun i=>entry m i) (fun x u v a b=>good x u v ((eq _ _).mp a) ((eq _ _).mp b))
  split at good
  · right
    intro u
    have same : G.neighborFinset u=Finset.univ.filter (fun y=>cross m u y) := by
      ext v
      simpa using eq u v
    rw [SimpleGraph.degree,same]
    exact good u
  · obtain ⟨ab,uv,au,av,bu,bv⟩ := good
    have k := no4 _ _ ab
    have e := Finset.card_le_one.mp k _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(eq _ _).mpr au,(eq _ _).mpr bu⟩)
      _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(eq _ _).mpr av,(eq _ _).mpr bv⟩)
    exact (uv e).elim

theorem incidence (I : Fin 3→Fin 3→Prop) [DecidableRel I] (G : SimpleGraph (Fin 6))
    (edges : ∀ u v : Fin 6,G.Adj u v ↔ ∃ p l : Fin 3, I p l ∧
      ((u=Fin.castAdd 3 p ∧ v=Fin.natAdd 3 l) ∨ (u=Fin.natAdd 3 l ∧ v=Fin.castAdd 3 p))) :
    ∀u v,G.Adj u v ↔ cross (code (fun p l=>decide (I p l))) u v=true := by
  let B := fun p l : Fin 3=>decide (I p l)
  let m := code B
  have hit (p l : Fin 3) : bits m p l=true ↔ I p l := by rw [coding];simp [B]
  have lr (p l : Fin 3) : cross m (Fin.castAdd 3 p) (Fin.natAdd 3 l)=bits m p l := by
    simp [cross,bits,p.isLt]
  have rl (p l : Fin 3) : cross m (Fin.natAdd 3 l) (Fin.castAdd 3 p)=bits m p l := by
    simp [cross,bits,p.isLt]
  intro u v
  constructor
  · intro g
    obtain ⟨p,l,i,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (edges _ _).mp g
    · exact (lr p l).trans ((hit p l).mpr i)
    · exact (rl p l).trans ((hit p l).mpr i)
  · refine Fin.addCases (motive:=fun z : Fin (3+3)=>cross m z v=true → G.Adj z v) (fun p : Fin 3=>?_) (fun l : Fin 3=>?_) u
    · refine Fin.addCases (motive:=fun z : Fin (3+3)=>cross m (Fin.castAdd 3 p) z=true → G.Adj (Fin.castAdd 3 p) z) (fun q : Fin 3=>?_) (fun l : Fin 3=>?_) v
      · intro wrong
        simp [cross,p.isLt] at wrong
        exact (Nat.not_le_of_gt q.isLt wrong.1).elim
      · intro ok
        exact (edges _ _).mpr ⟨p,l,(hit p l).mp ((lr p l).symm.trans ok),Or.inl ⟨rfl,rfl⟩⟩
    · refine Fin.addCases (motive:=fun z : Fin (3+3)=>cross m (Fin.natAdd 3 l) z=true → G.Adj (Fin.natAdd 3 l) z) (fun p : Fin 3=>?_) (fun k : Fin 3=>?_) v
      · intro ok
        exact (edges _ _).mpr ⟨p,l,(hit p l).mp ((rl p l).symm.trans ok),Or.inr ⟨rfl,rfl⟩⟩
      · intro wrong; simp [cross] at wrong

end Three3722
