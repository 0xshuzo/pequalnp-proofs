import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9740.Aligned
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def step (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs++[g]) w=step (run gs w) g := by simp [run,List.foldl_append]
theorem length_run (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [step,ih]; omega
theorem snoc_other (w : List Bool) (v : Bool) (q : Nat) (ne : q≠w.length) :
    (w++[v]).getD q false=w.getD q false := by
  by_cases h : q<w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
theorem snoc_last (w : List Bool) (v : Bool) : (w++[v]).getD w.length false=v := by simp

def separates {k : Nat} (X Y : Fin k→List Bool) (T : Finset Nat) :=
  ∀ i,∃ t∈T,(X i).getD t false≠(Y i).getD t false

def useful (g : Gate) : List Nat :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def charge : GateOp → Nat
  | .not => 0
  | _ => 1

def mass (gs : List Gate) := (gs.map fun g => charge g.op).sum
def inverters (gs : List Gate) := (gs.map fun g => 1-charge g.op).sum

theorem mass_split (gs : List Gate) : mass gs + inverters gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have cap : charge g.op≤1 := by cases g.op <;> simp [charge]
    change charge g.op+mass gs+(1-charge g.op+inverters gs)=gs.length+1
    omega

theorem mass_snoc (gs : List Gate) (g : Gate) : mass (gs++[g])=mass gs+charge g.op := by
  simp [mass,List.sum_append]

theorem use_sound (g : Gate) (v : Nat→Bool) :
    g.op.eval (g.inputs.map v)=g.op.eval ((useful g).map v) := by
  rcases g with ⟨op,args⟩
  cases op <;> cases args <;> rfl

theorem use_count (g : Gate) (h : g.inputs.length≤2) : (useful g).length ≤ charge g.op+1 := by
  rcases g with ⟨op,args⟩
  cases op <;> simp_all [useful,charge]

theorem trace (k m : Nat) (X Y : Fin k→List Bool)
    (lens : ∀ i,(X i).length=m ∧ (Y i).length=m)
    (gs : List Gate) (fan : ∀ g∈gs,g.inputs.length≤2)
    (S : Finset Nat) (sep : separates (fun i=>run gs (X i)) (fun i=>run gs (Y i)) S) :
    ∃ T : Finset Nat,separates X Y T ∧ T.card≤S.card+mass gs := by
  classical
  induction gs using List.reverseRecOn generalizing S with
  | nil => exact ⟨S,sep,by simp [mass]⟩
  | append_singleton gs g ih =>
    let last := m+gs.length
    let V := fun i => run gs (X i)
    let W := fun i => run gs (Y i)
    have vl (i) : (V i).length=last := by rw [show V i=run gs (X i) by rfl,length_run,(lens i).1]
    have wl (i) : (W i).length=last := by rw [show W i=run gs (Y i) by rfl,length_run,(lens i).2]
    have stay (i : Fin k) (w : Nat) (ne : w≠last) :
        (run (gs++[g]) (X i)).getD w false ≠ (run (gs++[g]) (Y i)).getD w false →
          (V i).getD w false ≠ (W i).getD w false := by
      rw [run_snoc,run_snoc]
      change (V i++[_]).getD w false≠(W i++[_]).getD w false → _
      rw [snoc_other _ _ w (by rwa [vl]),snoc_other _ _ w (by rwa [wl])]
      exact id
    have old : ∀ a∈gs,a.inputs.length≤2 := fun a ha => fan a (by simp [ha])
    by_cases mem : last∈S
    · let R := S.erase last ∪ (useful g).toFinset
      have rsep : separates V W R := by
        intro i
        obtain ⟨w,ws,diff⟩ := sep i
        by_cases eq : w=last
        · subst w
          by_contra! blocked
          have same : (useful g).map (fun t => (V i).getD t false)=(useful g).map (fun t => (W i).getD t false) := by
            apply List.map_congr_left
            intro t ht
            exact blocked t (Finset.mem_union_right _ (List.mem_toFinset.mpr ht))
          change (run (gs++[g]) (X i)).getD last false≠(run (gs++[g]) (Y i)).getD last false at diff
          rw [run_snoc,run_snoc] at diff
          change (V i++[g.op.eval _]).getD last false≠(W i++[g.op.eval _]).getD last false at diff
          rw [←vl i,snoc_last,vl i,←wl i,snoc_last] at diff
          exact diff ((use_sound g _).trans ((congrArg g.op.eval same).trans (use_sound g _).symm))
        · exact ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ws⟩),stay i w eq diff⟩
      obtain ⟨T,st,card⟩ := ih old R rsep
      have maxfan := fan g (by simp)
      have usable := use_count g maxfan
      have len := List.toFinset_card_le (useful g)
      have union : R.card≤(S.erase last).card+(useful g).toFinset.card := Finset.card_union_le _ _
      have erase := Finset.card_erase_add_one mem
      exact ⟨T,st,by rw [mass_snoc]; omega⟩
    · have oldSep : separates V W S := by
        intro i
        obtain ⟨w,ws,h⟩ := sep i
        exact ⟨w,ws,stay i w (fun eq => mem (eq ▸ ws)) h⟩
      obtain ⟨T,st,card⟩ := ih old S oldSep
      exact ⟨T,st,by rw [mass_snoc]; omega⟩

theorem manyPrice {k m t : Nat} (X Y : Fin k → List Bool)
    (lens : ∀ i,(X i).length=m ∧ (Y i).length=m)
    (single : ∀ (w : Nat) (i j : Fin k),(X i).getD w false≠(Y i).getD w false →
      (X j).getD w false≠(Y j).getD w false → i=j)
    (gs : List Gate) (fan : ∀ g∈gs,g.inputs.length≤2) (port : Fin t → Nat)
    (detect : ∀ i, ∃ j,(run gs (X i)).getD (port j) false≠(run gs (Y i)).getD (port j) false) :
    k≤gs.length+t := by
  classical
  let S := Finset.univ.image port
  obtain ⟨T,sep,bound⟩ := trace k m X Y lens gs fan S (by
    intro i
    obtain ⟨j,hit⟩ := detect i
    exact ⟨port j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,hit⟩)
  let f := fun i => Classical.choose (sep i)
  have ok (i) := Classical.choose_spec (sep i)
  have cap : (Finset.univ : Finset (Fin k)).card≤T.card :=
    Finset.card_le_card_of_injOn f (fun i _ => (ok i).1) (fun i _ j _ eq =>
      single (f j) i j (eq ▸ (ok i).2) (ok j).2)
  have small := Finset.card_image_le (s:=Finset.univ) (f:=port)
  change T.card≤(Finset.univ.image port).card+mass gs at bound
  simp only [Finset.card_univ,Fintype.card_fin] at cap small
  have eq := mass_split gs
  omega

def tapped {t : Nat} (gs : List Gate) (port : Fin t → Nat) (bank : List Bool) :
    Fin t → Bool := fun j => (run gs bank).getD (port j) false


abbrev L := Fin 20
abbrev P := Fin 20
abbrev I := Fin 5
abbrev Assignment := Option I
abbrev Z (t : Nat) := Fin t → Bool

def spot : I → L := ![0,4,6,16,19]
def adj (p : P) (l : L) : Bool := (([131233, 262466, 524934, 1293, 2584, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 274945, 549888, 51203, 102404, 204810, 409620, 819240] : List Nat).getD p.val 0).testBit l.val
theorem one_intersection : ∀ (p : P) (i j : I),
    adj p (spot i)=true → adj p (spot j)=true → i=j := by decide +kernel

noncomputable section
open Classical
structure Sites (t : Nat) where
  top : Fin t → Prop
  sel : L → Fin t → Prop
  coeff : L → Fin t → Prop
  support : ∀ j,∃ p,∀ l,coeff l j → adj p l=true

def host {t} (S : Sites t) (r : Assignment) (z : Z t) : Prop :=
  (∃ j,S.top j ∧ z j=true) ∨ ∃ l : L,
    ((∃ i, r=some i ∧ spot i=l) ∨ ∃ j,S.sel l j ∧ z j=true) ∧
      ∃ j,S.coeff l j ∧ z j=true

-- An enabled coefficient tap can cover only one of the marked rows.
theorem owner {t} (S : Sites t) (z : Z t) (neg : ¬host S none z)
    {i : I} (hit : host S (some i) z) :
    ∃ j,z j=true ∧ S.coeff (spot i) j := by
  rcases hit with h|⟨l,(raw|sel),j,hj,on⟩
  · exact False.elim (neg (Or.inl h))
  · obtain ⟨k,hk,rfl⟩ := raw
    have eq : i=k := Option.some.inj hk
    subst k
    exact ⟨j,on,hj⟩
  · exact False.elim (neg (Or.inr ⟨l,Or.inr sel,j,hj,on⟩))

-- A frozen bank port either changes on at most one marked raw line, or its
-- truth implies host truth (a star-product output or its downstream OR).
theorem alignedFive {m t} (S : Sites t) (gs : List Gate)
    (fan : ∀ g∈gs,g.inputs.length≤2) (port : Fin t → Nat)
    (bank : Assignment → Z t → List Bool) (len : ∀ r z,(bank r z).length=m)
    (views : ∀ w z, (∃ h : I,∀ i,(bank none z).getD w false≠(bank (some i) z).getD w false → i=h) ∨
      (∀ r,(bank r z).getD w false=true → host S r z))
    (mono : ∀ z i j, tapped gs port (bank none z) j=true →
      tapped gs port (bank (some i) z) j=true)
    (baseline : ∃ z,tapped gs port (bank none z)=z ∧ ¬host S none z)
    (correct : ∀ i z,tapped gs port (bank (some i) z)=z → host S (some i) z) :
    5≤gs.length+t := by
  classical
  obtain ⟨z,base,neg⟩ := baseline
  let B : Finset I := Finset.univ.filter (fun i => host S (some i) z)
  let A : Finset (Fin t) := Finset.univ.filter (fun j => z j=true)
  have hb {i : I} : i∈B ↔ host S (some i) z := by simp [B]
  have ha {j : Fin t} : j∈A ↔ z j=true := by simp [A]
  have owners (i : ↥B) := owner S z neg (hb.mp i.property)
  let ow : ↥B → Fin t := fun i => Classical.choose (owners i)
  have fact (i : ↥B) : z (ow i)=true ∧ S.coeff (spot i.val) (ow i) := Classical.choose_spec (owners i)
  let f : ↥B → ↥A := fun i => ⟨ow i,ha.mpr (fact i).1⟩
  have injective : Function.Injective f := by
    intro i j eq
    have same : ow i=ow j := congrArg Subtype.val eq
    obtain ⟨p,tr⟩ := S.support (ow j)
    apply Subtype.ext
    exact one_intersection p i j (tr _ (same ▸ (fact i).2)) (tr _ (fact j).2)
  have card : B.card≤A.card := by simpa using Fintype.card_le_of_injective f injective
  let U : Finset I := Bᶜ
  let V : Finset (Fin t) := Aᶜ
  let eu := Fintype.equivFin ↥U
  let ev := Fintype.equivFin ↥V
  let pts := fun i => (eu.symm i).val
  have empty (i) : ¬host S (some (pts i)) z := by
    intro h
    have q : (eu.symm i).val∈B := hb.mpr h
    exact (Finset.mem_compl.mp (eu.symm i).property) q
  let X := fun (_ : Fin (Fintype.card ↥U)) => bank none z
  let Y := fun i => bank (some (pts i)) z
  let pr := fun j => port (ev.symm j).val
  have priced := manyPrice (m:=m) X Y (fun i => ⟨len _ _,len _ _⟩) (show
    ∀ (w : Nat) i j,(X i).getD w false≠(Y i).getD w false →
      (X j).getD w false≠(Y j).getD w false → i=j from by
    intro w i j di dj
    rcases views w z with ⟨h,only⟩ | top
    · apply eu.symm.injective
      apply Subtype.ext
      exact (only (pts i) di).trans (only (pts j) dj).symm
    · have at0 : (bank none z).getD w false=false := by
        cases h : (bank none z).getD w false
        · rfl
        · exact False.elim (neg (top none h))
      have atI : (bank (some (pts i)) z).getD w false=false := by
        cases h : (bank (some (pts i)) z).getD w false
        · rfl
        · exact False.elim (empty i (top (some (pts i)) h))
      exact False.elim (di (at0.trans atI.symm))) gs fan pr (show
    ∀ i,∃ j,(run gs (X i)).getD (pr j) false≠(run gs (Y i)).getD (pr j) false from by
    intro i
    have diff : tapped gs port (Y i) ≠ z := fun h => empty i (correct (pts i) z h)
    have ne : ∃ j,tapped gs port (Y i) j ≠ z j := by
      by_contra! hh
      exact diff (funext hh)
    obtain ⟨j,hj⟩ := ne
    have zero : z j≠true := by
      intro on
      have old : tapped gs port (bank none z) j=true := by rw [base,on]
      exact hj ((mono z (pts i) j old).trans on.symm)
    have mem : j∈V := Finset.mem_compl.mpr (fun h => zero (ha.mp h))
    refine ⟨ev ⟨j,mem⟩,?_⟩
    simp only [pr,Equiv.symm_apply_apply]
    change tapped gs port (bank none z) j ≠ tapped gs port (Y i) j
    rw [base]
    exact Ne.symm hj)
  simp only [U,V,Fintype.card_coe,Finset.card_compl,Fintype.card_fin] at priced
  have bcap : B.card≤5 := by simpa using (Finset.card_le_univ B)
  have acap : A.card≤t := by simpa using (Finset.card_le_univ A)
  omega
end
end PEqualNP.Outside.L_meta_9740.Aligned
