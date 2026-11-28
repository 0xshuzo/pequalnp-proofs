import PEqualNP.Defs
namespace Arms17852
abbrev V := Fin 11
abbrev E := Fin 16
abbrev F := Finset V
def row (m:Nat) : F := Finset.univ.filter (fun i=>m.testBit i.val)
def edges : List Nat := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
def negs : List Nat := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
def er (i:E) := row (edges.getD i.val 0)
def nr (i:Fin 24) := row (negs.getD i.val 0)
def fire (s t x:F) : Prop := (x∩s).Nonempty ∧ (x∩t).Nonempty
instance (s t x:F) : Decidable (fire s t x) := inferInstanceAs (Decidable (_ ∧ _))
def guards (s t:F) := Finset.univ.filter (fun w:V => ∀ i:Fin 24,w∈nr i→¬fire s t (nr i))
def box (sl sh tl th:F) := Finset.univ.filter (fun e:E=>fire sh th (er e) ∧ ((er e)∩guards sl tl).Nonempty)
def hits (s t:F) := box s s t t
lemma fire_up {s s' t t' x:F} (hs:s⊆s') (ht:t⊆t') (h:fire s t x) : fire s' t' x := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := h
  obtain ⟨ax,as⟩ := Finset.mem_inter.mp ha
  obtain ⟨bx,bt⟩ := Finset.mem_inter.mp hb
  exact ⟨⟨a,Finset.mem_inter.mpr ⟨ax,hs as⟩⟩,⟨b,Finset.mem_inter.mpr ⟨bx,ht bt⟩⟩⟩
lemma bound {s t sl sh tl th:F} (l:sl⊆s) (h:s⊆sh) (l':tl⊆t) (h':t⊆th) :
    hits s t ⊆ box sl sh tl th := by
  intro e he
  obtain ⟨pos,⟨w,hw⟩⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨we,wg⟩ := Finset.mem_inter.mp hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fire_up h h' pos, w, Finset.mem_inter.mpr ⟨we,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i wi on=>(Finset.mem_filter.mp wg).2 i wi (fire_up l l' on)⟩⟩⟩
def listed : List (Nat × Nat) := [(85,1040),(85,1088),(85,1160),(85,1282),(272,562),(272,1282),(288,562),(288,772),(289,562),(289,768),(385,562),(385,768),(416,562),(416,768),(417,530),(417,544),(417,546),(417,560),(417,562),(417,584),(417,640),(417,768),(417,772),(530,417),(530,768),(544,417),(544,772),(546,417),(546,768),(560,417),(560,768),(562,272),(562,288),(562,289),(562,385),(562,416),(562,417),(562,768),(562,772),(562,1282),(584,417),(584,640),(640,417),(640,584),(768,289),(768,385),(768,416),(768,417),(768,530),(768,546),(768,560),(768,562),(772,288),(772,417),(772,544),(772,562),(1040,85),(1040,1282),(1088,85),(1088,1160),(1160,85),(1160,1088),(1282,85),(1282,272),(1282,562),(1282,1040)]
def packs : List Nat := [21,50,161,289,385,416,417,530,546,560,562,584,772,1160,1282]

def member (s t:F) : Prop := ∃p∈listed,row p.1=s ∧ row p.2=t
instance (s t:F) : Decidable (member s t) := by unfold member; infer_instance
inductive T where
 | leaf
 | left (v:V) (no yes:T)
 | right (v:V) (no yes:T)
def ck (tr:T) (sl sh tl th:F) : Bool := match tr with
 | .leaf => decide ((box sl sh tl th).card≤5 ∨ (sl=sh ∧ tl=th ∧ member sl tl))
 | .left v no yes => ck no sl (sh.erase v) tl th && ck yes (insert v sl) sh tl th
 | .right v no yes => ck no sl sh tl (th.erase v) && ck yes sl sh (insert v tl) th
theorem sound (tree:T) (s t:F) : ∀sl sh tl th, sl⊆s → s⊆sh → tl⊆t → t⊆th →
    ck tree sl sh tl th=true → (hits s t).card≤5 ∨ member s t := by
 induction tree with
 | leaf =>
   intro sl sh tl th ls hs lt ht hc
   rcases of_decide_eq_true hc with low|⟨a,b,mem⟩
   · exact Or.inl ((Finset.card_le_card (bound ls hs lt ht)).trans low)
   · have one:s=sl := Finset.Subset.antisymm (a.symm ▸ hs) ls
     have two:t=tl := Finset.Subset.antisymm (b.symm ▸ ht) lt
     exact Or.inr (one.symm ▸ two.symm ▸ mem)
 | left v no yes hn hy =>
   intro sl sh tl th ls hs lt ht hc
   obtain ⟨n,y⟩ := Bool.and_eq_true_iff.mp hc
   by_cases hv:v∈s
   · exact hy _ _ _ _ (Finset.insert_subset hv ls) hs lt ht y
   · exact hn _ _ _ _ ls (by intro i hi; exact Finset.mem_erase.mpr ⟨fun e=>hv (e ▸ hi),hs hi⟩) lt ht n
 | right v no yes hn hy =>
   intro sl sh tl th ls hs lt ht hc
   obtain ⟨n,y⟩ := Bool.and_eq_true_iff.mp hc
   by_cases hv:v∈t
   · exact hy _ _ _ _ ls hs (Finset.insert_subset hv lt) ht y
   · exact hn _ _ _ _ ls hs lt (by intro i hi; exact Finset.mem_erase.mpr ⟨fun e=>hv (e ▸ hi),ht hi⟩) n

def node9 := T.leaf
set_option maxHeartbeats 3000000 in
private theorem node9OK : ck node9 (row 0) (row 200) (row 0) (row 2047) = true := by decide +kernel
def node15 := (T.right 5 (T.right 9 (T.right 7 T.leaf (T.left 7 T.leaf T.leaf)) T.leaf) (T.right 9 (T.left 6 (T.left 7 T.leaf (T.right 7 T.leaf T.leaf)) (T.left 7 (T.left 3 T.leaf T.leaf) T.leaf)) (T.left 7 T.leaf T.leaf)))
set_option maxHeartbeats 3000000 in
private theorem node15OK : ck node15 (row 4) (row 204) (row 0) (row 1768) = true := by decide +kernel
def node16 := T.leaf
set_option maxHeartbeats 3000000 in
private theorem node16OK : ck node16 (row 4) (row 204) (row 256) (row 2024) = true := by decide +kernel
def node17 := T.leaf
set_option maxHeartbeats 3000000 in
private theorem node17OK : ck node17 (row 4) (row 204) (row 16) (row 2040) = true := by decide +kernel
def node18 := T.leaf
set_option maxHeartbeats 3000000 in
private theorem node18OK : ck node18 (row 4) (row 204) (row 1) (row 2041) = true := by decide +kernel
def node19 := T.leaf
set_option maxHeartbeats 3000000 in
private theorem node19OK : ck node19 (row 4) (row 204) (row 4) (row 2045) = true := by decide +kernel
def node20 := T.leaf
set_option maxHeartbeats 3000000 in
private theorem node20OK : ck node20 (row 4) (row 204) (row 2) (row 2047) = true := by decide +kernel
def node26 := (T.left 7 T.leaf (T.right 5 (T.right 4 T.leaf (T.right 3 (T.right 7 T.leaf T.leaf) T.leaf)) T.leaf))
set_option maxHeartbeats 3000000 in
private theorem node26OK : ck node26 (row 1024) (row 1224) (row 0) (row 1016) = true := by decide +kernel

end Arms17852
