import PEqualNP.Defs
namespace N9134
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


abbrev Vec (N : ℕ) := Fin N → Bool
abbrev Board (N : ℕ) := Vec N × Vec N
abbrev Bank (N : ℕ) := ℕ → Set (Board N)
abbrev n (N : ℕ) := N+N
def lo (N w : ℕ) := if w<N then w else if w<n N then n N else w+1
def hi (N s w : ℕ) := if w<n N then w else w+1+s
def count (s : ℕ) := 1+s+s
def clean (N s w : ℕ) := w<N ∨ n N≤w ∧ w≤n N+s
def inM (s : ℕ) (M : Finset ℕ) := ((M.filter (·<s)).image (fun j => 1+s+j))
def pointRow {N : ℕ} (z : Board N) : Board N := (z.1,fun _ => false)
def one {N : ℕ} (p : Fin N) : Vec N := fun r => decide (r=p)
def Inputs {N} (W : Bank N) := ∀ i : Fin N,
  W i.val = {z | z.1 i=true} ∧ W (N+i.val)={z | z.2 i=true}
def MarkSteps {N : ℕ} (W : Bank N) (s : ℕ) (M : Finset ℕ) := ∀ j<s,
  ∃ a<n N+j, ∃ b<n N+j, W (n N+j)∈[W a∪W b,W a,∅] ∨ W (n N+j)=W a∩W b ∧
    (j∈M ∨ ∃ T U : Set (Vec N), W a=T ×ˢ Set.univ ∧ W b=Set.univ ×ˢ U)
def liftBank {N : ℕ} (W : Bank N) (s i : ℕ) : Set (Board N) :=
  if i<n N then W i else if i=n N then ∅ else if i≤n N+s then pointRow ⁻¹' W (i-1)
  else W (i-(1+s))

lemma loeq {N s : ℕ} (W : Bank N) (raw : Inputs W) (w : ℕ) (hw : w<n N+s) :
    liftBank W s (lo N w) = pointRow ⁻¹' W w := by
  by_cases p : w<N
  · have h : w<n N := by dsimp [n]; omega
    let i : Fin N := ⟨w,p⟩
    rw [lo,if_pos p,liftBank,if_pos h,show W w={z | z.1 i=true} from (raw i).1]
    rfl
  by_cases l : w<n N
  · let i : Fin N := ⟨w-N,by dsimp [n] at l; omega⟩
    have e : N+i.val=w := by dsimp [i]; omega
    have rawW : W w={z | z.2 i=true} := e ▸ (raw i).2
    rw [lo,if_neg p,if_pos l,liftBank,if_neg (by omega),if_pos rfl,rawW]
    ext z
    simp [pointRow]
  · have a : ¬w+1<n N := by omega
    have b : w+1≠n N := by omega
    have c : w+1≤n N+s := by omega
    simp [lo,p,l,liftBank,a,b,c]

lemma hieq {N s : ℕ} (W : Bank N) (w : ℕ) : liftBank W s (hi N s w)=W w := by
  by_cases lt : w<n N
  · simp [hi,lt,liftBank]
  · have a : ¬w+1+s<n N := by omega
    have b : w+1+s≠n N := by omega
    have c : ¬w+1+s≤n N+s := by omega
    simp [hi,lt,liftBank,a,b,c,Nat.add_assoc]

lemma low_clean {N s w : ℕ} (h : w<n N+s) : clean N s (lo N w) := by
  unfold lo clean
  split_ifs <;> omega
lemma lo_prior {N j w : ℕ} (h : w<n N+j) : lo N w<n N+(1+j) := by
  unfold lo
  split_ifs <;> omega
lemma hi_prior {N s j w : ℕ} (h : w<n N+j) : hi N s w<n N+(1+s+j) := by
  unfold hi
  split_ifs <;> omega

inductive Node
  | sup (a b : ℕ)
  | copy (a : ℕ)
  | zero
  | both (a b : ℕ)
def Node.gate : Node → Gate
  | .sup a b => ⟨.or,[a,b]⟩
  | .copy a => ⟨.or,[a]⟩
  | .zero => ⟨.or,[]⟩
  | .both a b => ⟨.and,[a,b]⟩
def Node.den {N} (W : Bank N) : Node → Set (Board N)
  | .sup a b => W a∪W b
  | .copy a => W a
  | .zero => ∅
  | .both a b => W a∩W b

def Good {N : ℕ} (W : Bank N) (s : ℕ) (M : Finset ℕ) (k : ℕ) (t : Node) :=
  liftBank W s (n N+k) = t.den (liftBank W s) ∧
  (∀ r∈t.gate.inputs, r<n N+k) ∧
  (clean N s (n N+k) → ∀ r∈t.gate.inputs, clean N s r) ∧
  (t.gate.op=.and → k∈inM s M ∨ ∃ r∈t.gate.inputs, clean N s r)

theorem pick {N s : ℕ} (W : Bank N) (M : Finset ℕ) (raw : Inputs W) (steps : MarkSteps W s M) :
    ∀ k<count s, ∃ t : Node, Good W s M k t := by
  intro k hk
  by_cases nk : k=0
  · subst k
    exact ⟨.zero,by simp [Good,liftBank,Node.den,Node.gate]⟩
  by_cases ck : k≤s
  · let j := k-1
    have dj : 1+j=k := by dsimp [j]; omega
    have js : j<s := by omega
    obtain ⟨a,ha,b,hb,eq|⟨eq,-⟩⟩ := steps j js
    all_goals
      have av := lo_prior ha
      have bv := lo_prior hb
      rw [dj] at av bv
      have ac := low_clean (s:=s) (w:=a) (by omega : a<n N+s)
      have bc := low_clean (s:=s) (w:=b) (by omega : b<n N+s)
      have al := loeq W raw a (by omega : a<n N+s)
      have bl := loeq W raw b (by omega : b<n N+s)
      have ev : liftBank W s (n N+k)= pointRow ⁻¹' W (n N+j) := by
        have h1 : ¬n N+k<n N := by omega
        have h2 : n N+k≠n N := by omega
        have h3 : n N+k≤n N+s := by omega
        have h4 : n N+k-1=n N+j := by omega
        simp [liftBank,h1,h2,h3,h4]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at eq
      rcases eq with eq|eq|eq
      · exact ⟨.sup (lo N a) (lo N b),by simp [Good,ev,eq,Node.den,Node.gate,al,bl,av,bv,ac,bc]⟩
      · exact ⟨.copy (lo N a),by simp [Good,ev,eq,Node.den,Node.gate,al,av,ac]⟩
      · exact ⟨.zero,by simp [Good,ev,eq,Node.den,Node.gate]⟩
    · exact ⟨.both (lo N a) (lo N b),by simp [Good,ev,eq,Node.den,Node.gate,al,bl,av,bv,ac,bc]⟩
  · let j := k-(1+s)
    have dj : 1+s+j=k := by dsimp [j]; omega
    have js : j<s := by dsimp [count] at hk; omega
    obtain ⟨a,ha,b,hb,eq|⟨eq,mark⟩⟩ := steps j js
    all_goals
      have av := hi_prior (s:=s) ha
      have bv := hi_prior (s:=s) hb
      rw [dj] at av bv
      have unclean : ¬clean N s (n N+k) := by unfold clean n; omega
      have ev : liftBank W s (n N+k)= W (n N+j) := by
        have h1 : ¬n N+k<n N := by omega
        have h2 : n N+k≠n N := by omega
        have h3 : ¬n N+k≤n N+s := by omega
        have h4 : n N+k-(1+s)=n N+j := by omega
        simp [liftBank,h1,h2,h3,h4]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at eq
      rcases eq with eq|eq|eq
      · exact ⟨.sup (hi N s a) (hi N s b),by simp [Good,ev,eq,Node.den,Node.gate,hieq,av,bv,unclean]⟩
      · exact ⟨.copy (hi N s a),by simp [Good,ev,eq,Node.den,Node.gate,hieq,av,unclean]⟩
      · exact ⟨.zero,by simp [Good,ev,eq,Node.den,Node.gate,unclean]⟩
    · rcases mark with hj|⟨T,U,hT,hU⟩
      · have inMark : k∈inM s M := Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,js⟩,dj⟩
        exact ⟨.both (hi N s a) (hi N s b),by
          simp [Good,ev,eq,Node.den,Node.gate,hieq,av,bv,unclean,inMark]⟩
      · have al := loeq W raw a (by omega : a<n N+s)
        have pure : pointRow ⁻¹' W a=W a := by rw [hT]; ext z; simp [pointRow]
        have ac := low_clean (s:=s) (w:=a) (by omega : a<n N+s)
        have low : lo N a<n N+k := by have := lo_prior ha; omega
        exact ⟨.both (lo N a) (hi N s b),by
          simp [Good,ev,eq,Node.den,Node.gate,al,pure,hieq,low,bv,unclean,ac]⟩

end N9134
