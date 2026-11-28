import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166.TerminalCut
abbrev V := Fin 5 × Fin 4
abbrev B := V → Bool
def words : Array Nat := #[541201,295441,533521,164881,272401,149521,540961,295201,532801,164161,270721,147841,529441,268321,528961,137281,266881,136321,99361,84001,98881,75841,82561,74881,540962,295202,529442,99362,268322,84002,541202,295442,528962,98882,266882,82562,533522,272402,532802,75842,270722,74882,164882,149522,164162,137282,147842,136322,532804,164164,528964,98884,137284,75844,533524,164884,529444,99364,136324,74884,541204,149524,540964,84004,147844,82564,295444,272404,295204,268324,270724,266884,270728,147848,266888,82568,136328,74888,272408,149528,268328,84008,137288,75848,295448,164888,295208,99368,164168,98888,541208,533528,540968,529448,532808,528968]
def sample (h q : Fin 4) (t : Fin 6) (v : V) : Bool :=
  words[24*h.val+6*q.val+t.val]!.testBit (4*v.1.val+v.2.val)
def fixed (x : B) (h : Fin 4) := ∀ k : Fin 4,x (0,k)=(h==k)
theorem sampleFixed : ∀h q t,fixed (sample h q t) h := by
  unfold fixed
  decide +kernel
theorem varied : ∀ h : Fin 4, ∀ v : V, v.1≠0 → v.2≠h →
    ∃ q : Fin 4,∃ s t : Fin 6,sample h q s v≠sample h q t v := by decide +kernel

inductive Tree where
  | leaf
  | node (v : V) (zero one : Tree)
def path : Tree → B → List Bool
  | .leaf, _ => []
  | .node v z o,x => (x v)::(if x v then path o x else path z x)
def single (T : Tree) (h : Fin 4) := ∀ q : Fin 4, ∀ s t : Fin 6,
  path T (sample h q s)=path T (sample h q t)
def apart (T : Tree) (a b : Fin 4) :=
  path T (sample a 0 0) ≠ path T (sample b 0 0)

theorem separate (T : Tree) (a b : Fin 4) (ne : a≠b)
    (ca : single T a) (cb : single T b) (d : apart T a b)
    (x y : B) (xa : fixed x a) (yb : fixed y b) : path T x ≠ path T y := by
  induction T with
  | leaf => exact (d rfl).elim
  | node v z o ihz iho =>
    have row : v.1=0 := by
      by_contra nr
      have head (h : Fin 4) (hh : single (.node v z o) h) (diff : v.2≠h) : False := by
        obtain ⟨q,s,t,une⟩:=varied h v nr diff
        exact une (List.cons.inj (hh q s t)).1
      by_cases eq : v.2=a
      · exact head b cb (by simpa [eq] using ne)
      · exact head a ca eq
    obtain ⟨p,k⟩:=v
    change p=0 at row
    subst p
    have xs:=xa k
    have ys:=yb k
    have ar (q : Fin 4) (t : Fin 6) := sampleFixed a q t k
    have br (q : Fin 4) (t : Fin 6) := sampleFixed b q t k
    by_cases ak : a=k
    · subst k
      have bk : (b==a)=false := by simp [Ne.symm ne]
      simp [path,xs,ys,bk]
    · by_cases bk : b=k
      · subst k
        have av : (a==b)=false := by simp [ne]
        simp [path,xs,ys,av]
      · have av : (a==k)=false := by simp [ak]
        have bv : (b==k)=false := by simp [bk]
        have az : single z a := by
          intro q s t
          simpa [path,ar,av] using ca q s t
        have bz : single z b := by
          intro q s t
          simpa [path,br,bv] using cb q s t
        have dz : apart z a b := by
          unfold apart at d ⊢
          simpa [path,ar,br,av,bv] using d
        simpa [path,xs,ys,av,bv] using ihz az bz dz

end PEqualNP.Outside.L_pcx_166.TerminalCut
