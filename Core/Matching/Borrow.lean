import Core.Datatypes.Enum

/-!
# 按借用的 `match`

在 `Datatypes.Enum` 上加入按借用匹配 `bmat x q arms`：`match &x { .V0(q) => …, … }`。
分支变量 `q` 不拥有值，只指向 `x` 的载荷（`Projection.Lock` 的投影）；分支里可以通过 `q` 读载荷（`readq q`）。
分支结束后 `x` 仍然拥有它的值，`q` 不再能用。

**锁定**：分支执行期间 `x` 被锁住，分支里的语句不能写 `x`（移动、释放、构造、析构），也不能写 `q`；
只读使用 `use x` 允许。为了让锁定规则有意义，分支里加了一种能销毁枚举的语句 `dropE z`
（例如以 `sink` 传给一个函数）：不经检查时，`dropE x` 之后再 `readq q` 就会读到已释放的载荷。

**静态检查**：`readq q` 只能出现在带载荷的变体的分支里；`match` 必须穷尽；各分支结束状态合并。

**主定理** `safety_and_no_leak`：检查器接受的程序（含按移动和按借用的 `match`），
执行和作用域结束时的析构都不出错，结束时堆上没有活着的值。

证明思路：分支执行期间维持 `ArmInv`——`x` 仍拥有同一个位置 `l`，`l` 活着、载荷不变、`q` 指向这个载荷。
不写 `x` 的语句不会动 `l`（`DInv` 里“每个位置恰好一个拥有者”保证别的变量释放的不是 `l`，也不是 `l` 的载荷）。
-/

namespace Core.Matching.Borrow
open Core.Datatypes.Enum (Own Ty SEnv hasPay Stmt checkS joinAll St look execS dropOne dropAll Shape DInv
  Compat compat_empty dinv_empty compat_joinAll live_ne_next stepS dropOne_sound dropAll_sound
  killOp killLoc newOp wrapOp moveOp)

/-- 分支里的语句：`Datatypes.Enum` 的语句、通过 `q` 读载荷、销毁一个枚举。 -/
inductive BStmt
  | s     (t : Stmt)
  | readq (q : Var)
  | dropE (z : Var)

inductive Item
  | base (it : Datatypes.Enum.Item)
  | bmat (x q : Var) (arms : List (List BStmt))

/-- 语句 `t` 是否写变量 `v`（`use` 是只读的）。 -/
def wr : Stmt → Var → Bool
  | .alloc z, v          => decide (z = v)
  | .free z, v           => decide (z = v)
  | .use _, _            => false
  | .move a b, v         => decide (a = v) || decide (b = v)
  | .mk z _ none, v      => decide (z = v)
  | .mk z _ (some y), v  => decide (z = v) || decide (y = v)

/-! ## 静态检查 -/

section
variable (Γ : Var → Ty) (D : List Bool) (N : Nat)

/-- 第 `i` 个分支里的一条语句：`x` 被锁住，`q` 只能读。 -/
def checkB (x q : Var) (i : Nat) (σ : SEnv) : BStmt → Option SEnv
  | .s t     => if wr t x = false ∧ wr t q = false then checkS Γ D N σ t else none
  | .readq r => if r = q ∧ hasPay D i = true then some σ else none
  | .dropE z => if Γ z = .enum ∧ σ z = .yes ∧ z ≠ x then some (upd σ z .no) else none

def checkBList (x q : Var) (i : Nat) (σ : SEnv) : List BStmt → Option SEnv
  | []      => some σ
  | b :: bs =>
    match checkB Γ D N x q i σ b with
    | some σ' => checkBList x q i σ' bs
    | none    => none

def checkBArms (x q : Var) (σ : SEnv) : Nat → List (List BStmt) → Option (List SEnv)
  | _, []      => some []
  | i, a :: as =>
    match checkBList Γ D N x q i σ a, checkBArms x q σ (i + 1) as with
    | some σ', some l => some (σ' :: l)
    | _, _            => none

def checkItem (σ : SEnv) : Item → Option SEnv
  | .base it => Datatypes.Enum.checkItem Γ D N σ it
  | .bmat x q arms =>
    if Γ x = .enum ∧ x ≠ q ∧ σ x = .yes ∧ σ q = .no ∧ arms.length = D.length
    then (checkBArms Γ D N x q σ 0 arms).map joinAll
    else none

def checkItems (σ : SEnv) : List Item → Option SEnv
  | []        => some σ
  | it :: its =>
    match checkItem Γ D N σ it with
    | some σ' => checkItems σ' its
    | none    => none

end

/-! ## 动态语义 -/

/-- 分支开始：`q` 指向载荷（没有载荷时为 `none`），不拥有它（drop flag 不变）。 -/
def bindOp (q : Var) (po : Option Loc) (s : St) : St := { s with env := upd s.env q po }

section
variable (Γ : Var → Ty) (D : List Bool)

def execB (s : St) : BStmt → Option St
  | .s t     => execS s t
  | .readq r =>
    match s.env r with
    | some p => if s.live p = true then some s else none
    | none   => none
  | .dropE z => dropOne Γ D z s

def execBList (s : St) : List BStmt → Option St
  | []      => some s
  | b :: bs =>
    match execB Γ D s b with
    | some s' => execBList s' bs
    | none    => none

def execItem (s : St) : Item → Option St
  | .base it => Datatypes.Enum.execItem s it
  | .bmat x q arms =>
    match look s x with
    | some l =>
      match arms[s.tag l]? with
      | some a => execBList Γ D (bindOp q (s.pay l) s) a
      | none   => none
    | none => none

def execItems (s : St) : List Item → Option St
  | []        => some s
  | it :: its =>
    match execItem Γ D s it with
    | some s' => execItems s' its
    | none    => none

end

/-- 分支执行期间的不变式：`x` 仍拥有活着的 `l`，载荷不变，`q` 指向载荷。 -/
structure ArmInv (x q : Var) (l : Loc) (po : Option Loc) (s : St) : Prop where
  fx : s.flag x = true
  ex : s.env x = some l
  lv : s.live l = true
  py : s.pay l = po
  eq : ∀ p, po = some p → s.env q = some p

/-! ## 引理 -/

section
variable {Γ : Var → Ty} {D : List Bool} {N : Nat}

/-- 给不拥有值的变量改指向，不影响 `DInv`。 -/
theorem dinv_bind {q : Var} {po : Option Loc} {s : St} (hd : DInv Γ D N s)
    (hfq : s.flag q = false) : DInv Γ D N (bindOp q po s) := by
  have ne : ∀ z, s.flag z = true → z ≠ q := by
    intro z hz h; rw [h, hfq] at hz; contradiction
  constructor
  · intro z hz
    obtain ⟨l, hl, h1, h2⟩ := hd.owned z hz
    exact ⟨l, by simp [bindOp, upd, ne z hz, hl], h1, h2⟩
  · intro l p h1 h2
    exact hd.payok l p h1 h2
  · intro m hm
    rcases hd.held m hm with ⟨z, hz, hez⟩ | h
    · left; exact ⟨z, hz, by simp [bindOp, upd, ne z hz, hez]⟩
    · right; exact h
  · intro a b m ha hb hea heb
    simp [bindOp, upd, ne a ha] at hea
    simp [bindOp, upd, ne b hb] at heb
    exact hd.vv a b m ha hb hea heb
  · intro a m l ha hea hl hpl
    simp [bindOp, upd, ne a ha] at hea
    exact hd.vp a m l ha hea hl hpl
  · intro l l' m h1 h2 h3 h4
    exact hd.pp l l' m h1 h2 h3 h4
  · intro l h
    exact hd.fresh l h
  · intro z hz
    exact hd.bound z hz

/-- 不写 `x`、`q` 的语句：`x` 仍拥有 `l`，`l` 活着、载荷不变，`q` 的指向不变。 -/
theorem frameS {σ σ' : SEnv} {s s' : St} {t : Stmt} {x q : Var} {l : Loc}
    (hc : checkS Γ D N σ t = some σ') (hc0 : Compat σ s.flag) (hd : DInv Γ D N s)
    (he : execS s t = some s') (hx : wr t x = false) (hq : wr t q = false)
    (hfx : s.flag x = true) (hl : s.env x = some l) (hlive : s.live l = true) :
    s'.flag x = true ∧ s'.env x = some l ∧ s'.live l = true ∧ s'.pay l = s.pay l ∧
      s'.env q = s.env q := by
  have hne := live_ne_next hd l hlive
  cases t with
  | alloc z =>
    simp [wr] at hx hq
    simp [execS] at he
    subst he
    exact ⟨by simp [newOp, upd, Ne.symm hx, hfx], by simp [newOp, upd, Ne.symm hx, hl],
      by simp [newOp, upd, hne, hlive], by simp [newOp, upd, hne], by simp [newOp, upd, Ne.symm hq]⟩
  | free z =>
    simp [wr] at hx
    simp only [checkS] at hc
    split at hc
    · rename_i h
      obtain ⟨_, hz⟩ := h
      have hfz := hc0.yes z hz
      obtain ⟨m, hm, hmlive, _⟩ := hd.owned z hfz
      have hlk : look s z = some m := by simp [look, hm, hmlive]
      simp [execS, hlk] at he
      subst he
      have hml : m ≠ l := by
        intro h; rw [h] at hm; exact hx (hd.vv z x l hfz hfx hm hl)
      exact ⟨by simp [killOp, upd, Ne.symm hx, hfx], hl, by simp [killOp, upd, Ne.symm hml, hlive],
        rfl, rfl⟩
    · contradiction
  | use z =>
    simp only [checkS] at hc
    split at hc
    · rename_i hz
      obtain ⟨m, hm, hmlive, _⟩ := hd.owned z (hc0.yes z hz)
      have hlk : look s z = some m := by simp [look, hm, hmlive]
      simp [execS, hlk] at he
      subst he
      exact ⟨hfx, hl, hlive, rfl, rfl⟩
    · contradiction
  | move a b =>
    simp [wr] at hx hq
    obtain ⟨hax, hbx⟩ := hx
    simp only [checkS] at hc
    split at hc
    · rename_i h
      obtain ⟨_, _, ha, _, _⟩ := h
      obtain ⟨m, hm, hmlive, _⟩ := hd.owned a (hc0.yes a ha)
      have hlk : look s a = some m := by simp [look, hm, hmlive]
      simp [execS, hlk] at he
      subst he
      exact ⟨by simp [moveOp, upd, Ne.symm hax, Ne.symm hbx, hfx], by simp [moveOp, upd, Ne.symm hbx, hl],
        hlive, rfl, by simp [moveOp, upd, Ne.symm hq.2]⟩
    · contradiction
  | mk z i o =>
    cases o with
    | none =>
      simp [wr] at hx hq
      simp [execS] at he
      subst he
      exact ⟨by simp [newOp, upd, Ne.symm hx, hfx], by simp [newOp, upd, Ne.symm hx, hl],
        by simp [newOp, upd, hne, hlive], by simp [newOp, upd, hne], by simp [newOp, upd, Ne.symm hq]⟩
    | some y =>
      simp [wr] at hx hq
      obtain ⟨hzx, hyx⟩ := hx
      simp only [checkS] at hc
      split at hc
      · rename_i h
        obtain ⟨_, _, _, _, hy, _, _, _⟩ := h
        obtain ⟨p, hp, hplive, _⟩ := hd.owned y (hc0.yes y hy)
        have hlk : look s y = some p := by simp [look, hp, hplive]
        simp [execS, hlk] at he
        subst he
        exact ⟨by simp [wrapOp, upd, Ne.symm hzx, Ne.symm hyx, hfx], by simp [wrapOp, upd, Ne.symm hzx, hl],
          by simp [wrapOp, upd, hne, hlive], by simp [wrapOp, upd, hne], by simp [wrapOp, upd, Ne.symm hq.1]⟩
      · contradiction

/-- 销毁别的枚举 `z ≠ x`：同样不动 `l` 和它的载荷。 -/
theorem frameDrop {s s' : St} {z x q : Var} {l : Loc} (hd : DInv Γ D N s)
    (hfz : s.flag z = true) (hΓ : Γ z = .enum) (hzx : z ≠ x) (he : dropOne Γ D z s = some s')
    (hfx : s.flag x = true) (hl : s.env x = some l) (hlive : s.live l = true) :
    s'.flag x = true ∧ s'.env x = some l ∧ s'.live l = true ∧ s'.pay l = s.pay l ∧
      s'.env q = s.env q := by
  obtain ⟨m, hm, hmlive, hsh⟩ := hd.owned z hfz
  have hlk : look s z = some m := by simp [look, hm, hmlive]
  have hml : m ≠ l := by
    intro h; rw [h] at hm; exact hzx (hd.vv z x l hfz hfx hm hl)
  rw [hΓ] at hsh
  obtain ⟨_, hps⟩ := hsh
  cases hp : s.pay m with
  | none =>
    have hh : hasPay D (s.tag m) = false := by simpa [hp] using hps.symm
    simp [dropOne, hfz, hlk, hΓ, hh] at he
    subst he
    exact ⟨by simp [killOp, upd, Ne.symm hzx, hfx], hl, by simp [killOp, upd, Ne.symm hml, hlive],
      rfl, rfl⟩
  | some p =>
    have hh : hasPay D (s.tag m) = true := by simpa [hp] using hps.symm
    have hpl := (hd.payok m p hmlive hp).1
    simp [dropOne, hfz, hlk, hΓ, hh, hp, hpl] at he
    subst he
    have hpl' : p ≠ l := by
      intro h; rw [h] at hp; exact hd.vp x l m hfx hl hmlive hp
    exact ⟨by simp [killOp, killLoc, upd, Ne.symm hzx, hfx], hl,
      by simp [killOp, killLoc, upd, Ne.symm hml, Ne.symm hpl', hlive], rfl, rfl⟩

theorem compat_dropE {σ : SEnv} {s s' : St} {z : Var} (hc : Compat σ s.flag)
    (hz : s'.flag z = false) (hrest : ∀ y, y ≠ z → s'.flag y = s.flag y) :
    Compat (upd σ z .no) s'.flag := by
  constructor
  · intro y hy
    by_cases hyz : y = z
    · subst hyz; simp at hy
    · simp [hyz] at hy
      rw [hrest y hyz]
      exact hc.yes y hy
  · intro y hy
    by_cases hyz : y = z
    · rw [hyz]; exact hz
    · simp [hyz] at hy
      rw [hrest y hyz]
      exact hc.no y hy

/-! ## 分支里的语句 -/

theorem bstep {x q : Var} {l : Loc} {po : Option Loc} {i : Nat} {σ σ' : SEnv} {s : St} {b : BStmt}
    (hpo : hasPay D i = true → ∃ p, po = some p)
    (hc : checkB Γ D N x q i σ b = some σ') (hc0 : Compat σ s.flag) (hd : DInv Γ D N s)
    (ha : ArmInv x q l po s) :
    ∃ s', execB Γ D s b = some s' ∧ Compat σ' s'.flag ∧ DInv Γ D N s' ∧ ArmInv x q l po s' := by
  obtain ⟨hfx, hl, hlive, hpay, henv⟩ := ha
  cases b with
  | s t =>
    simp only [checkB] at hc
    split at hc
    · rename_i h
      obtain ⟨hx, hq⟩ := h
      obtain ⟨s', he, hc', hd'⟩ := stepS hc hc0 hd
      obtain ⟨f1, f2, f3, f4, f5⟩ := frameS hc hc0 hd he hx hq hfx hl hlive
      refine ⟨s', he, hc', hd', f1, f2, f3, by rw [f4]; exact hpay, ?_⟩
      intro p hp
      rw [f5]
      exact henv p hp
    · contradiction
  | readq r =>
    simp only [checkB] at hc
    split at hc
    · rename_i h
      obtain ⟨hr, hi⟩ := h
      cases hc
      obtain ⟨p, hp⟩ := hpo hi
      have hq := henv p hp
      have hpl : s.live p = true := (hd.payok l p hlive (by rw [hpay]; exact hp)).1
      exact ⟨s, by simp [execB, hr, hq, hpl], hc0, hd, hfx, hl, hlive, hpay, henv⟩
    · contradiction
  | dropE z =>
    simp only [checkB] at hc
    split at hc
    · rename_i h
      obtain ⟨hΓ, hz, hzx⟩ := h
      cases hc
      have hfz := hc0.yes z hz
      obtain ⟨s', he, hd', hfz', hrest⟩ := dropOne_sound z hd
      obtain ⟨f1, f2, f3, f4, f5⟩ := frameDrop (q := q) hd hfz hΓ hzx he hfx hl hlive
      refine ⟨s', he, compat_dropE hc0 hfz' hrest, hd', f1, f2, f3, by rw [f4]; exact hpay, ?_⟩
      intro p hp
      rw [f5]
      exact henv p hp
    · contradiction

theorem armSound {x q : Var} {l : Loc} {po : Option Loc} {i : Nat}
    (hpo : hasPay D i = true → ∃ p, po = some p) (bs : List BStmt) :
    ∀ {σ σ' : SEnv} {s : St}, checkBList Γ D N x q i σ bs = some σ' →
      Compat σ s.flag → DInv Γ D N s → ArmInv x q l po s →
      ∃ s', execBList Γ D s bs = some s' ∧ Compat σ' s'.flag ∧ DInv Γ D N s' := by
  induction bs with
  | nil =>
    intro σ σ' s hc hc0 hd _
    simp [checkBList] at hc
    subst hc
    exact ⟨s, by simp [execBList], hc0, hd⟩
  | cons b bs ih =>
    intro σ σ' s hc hc0 hd ha
    simp only [checkBList] at hc
    split at hc
    · rename_i σ₁ h₁
      obtain ⟨s₁, he₁, hc₁, hd₁, ha₁⟩ := bstep hpo h₁ hc0 hd ha
      obtain ⟨s₂, he₂, hc₂, hd₂⟩ := ih hc hc₁ hd₁ ha₁
      exact ⟨s₂, by simp [execBList, he₁, he₂], hc₂, hd₂⟩
    · contradiction

theorem barms_get {x q : Var} {σ : SEnv} (arms : List (List BStmt)) :
    ∀ (i : Nat) {L : List SEnv}, checkBArms Γ D N x q σ i arms = some L →
      ∀ j a, arms[j]? = some a → ∃ σj, checkBList Γ D N x q (i + j) σ a = some σj ∧ σj ∈ L := by
  induction arms with
  | nil => intro i L _ j a ha; simp at ha
  | cons a0 as ih =>
    intro i L hc j a ha
    simp only [checkBArms] at hc
    split at hc
    · rename_i σ0 l h0 hl
      cases hc
      cases j with
      | zero =>
        simp at ha
        subst ha
        exact ⟨σ0, by simpa using h0, by simp⟩
      | succ j =>
        simp at ha
        obtain ⟨σj, hj, hm⟩ := ih (i + 1) hl j a ha
        have e : i + 1 + j = i + (j + 1) := by omega
        rw [e] at hj
        exact ⟨σj, hj, by simp [hm]⟩
    · contradiction

/-! ## 项与项列表 -/

theorem itemSound {σ σ' : SEnv} {s : St} {it : Item}
    (hc : checkItem Γ D N σ it = some σ') (hc0 : Compat σ s.flag) (hd : DInv Γ D N s) :
    ∃ s', execItem Γ D s it = some s' ∧ Compat σ' s'.flag ∧ DInv Γ D N s' := by
  cases it with
  | base it =>
    simp only [checkItem] at hc
    obtain ⟨s', h1, h2, h3⟩ := Datatypes.Enum.itemSound hc hc0 hd
    exact ⟨s', by simp [execItem, h1], h2, h3⟩
  | bmat x q arms =>
    simp only [checkItem] at hc
    split at hc
    · rename_i h
      obtain ⟨hΓx, hxq, hx, hq, hlen⟩ := h
      cases hL : checkBArms Γ D N x q σ 0 arms with
      | none => rw [hL] at hc; simp at hc
      | some L =>
        rw [hL] at hc
        simp at hc
        have hfx := hc0.yes x hx
        obtain ⟨l, hl, hlive, hsh⟩ := hd.owned x hfx
        rw [hΓx] at hsh
        obtain ⟨htl, hps⟩ := hsh
        have htl' : s.tag l < arms.length := by rw [hlen]; exact htl
        have ha : arms[s.tag l]? = some arms[s.tag l] := List.getElem?_eq_getElem htl'
        obtain ⟨σt, hct, hmem⟩ := barms_get arms 0 hL (s.tag l) _ ha
        rw [Nat.zero_add] at hct
        have hlk : look s x = some l := by simp [look, hl, hlive]
        have hpo : hasPay D (s.tag l) = true → ∃ p, s.pay l = some p := by
          intro hh
          cases hp : s.pay l with
          | none => rw [hp, hh] at hps; simp at hps
          | some p => exact ⟨p, rfl⟩
        have ha0 : ArmInv x q l (s.pay l) (bindOp q (s.pay l) s) :=
          { fx := hfx
            ex := by simp [bindOp, upd, hxq, hl]
            lv := hlive
            py := rfl
            eq := by intro p hp; simp [bindOp, hp] }
        obtain ⟨s', he, hc', hd'⟩ :=
          armSound hpo arms[s.tag l] hct (show Compat σ (bindOp q (s.pay l) s).flag from hc0)
            (dinv_bind hd (hc0.no q hq)) ha0
        refine ⟨s', by simp [execItem, hlk, ha, he], ?_, hd'⟩
        rw [← hc]
        exact compat_joinAll hmem hc'
    · contradiction

theorem itemsSound (its : List Item) :
    ∀ {σ σ' : SEnv} {s : St}, checkItems Γ D N σ its = some σ' →
      Compat σ s.flag → DInv Γ D N s →
      ∃ s', execItems Γ D s its = some s' ∧ Compat σ' s'.flag ∧ DInv Γ D N s' := by
  induction its with
  | nil =>
    intro σ σ' s hc hc0 hd
    simp [checkItems] at hc
    subst hc
    exact ⟨s, by simp [execItems], hc0, hd⟩
  | cons it its ih =>
    intro σ σ' s hc hc0 hd
    simp only [checkItems] at hc
    split at hc
    · rename_i σ₁ h₁
      obtain ⟨s₁, he₁, hc₁, hd₁⟩ := itemSound h₁ hc0 hd
      obtain ⟨s₂, he₂, hc₂, hd₂⟩ := ih hc hc₁ hd₁
      exact ⟨s₂, by simp [execItems, he₁, he₂], hc₂, hd₂⟩
    · contradiction

end

/-! ## 主定理 -/

/-- **`Matching.Borrow` 主定理。** 检查器接受的程序（按移动和按借用的 `match`），
执行和作用域结束时的析构都不会出错，并且结束时堆上没有活着的值。 -/
theorem safety_and_no_leak (Γ : Var → Ty) (D : List Bool) (N : Nat) (its : List Item)
    (σ' : SEnv) (h : checkItems Γ D N (fun _ => .no) its = some σ') :
    ∃ s', (execItems Γ D St.empty its).bind (fun s => dropAll Γ D s N) = some s' ∧
      ∀ l, s'.live l = false := by
  obtain ⟨s₁, he₁, _, hd₁⟩ := itemsSound its h compat_empty (dinv_empty Γ D N)
  obtain ⟨s₂, he₂, hd₂, hf₂⟩ := dropAll_sound hd₁ N
  refine ⟨s₂, by rw [he₁]; exact he₂, ?_⟩
  have noflag : ∀ x, s₂.flag x = true → False := by
    intro x hx
    rw [hf₂ x (hd₂.bound x hx)] at hx
    contradiction
  intro l
  cases hl : s₂.live l with
  | false => rfl
  | true =>
    exfalso
    rcases hd₂.held l hl with ⟨x, hx, _⟩ | ⟨l', hl', hpl'⟩
    · exact noflag x hx
    · rcases hd₂.held l' hl' with ⟨x, hx, _⟩ | ⟨l'', hl'', hpl''⟩
      · exact noflag x hx
      · rw [(hd₂.payok l'' l' hl'' hpl'').2] at hpl'
        contradiction

/-! ## 例子

沿用 `Datatypes.Enum`：`enum Opt { Some(Box<I64>), None }`，变量 0 是 `Opt`，1、2 是 `Box`。 -/

def chk (its : List Item) : Bool := (checkItems Datatypes.Enum.Γx Datatypes.Enum.Dx 3 (fun _ => .no) its).isSome
def run (its : List Item) : Bool :=
  ((execItems Datatypes.Enum.Γx Datatypes.Enum.Dx St.empty its).bind (fun s => dropAll Datatypes.Enum.Γx Datatypes.Enum.Dx s 3)).isSome

def pre : List Item := [.base (.stmt (.alloc 1)), .base (.stmt (.mk 0 0 (some 1)))]

/-- `match &x0 { .Some(q2) => { read(*q2); use(x0) }, .None => {} }`：接受，运行无泄漏。 -/
def demo : List Item := pre ++ [.bmat 0 2 [[.readq 2, .s (.use 0)], []]]
example : chk demo = true := rfl
example : run demo = true := rfl

/-- 借用结束后 `x0` 仍拥有值，可以再按移动 `match`，`q2` 这个名字也可以重新绑定拥有的载荷。 -/
example : chk (demo ++ [.base (.mat 0 2 [[.free 2], []])]) = true := rfl
example : run (demo ++ [.base (.mat 0 2 [[.free 2], []])]) = true := rfl

/-- 分支之外不能再用 `q2`。 -/
example : chk (demo ++ [.base (.stmt (.use 2))]) = false := rfl

/-- `.None` 分支没有载荷，不能读 `q2`。 -/
example : chk (pre ++ [.bmat 0 2 [[], [.readq 2]]]) = false := rfl

/-- 锁定：分支里销毁 `x0` 被拒绝。 -/
def bad : List Item := pre ++ [.bmat 0 2 [[.dropE 0, .readq 2], []]]
example : chk bad = false := rfl

/-- 不经检查执行：`x0` 被销毁后再通过 `q2` 读载荷，读到已释放的内存，执行卡住。 -/
example : (execItems Datatypes.Enum.Γx Datatypes.Enum.Dx St.empty bad).isNone = true := rfl

/-- 分支里做别的事（分配、释放别的值）照常允许。 -/
example : chk (pre ++ [.bmat 0 2 [[.s (.alloc 1), .readq 2, .s (.free 1)], []]]) = true := rfl

end Core.Matching.Borrow
