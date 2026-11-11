import Core.Ownership.Drop

/-!
# 分支与 drop flag

在 `Ownership.Drop` 的基础上加入分支（暂时只有一层，分支里只能放普通语句）。

**静态检查**：变量有三种状态，`yes`（拥有）、`no`（没有）、`maybe`（可能已移走）。
两个分支结束时状态不同的变量，合并（`join`）后变成 `maybe`。
`maybe` 的变量不能使用、不能移走、不能释放。

**动态语义**：编译后的代码给每个变量维护一个 drop flag（`St.flag`），
表示它此刻是否真的拥有值。作用域结束时按 flag 释放（`dropAll`）。
分支走哪一边由外部输入的 `cs : List Bool` 决定，所以定理对所有分支选择都成立。

**主定理** `safety_and_no_leak`：检查器接受的程序，无论分支怎么走，
执行和作用域结束时的释放都不会出错，并且结束时堆上没有活着的值。

证明结构：动态不变式 `DInv` 只谈 flag，不谈静态状态；
`Compat` 把静态状态和 flag 联系起来（`yes` ⇒ flag 为真，`no` ⇒ flag 为假，`maybe` 不作要求）。
这样分支合并只需要证明 `Compat` 能弱化到 `join`。
-/

namespace Core.Ownership.Branch
open Core.Ownership.Move (Stmt)
open Core.Ownership.Drop (varsOk)

inductive Own | no | yes | maybe
  deriving DecidableEq, Repr

abbrev SEnv := Var → Own

/-! ## 静态检查 -/

def checkS (σ : SEnv) : Stmt → Option SEnv
  | .alloc x  => if σ x = .no then some (upd σ x .yes) else none
  | .move x y =>
      if x = y then none
      else if σ x = .yes then
        (if σ y = .no then some (upd (upd σ x .no) y .yes) else none)
      else none
  | .use x    => if σ x = .yes then some σ else none
  | .free x   => if σ x = .yes then some (upd σ x .no) else none

def checkStmtV (N : Nat) (σ : SEnv) (t : Stmt) : Option SEnv :=
  if varsOk N t = true then checkS σ t else none

def checkList (N : Nat) (σ : SEnv) : List Stmt → Option SEnv
  | []      => some σ
  | t :: ts =>
    match checkStmtV N σ t with
    | some σ' => checkList N σ' ts
    | none    => none

inductive Item
  | stmt   (t : Stmt)
  | branch (a b : List Stmt)

/-- 两个分支结束时的状态合并：一致则保留，不一致则变成 `maybe`。 -/
def join (σa σb : SEnv) : SEnv := fun x => if σa x = σb x then σa x else .maybe

def checkItem (N : Nat) (σ : SEnv) : Item → Option SEnv
  | .stmt t     => checkStmtV N σ t
  | .branch a b =>
    match checkList N σ a, checkList N σ b with
    | some σa, some σb => some (join σa σb)
    | _, _             => none

def checkItems (N : Nat) (σ : SEnv) : List Item → Option SEnv
  | []        => some σ
  | it :: its =>
    match checkItem N σ it with
    | some σ' => checkItems N σ' its
    | none    => none

/-! ## 动态语义（带 drop flag） -/

structure St where
  env  : Var → Option Loc
  live : Loc → Bool
  next : Loc
  flag : Var → Bool   -- drop flag：此刻是否真的拥有值

def St.empty : St :=
  { env := fun _ => none, live := fun _ => false, next := 0, flag := fun _ => false }

def allocOp (x : Var) (s : St) : St :=
  { env := upd s.env x (some s.next), live := upd s.live s.next true,
    next := s.next + 1, flag := upd s.flag x true }

def moveOp (x y : Var) (l : Loc) (s : St) : St :=
  { s with env := upd s.env y (some l), flag := upd (upd s.flag x false) y true }

def freeOp (x : Var) (l : Loc) (s : St) : St :=
  { s with live := upd s.live l false, flag := upd s.flag x false }

def execS (s : St) : Stmt → Option St
  | .alloc x => some (allocOp x s)
  | .move x y =>
      match s.env x with
      | some l => if s.live l = true then some (moveOp x y l s) else none
      | none   => none
  | .use x =>
      match s.env x with
      | some l => if s.live l = true then some s else none
      | none   => none
  | .free x =>
      match s.env x with
      | some l => if s.live l = true then some (freeOp x l s) else none
      | none   => none

def execList (s : St) : List Stmt → Option St
  | []      => some s
  | t :: ts =>
    match execS s t with
    | some s' => execList s' ts
    | none    => none

def execItem (s : St) (c : Bool) : Item → Option St
  | .stmt t     => execS s t
  | .branch a b => if c = true then execList s a else execList s b

/-- `cs` 给出每一步的分支选择（不够时默认走 `false` 分支）。 -/
def execItems (s : St) : List Bool → List Item → Option St
  | _,  []        => some s
  | cs, it :: its =>
    match execItem s (cs.headD false) it with
    | some s' => execItems s' cs.tail its
    | none    => none

/-- 作用域结束：按 drop flag 释放变量 `x`。 -/
def dropOne (x : Var) (s : St) : Option St :=
  if s.flag x = true then
    match s.env x with
    | some l => if s.live l = true then some (freeOp x l s) else none
    | none   => none
  else some s

def dropAll (s : St) : Nat → Option St
  | 0     => some s
  | n + 1 =>
    match dropAll s n with
    | some s' => dropOne n s'
    | none    => none

/-! ## 不变式 -/

/-- 动态不变式：只谈 drop flag。 -/
structure DInv (N : Nat) (s : St) : Prop where
  owned_live : ∀ x, s.flag x = true → ∃ l, s.env x = some l ∧ s.live l = true
  unique : ∀ x y l, s.flag x = true → s.flag y = true → s.env x = some l → s.env y = some l → x = y
  bounded : ∀ x l, s.env x = some l → l < s.next
  live_owned : ∀ l, s.live l = true → ∃ x, s.flag x = true ∧ s.env x = some l
  bound : ∀ x, s.flag x = true → x < N

/-- 静态状态与 drop flag 一致；`maybe` 不作要求。 -/
structure Compat (σ : SEnv) (f : Var → Bool) : Prop where
  yes : ∀ x, σ x = .yes → f x = true
  no  : ∀ x, σ x = .no → f x = false

theorem compat_empty : Compat (fun _ => .no) St.empty.flag :=
  { yes := by intro x h; simp at h
    no := by intro x _; rfl }

theorem dinv_empty (N : Nat) : DInv N St.empty :=
  { owned_live := by intro x h; simp [St.empty] at h
    unique := by intro x y l hx; simp [St.empty] at hx
    bounded := by intro x l h; simp [St.empty] at h
    live_owned := by intro l h; simp [St.empty] at h
    bound := by intro x h; simp [St.empty] at h }

theorem compat_upd {σ : SEnv} {f : Var → Bool} {x : Var} {o : Own} {b : Bool}
    (h : Compat σ f) (h1 : o = .yes → b = true) (h2 : o = .no → b = false) :
    Compat (upd σ x o) (upd f x b) := by
  constructor
  · intro z hz
    by_cases hzx : z = x
    · subst hzx
      simp [upd] at hz ⊢
      exact h1 hz
    · simp [upd, hzx] at hz ⊢
      exact h.yes z hz
  · intro z hz
    by_cases hzx : z = x
    · subst hzx
      simp [upd] at hz ⊢
      exact h2 hz
    · simp [upd, hzx] at hz ⊢
      exact h.no z hz

theorem compat_join_left {σa σb : SEnv} {f : Var → Bool} (h : Compat σa f) :
    Compat (join σa σb) f := by
  constructor
  · intro x hx
    simp only [join] at hx
    split at hx
    · exact h.yes x hx
    · cases hx
  · intro x hx
    simp only [join] at hx
    split at hx
    · exact h.no x hx
    · cases hx

theorem compat_join_right {σa σb : SEnv} {f : Var → Bool} (h : Compat σb f) :
    Compat (join σa σb) f := by
  constructor
  · intro x hx
    simp only [join] at hx
    split at hx
    · rename_i heq
      rw [heq] at hx
      exact h.yes x hx
    · cases hx
  · intro x hx
    simp only [join] at hx
    split at hx
    · rename_i heq
      rw [heq] at hx
      exact h.no x hx
    · cases hx

/-! ## 三种动态操作保持 `DInv` -/

theorem dinv_alloc {N : Nat} {s : St} {x : Var}
    (hd : DInv N s) (hfx : s.flag x = false) (hxN : x < N) : DInv N (allocOp x s) := by
  constructor
  · intro z hz
    by_cases hzx : z = x
    · subst hzx
      exact ⟨s.next, by simp [allocOp, upd], by simp [allocOp, upd]⟩
    · simp [allocOp, upd, hzx] at hz
      obtain ⟨l, hl, hlive⟩ := hd.owned_live z hz
      have hne : l ≠ s.next := Nat.ne_of_lt (hd.bounded z l hl)
      exact ⟨l, by simp [allocOp, upd, hzx, hl], by simp [allocOp, upd, hne, hlive]⟩
  · intro a b l ha hb hea heb
    by_cases hax : a = x <;> by_cases hbx : b = x
    · rw [hax, hbx]
    · exfalso
      simp [allocOp, upd, hax] at hea
      simp [allocOp, upd, hbx] at heb
      subst hea
      exact Nat.lt_irrefl _ (hd.bounded b _ heb)
    · exfalso
      simp [allocOp, upd, hax] at hea
      simp [allocOp, upd, hbx] at heb
      subst heb
      exact Nat.lt_irrefl _ (hd.bounded a _ hea)
    · simp [allocOp, upd, hax] at ha hea
      simp [allocOp, upd, hbx] at hb heb
      exact hd.unique a b l ha hb hea heb
  · intro z l hz
    show l < s.next + 1
    by_cases hzx : z = x
    · simp [allocOp, upd, hzx] at hz
      subst hz
      exact Nat.lt_succ_self _
    · simp [allocOp, upd, hzx] at hz
      exact Nat.lt_succ_of_lt (hd.bounded z l hz)
  · intro l hl
    by_cases hln : l = s.next
    · exact ⟨x, by simp [allocOp, upd], by simp [allocOp, upd, hln]⟩
    · simp [allocOp, upd, hln] at hl
      obtain ⟨y, hy, hey⟩ := hd.live_owned l hl
      have hyx : y ≠ x := by
        intro h; rw [h] at hy; rw [hy] at hfx; contradiction
      exact ⟨y, by simp [allocOp, upd, hyx, hy], by simp [allocOp, upd, hyx, hey]⟩
  · intro z hz
    by_cases hzx : z = x
    · rw [hzx]; exact hxN
    · simp [allocOp, upd, hzx] at hz
      exact hd.bound z hz

theorem dinv_move {N : Nat} {s : St} {x y : Var} {l : Loc}
    (hd : DInv N s) (hxy : x ≠ y) (hfx : s.flag x = true) (hfy : s.flag y = false)
    (hyN : y < N) (hl : s.env x = some l) (hlive : s.live l = true) :
    DInv N (moveOp x y l s) := by
  have own : ∀ z, z ≠ y → upd (upd s.flag x false) y true z = true →
      z ≠ x ∧ s.flag z = true := by
    intro z hzy hz
    by_cases hzx : z = x
    · subst hzx
      simp [upd, hxy] at hz
    · simp [upd, hzy, hzx] at hz
      exact ⟨hzx, hz⟩
  constructor
  · intro z hz
    by_cases hzy : z = y
    · subst hzy
      exact ⟨l, by simp [moveOp, upd], hlive⟩
    · obtain ⟨_, hz'⟩ := own z hzy hz
      obtain ⟨m, hm, hmlive⟩ := hd.owned_live z hz'
      exact ⟨m, by simp [moveOp, upd, hzy, hm], hmlive⟩
  · intro a b m ha hb hea heb
    by_cases hay : a = y <;> by_cases hby : b = y
    · rw [hay, hby]
    · exfalso
      obtain ⟨hbx, hb'⟩ := own b hby hb
      simp [moveOp, upd, hay] at hea
      simp [moveOp, upd, hby] at heb
      rw [← hea] at heb
      exact hbx (hd.unique x b l hfx hb' hl heb).symm
    · exfalso
      obtain ⟨hax, ha'⟩ := own a hay ha
      simp [moveOp, upd, hay] at hea
      simp [moveOp, upd, hby] at heb
      rw [← heb] at hea
      exact hax (hd.unique x a l hfx ha' hl hea).symm
    · obtain ⟨_, ha'⟩ := own a hay ha
      obtain ⟨_, hb'⟩ := own b hby hb
      simp [moveOp, upd, hay] at hea
      simp [moveOp, upd, hby] at heb
      exact hd.unique a b m ha' hb' hea heb
  · intro z m hz
    show m < s.next
    by_cases hzy : z = y
    · simp [moveOp, upd, hzy] at hz
      rw [← hz]
      exact hd.bounded x l hl
    · simp [moveOp, upd, hzy] at hz
      exact hd.bounded z m hz
  · intro m hm
    obtain ⟨z, hz, hez⟩ := hd.live_owned m hm
    by_cases hzx : z = x
    · rw [hzx, hl] at hez
      simp at hez
      exact ⟨y, by simp [moveOp, upd], by simp [moveOp, upd, hez]⟩
    · have hzy : z ≠ y := by
        intro h; rw [h] at hz; rw [hz] at hfy; contradiction
      exact ⟨z, by simp [moveOp, upd, hzx, hzy, hz], by simp [moveOp, upd, hzy, hez]⟩
  · intro z hz
    by_cases hzy : z = y
    · rw [hzy]; exact hyN
    · obtain ⟨_, hz'⟩ := own z hzy hz
      exact hd.bound z hz'

theorem dinv_free {N : Nat} {s : St} {x : Var} {l : Loc}
    (hd : DInv N s) (hfx : s.flag x = true) (hl : s.env x = some l) :
    DInv N (freeOp x l s) := by
  constructor
  · intro z hz
    by_cases hzx : z = x
    · simp [freeOp, upd, hzx] at hz
    · simp [freeOp, upd, hzx] at hz
      obtain ⟨m, hm, hmlive⟩ := hd.owned_live z hz
      have hml : m ≠ l := by
        intro h
        rw [h] at hm
        exact hzx (hd.unique z x l hz hfx hm hl)
      exact ⟨m, hm, by simp [freeOp, upd, hml, hmlive]⟩
  · intro a b m ha hb hea heb
    by_cases hax : a = x
    · simp [freeOp, upd, hax] at ha
    · by_cases hbx : b = x
      · simp [freeOp, upd, hbx] at hb
      · simp [freeOp, upd, hax] at ha
        simp [freeOp, upd, hbx] at hb
        exact hd.unique a b m ha hb hea heb
  · intro z m hz
    exact hd.bounded z m hz
  · intro m hm
    have hml : m ≠ l := by
      intro h; rw [h] at hm; simp [freeOp, upd] at hm
    simp [freeOp, upd, hml] at hm
    obtain ⟨z, hz, hez⟩ := hd.live_owned m hm
    have hzx : z ≠ x := by
      intro h; rw [h, hl] at hez; simp at hez; exact hml hez.symm
    exact ⟨z, by simp [freeOp, upd, hzx, hz], hez⟩
  · intro z hz
    by_cases hzx : z = x
    · simp [freeOp, upd, hzx] at hz
    · simp [freeOp, upd, hzx] at hz
      exact hd.bound z hz

/-! ## 语句、语句列表、分支 -/

theorem stepS {N : Nat} {σ σ' : SEnv} {s : St} {t : Stmt}
    (hv : varsOk N t = true) (hc : checkS σ t = some σ')
    (hc0 : Compat σ s.flag) (hd : DInv N s) :
    ∃ s', execS s t = some s' ∧ Compat σ' s'.flag ∧ DInv N s' := by
  cases t with
  | alloc x =>
    simp only [checkS] at hc
    split at hc
    · rename_i hx
      cases hc
      simp only [varsOk, decide_eq_true_eq] at hv
      have hfx := hc0.no x hx
      refine ⟨allocOp x s, rfl, ?_, dinv_alloc hd hfx hv⟩
      exact compat_upd hc0 (fun _ => rfl) (fun h => by cases h)
    · contradiction
  | move x y =>
    simp only [checkS] at hc
    split at hc
    · contradiction
    · rename_i hxy
      split at hc
      · rename_i hx
        split at hc
        · rename_i hy
          cases hc
          simp only [varsOk, decide_eq_true_eq] at hv
          have hfx := hc0.yes x hx
          have hfy := hc0.no y hy
          obtain ⟨l, hl, hlive⟩ := hd.owned_live x hfx
          refine ⟨moveOp x y l s, by simp [execS, hl, hlive], ?_,
            dinv_move hd hxy hfx hfy hv hl hlive⟩
          exact compat_upd (compat_upd hc0 (fun h => by cases h) (fun _ => rfl))
            (fun _ => rfl) (fun h => by cases h)
        · contradiction
      · contradiction
  | use x =>
    simp only [checkS] at hc
    split at hc
    · rename_i hx
      cases hc
      have hfx := hc0.yes x hx
      obtain ⟨l, hl, hlive⟩ := hd.owned_live x hfx
      exact ⟨s, by simp [execS, hl, hlive], hc0, hd⟩
    · contradiction
  | free x =>
    simp only [checkS] at hc
    split at hc
    · rename_i hx
      cases hc
      have hfx := hc0.yes x hx
      obtain ⟨l, hl, hlive⟩ := hd.owned_live x hfx
      refine ⟨freeOp x l s, by simp [execS, hl, hlive], ?_, dinv_free hd hfx hl⟩
      exact compat_upd hc0 (fun h => by cases h) (fun _ => rfl)
    · contradiction

theorem listSound (N : Nat) (ts : List Stmt) :
    ∀ {σ σ' : SEnv} {s : St}, checkList N σ ts = some σ' → Compat σ s.flag → DInv N s →
      ∃ s', execList s ts = some s' ∧ Compat σ' s'.flag ∧ DInv N s' := by
  induction ts with
  | nil =>
    intro σ σ' s hc hc0 hd
    simp [checkList] at hc
    subst hc
    exact ⟨s, by simp [execList], hc0, hd⟩
  | cons t ts ih =>
    intro σ σ' s hc hc0 hd
    simp only [checkList] at hc
    split at hc
    · rename_i σ₁ h₁
      simp only [checkStmtV] at h₁
      split at h₁
      · rename_i hv
        obtain ⟨s₁, he₁, hc₁, hd₁⟩ := stepS hv h₁ hc0 hd
        obtain ⟨s₂, he₂, hc₂, hd₂⟩ := ih hc hc₁ hd₁
        exact ⟨s₂, by simp [execList, he₁, he₂], hc₂, hd₂⟩
      · contradiction
    · contradiction

theorem itemSound {N : Nat} {σ σ' : SEnv} {s : St} {it : Item} (c : Bool)
    (hc : checkItem N σ it = some σ') (hc0 : Compat σ s.flag) (hd : DInv N s) :
    ∃ s', execItem s c it = some s' ∧ Compat σ' s'.flag ∧ DInv N s' := by
  cases it with
  | stmt t =>
    simp only [checkItem, checkStmtV] at hc
    split at hc
    · rename_i hv
      exact stepS hv hc hc0 hd
    · contradiction
  | branch a b =>
    simp only [checkItem] at hc
    split at hc
    · rename_i σa σb ha hb
      cases hc
      cases c with
      | true =>
        obtain ⟨s', he, hc', hd'⟩ := listSound N a ha hc0 hd
        exact ⟨s', by simp [execItem, he], compat_join_left hc', hd'⟩
      | false =>
        obtain ⟨s', he, hc', hd'⟩ := listSound N b hb hc0 hd
        exact ⟨s', by simp [execItem, he], compat_join_right hc', hd'⟩
    · contradiction

theorem itemsSound (N : Nat) (its : List Item) :
    ∀ {σ σ' : SEnv} {s : St} (cs : List Bool), checkItems N σ its = some σ' →
      Compat σ s.flag → DInv N s →
      ∃ s', execItems s cs its = some s' ∧ Compat σ' s'.flag ∧ DInv N s' := by
  induction its with
  | nil =>
    intro σ σ' s cs hc hc0 hd
    simp [checkItems] at hc
    subst hc
    exact ⟨s, by simp [execItems], hc0, hd⟩
  | cons it its ih =>
    intro σ σ' s cs hc hc0 hd
    simp only [checkItems] at hc
    split at hc
    · rename_i σ₁ h₁
      obtain ⟨s₁, he₁, hc₁, hd₁⟩ := itemSound (cs.headD false) h₁ hc0 hd
      obtain ⟨s₂, he₂, hc₂, hd₂⟩ := ih cs.tail hc hc₁ hd₁
      exact ⟨s₂, by simp only [execItems, he₁, he₂], hc₂, hd₂⟩
    · contradiction

/-! ## 作用域结束：按 drop flag 释放 -/

theorem dropOne_sound {N : Nat} {s : St} (x : Var) (hd : DInv N s) :
    ∃ s', dropOne x s = some s' ∧ DInv N s' ∧ s'.flag x = false ∧
      ∀ y, y ≠ x → s'.flag y = s.flag y := by
  by_cases hf : s.flag x = true
  · obtain ⟨l, hl, hlive⟩ := hd.owned_live x hf
    refine ⟨freeOp x l s, by simp [dropOne, hf, hl, hlive], dinv_free hd hf hl,
      by simp [freeOp, upd], ?_⟩
    intro y hy
    simp [freeOp, upd, hy]
  · exact ⟨s, by simp [dropOne, hf], hd, by simpa using hf, fun _ _ => rfl⟩

theorem dropAll_sound {N : Nat} {s : St} (hd : DInv N s) :
    ∀ n, ∃ s', dropAll s n = some s' ∧ DInv N s' ∧ ∀ y, y < n → s'.flag y = false := by
  intro n
  induction n with
  | zero => exact ⟨s, by simp [dropAll], hd, fun y h => absurd h (Nat.not_lt_zero y)⟩
  | succ n ih =>
    obtain ⟨s₁, he₁, hd₁, hf₁⟩ := ih
    obtain ⟨s₂, he₂, hd₂, hfn, hrest⟩ := dropOne_sound n hd₁
    refine ⟨s₂, by simp only [dropAll, he₁, he₂], hd₂, ?_⟩
    intro y hy
    by_cases hyn : y = n
    · rw [hyn]; exact hfn
    · rw [hrest y hyn]
      exact hf₁ y (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hy) hyn)

/-! ## 主定理 -/

/-- **`Ownership.Branch` 主定理。** 检查器接受的程序，无论分支怎么走，
执行和作用域结束时按 drop flag 的释放都不会出错，并且结束时堆上没有活着的值。 -/
theorem safety_and_no_leak (N : Nat) (its : List Item) (σ' : SEnv) (cs : List Bool)
    (h : checkItems N (fun _ => .no) its = some σ') :
    ∃ s', (execItems St.empty cs its).bind (fun s => dropAll s N) = some s' ∧
      ∀ l, s'.live l = false := by
  obtain ⟨s₁, he₁, _, hd₁⟩ := itemsSound N its cs h compat_empty (dinv_empty N)
  obtain ⟨s₂, he₂, hd₂, hf₂⟩ := dropAll_sound hd₁ N
  refine ⟨s₂, by rw [he₁]; exact he₂, ?_⟩
  intro l
  cases hl : s₂.live l with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨x, hx, _⟩ := hd₂.live_owned l hl
    have hxN := hd₂.bound x hx
    rw [hf₂ x hxN] at hx
    contradiction

/-! ## 例子 -/

/-- 一个分支里把 0 移走并释放，另一个分支什么都不做。 -/
def demo : List Item := [.stmt (.alloc 0), .branch [.move 0 1, .free 1] []]

/-- 检查器接受。 -/
example : (checkItems 2 (fun _ => .no) demo).isSome = true := rfl

/-- 分支之后 0 是“可能已移走”，再使用就被拒绝。 -/
example : (checkItems 2 (fun _ => .no) (demo ++ [.stmt (.use 0)])).isNone = true := rfl

/-- 两个分支各自执行，结束时按 drop flag 释放，都不出错。 -/
example : ((execItems St.empty [false, true] demo).bind (fun s => dropAll s 2)).isSome = true := rfl
example : ((execItems St.empty [false, false] demo).bind (fun s => dropAll s 2)).isSome = true := rfl

end Core.Ownership.Branch
