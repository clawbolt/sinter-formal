import Core.M2b

/-!
# M4（一）：投影与源对象锁定

在 M2b 的直线代码上加入投影：

- `proj p x`：`let p = proj x.f`。`p` 不拥有值，只指向 `x` 内部。
- `readp p`：通过投影读取。
- `endp p`：投影的生命期结束。这一轮由程序显式写出；
  M4（二）改为由活跃性分析在 `p` 最后一次使用之后自动插入。

**静态检查**：维护一张锁表 `ps : List (投影, 源对象)`。
投影存在期间，源对象被锁定：不能 move、不能 free；只读使用照常允许。
创建投影要求源对象处于 `yes`，投影名不能已经在用。

**动态语义**仍然故意做得“危险”：投影只是一个裸指针（`St4.pr`），
源对象被释放之后照样能拿它去读。文件末尾的例子演示了不经检查直接执行会读到已释放的内存。

**主定理** `safety_and_no_leak`：检查器接受的程序执行不出错
（包括每一次通过投影读取时，指向的位置都还活着），作用域结束后堆上没有活着的值。

证明在 M2b 的 `Compat`、`DInv` 之上加一条：锁表里的每一项 `(p, z)`，
`z` 静态上是 `yes`，并且 `p` 和 `z` 指向同一个位置。
-/

namespace Core.M4
open Core.M1 (Stmt)
open Core.M2b (Own SEnv checkS Compat DInv execS dropAll stepS dropAll_sound
  compat_empty dinv_empty)

inductive Cmd
  | base  (t : Stmt)
  | proj  (p x : Var)
  | readp (p : Var)
  | endp  (p : Var)

/-- 锁表：每一项是 `(投影, 源对象)`。 -/
abbrev Locks := List (Var × Var)

def locked (ps : Locks) (x : Var) : Bool := ps.any (fun e => e.2 == x)
def active (ps : Locks) (p : Var) : Bool := ps.any (fun e => e.1 == p)

/-- 语句会让哪个变量失去它的值（move 的来源、free 的对象）。 -/
def src : Stmt → Option Var
  | .move x _ => some x
  | .free x   => some x
  | _         => none

/-- 语句会改写哪个变量的指针（alloc、move 的目标）。 -/
def tgt : Stmt → Option Var
  | .alloc x  => some x
  | .move _ y => some y
  | _         => none

/-- 被锁定的变量不能失去它的值。 -/
def baseOk (ps : Locks) (t : Stmt) : Bool :=
  match src t with
  | some x => !locked ps x
  | none   => true

/-! ## 静态检查 -/

def check1 (N : Nat) (σ : SEnv) (ps : Locks) : Cmd → Option (SEnv × Locks)
  | .base t =>
    if baseOk ps t = true then
      match Core.M2b.checkStmtV N σ t with
      | some σ' => some (σ', ps)
      | none    => none
    else none
  | .proj p x =>
    if σ x = .yes ∧ active ps p = false then some (σ, (p, x) :: ps) else none
  | .readp p => if active ps p = true then some (σ, ps) else none
  | .endp p  =>
    if active ps p = true then some (σ, ps.filter (fun e => e.1 != p)) else none

def checkL (N : Nat) (σ : SEnv) (ps : Locks) : List Cmd → Option (SEnv × Locks)
  | []      => some (σ, ps)
  | c :: cs =>
    match check1 N σ ps c with
    | some (σ', ps') => checkL N σ' ps' cs
    | none           => none

/-! ## 动态语义：投影是裸指针 -/

structure St4 where
  b  : Core.M2b.St
  pr : Var → Option Loc

def St4.empty : St4 := ⟨Core.M2b.St.empty, fun _ => none⟩

def exec1 (s : St4) : Cmd → Option St4
  | .base t =>
    match execS s.b t with
    | some b' => some ⟨b', s.pr⟩
    | none    => none
  | .proj p x =>
    match s.b.env x with
    | some l => if s.b.live l = true then some ⟨s.b, upd s.pr p (some l)⟩ else none
    | none   => none
  | .readp p =>
    match s.pr p with
    | some l => if s.b.live l = true then some s else none
    | none   => none
  | .endp p => some ⟨s.b, upd s.pr p none⟩

def execL (s : St4) : List Cmd → Option St4
  | []      => some s
  | c :: cs =>
    match exec1 s c with
    | some s' => execL s' cs
    | none    => none

/-! ## 锁表的小引理 -/

theorem not_locked {ps : Locks} {x p z : Var}
    (h : locked ps x = false) (hm : (p, z) ∈ ps) : z ≠ x := by
  intro hzx
  have : locked ps x = true := List.any_eq_true.mpr ⟨(p, z), hm, by simp [hzx]⟩
  rw [h] at this
  contradiction

theorem not_active {ps : Locks} {p q z : Var}
    (h : active ps p = false) (hm : (q, z) ∈ ps) : q ≠ p := by
  intro hqp
  have : active ps p = true := List.any_eq_true.mpr ⟨(q, z), hm, by simp [hqp]⟩
  rw [h] at this
  contradiction

theorem active_mem {ps : Locks} {p : Var} (h : active ps p = true) : ∃ z, (p, z) ∈ ps := by
  obtain ⟨⟨q, z⟩, hm, hq⟩ := List.any_eq_true.mp h
  simp at hq
  subst hq
  exact ⟨z, hm⟩

theorem baseOk_src {ps : Locks} {t : Stmt} {p z : Var}
    (hok : baseOk ps t = true) (hm : (p, z) ∈ ps) : src t ≠ some z := by
  intro h
  have hl : locked ps z = false := by
    simp only [baseOk, h] at hok
    cases hl : locked ps z
    · rfl
    · simp [hl] at hok
  exact not_locked hl hm rfl

/-! ## 基本语句不碰被锁定的变量 -/

/-- 静态上：`yes` 的变量只要不是语句的来源，语句之后仍是 `yes`。 -/
theorem checkS_keep {σ σ' : SEnv} {t : Stmt} {z : Var}
    (hc : checkS σ t = some σ') (hz : σ z = .yes) (hs : src t ≠ some z) :
    σ' z = .yes := by
  cases t with
  | alloc x =>
    simp only [checkS] at hc
    split at hc
    · rename_i hx
      cases hc
      have hzx : z ≠ x := by intro h; rw [h, hx] at hz; cases hz
      simp [upd, hzx, hz]
    · contradiction
  | move x y =>
    simp only [checkS] at hc
    split at hc
    · contradiction
    · split at hc
      · split at hc
        · rename_i hy
          cases hc
          have hzx : z ≠ x := by intro h; rw [h] at hs; exact hs rfl
          have hzy : z ≠ y := by intro h; rw [h, hy] at hz; cases hz
          simp [upd, hzx, hzy, hz]
        · contradiction
      · contradiction
  | use x =>
    simp only [checkS] at hc
    split at hc
    · cases hc; exact hz
    · contradiction
  | free x =>
    simp only [checkS] at hc
    split at hc
    · cases hc
      have hzx : z ≠ x := by intro h; rw [h] at hs; exact hs rfl
      simp [upd, hzx, hz]
    · contradiction

/-- 静态上：`yes` 的变量不会是语句的目标（目标必须是 `no`）。 -/
theorem yes_not_tgt {σ σ' : SEnv} {t : Stmt} {z : Var}
    (hc : checkS σ t = some σ') (hz : σ z = .yes) : tgt t ≠ some z := by
  cases t with
  | alloc x =>
    simp only [checkS] at hc
    split at hc
    · rename_i hx
      intro h
      simp only [tgt, Option.some.injEq] at h
      rw [← h, hx] at hz
      cases hz
    · contradiction
  | move x y =>
    simp only [checkS] at hc
    split at hc
    · contradiction
    · split at hc
      · split at hc
        · rename_i hy
          intro h
          simp only [tgt, Option.some.injEq] at h
          rw [← h, hy] at hz
          cases hz
        · contradiction
      · contradiction
  | use x => simp [tgt]
  | free x => simp [tgt]

/-- 动态上：不是目标的变量，指针不变。 -/
theorem execS_frame {s s' : Core.M2b.St} {t : Stmt} {z : Var}
    (he : execS s t = some s') (hz : tgt t ≠ some z) : s'.env z = s.env z := by
  cases t with
  | alloc x =>
    simp only [execS] at he
    cases he
    have hzx : z ≠ x := by intro h; rw [h] at hz; exact hz rfl
    simp [Core.M2b.allocOp, upd, hzx]
  | move x y =>
    simp only [execS] at he
    split at he
    · split at he
      · cases he
        have hzy : z ≠ y := by intro h; rw [h] at hz; exact hz rfl
        simp [Core.M2b.moveOp, upd, hzy]
      · contradiction
    · contradiction
  | use x =>
    simp only [execS] at he
    split at he
    · split at he
      · cases he; rfl
      · contradiction
    · contradiction
  | free x =>
    simp only [execS] at he
    split at he
    · split at he
      · cases he; rfl
      · contradiction
    · contradiction

/-! ## 不变式与单步 -/

structure Good (N : Nat) (σ : SEnv) (ps : Locks) (s : St4) : Prop where
  compat : Compat σ s.b.flag
  dinv   : DInv N s.b
  /-- 锁表里的每一项：源对象静态上是 `yes`，投影和源对象指向同一个位置。 -/
  pinv   : ∀ p z, (p, z) ∈ ps → σ z = .yes ∧ s.pr p = s.b.env z

theorem good_empty (N : Nat) : Good N (fun _ => .no) [] St4.empty :=
  ⟨compat_empty, dinv_empty N, by intro p z h; cases h⟩

theorem step1 {N : Nat} {σ σ' : SEnv} {ps ps' : Locks} {s : St4} {c : Cmd}
    (hc : check1 N σ ps c = some (σ', ps')) (hg : Good N σ ps s) :
    ∃ s', exec1 s c = some s' ∧ Good N σ' ps' s' := by
  cases c with
  | base t =>
    simp only [check1] at hc
    split at hc
    · rename_i hok
      split at hc
      · rename_i σ₁ h₁
        cases hc
        simp only [Core.M2b.checkStmtV] at h₁
        split at h₁
        · rename_i hv
          obtain ⟨b', he, hc', hd'⟩ := stepS hv h₁ hg.compat hg.dinv
          refine ⟨⟨b', s.pr⟩, by simp [exec1, he], ⟨hc', hd', ?_⟩⟩
          intro p z hm
          obtain ⟨hz, hpz⟩ := hg.pinv p z hm
          refine ⟨checkS_keep h₁ hz (baseOk_src hok hm), ?_⟩
          show s.pr p = b'.env z
          rw [execS_frame he (yes_not_tgt h₁ hz)]
          exact hpz
        · contradiction
      · contradiction
    · contradiction
  | proj p x =>
    simp only [check1] at hc
    split at hc
    · rename_i hpx
      obtain ⟨hx, hpa⟩ := hpx
      cases hc
      obtain ⟨l, hl, hlive⟩ := hg.dinv.owned_live x (hg.compat.yes x hx)
      refine ⟨⟨s.b, upd s.pr p (some l)⟩, by simp [exec1, hl, hlive],
        ⟨hg.compat, hg.dinv, ?_⟩⟩
      intro q z hm
      rcases List.mem_cons.mp hm with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hx, by simp [hl]⟩
      · obtain ⟨hz, hqz⟩ := hg.pinv q z h
        have hqp : q ≠ p := not_active hpa h
        exact ⟨hz, by simp [upd, hqp, hqz]⟩
    · contradiction
  | readp p =>
    simp only [check1] at hc
    split at hc
    · rename_i hpa
      cases hc
      obtain ⟨z, hm⟩ := active_mem hpa
      obtain ⟨hz, hpz⟩ := hg.pinv p z hm
      obtain ⟨l, hl, hlive⟩ := hg.dinv.owned_live z (hg.compat.yes z hz)
      exact ⟨s, by simp [exec1, hpz, hl, hlive], hg⟩
    · contradiction
  | endp p =>
    simp only [check1] at hc
    split at hc
    · cases hc
      refine ⟨⟨s.b, upd s.pr p none⟩, by simp [exec1], ⟨hg.compat, hg.dinv, ?_⟩⟩
      intro q z hm
      obtain ⟨hm0, hq⟩ := List.mem_filter.mp hm
      have hqp : q ≠ p := by simpa using hq
      obtain ⟨hz, hqz⟩ := hg.pinv q z hm0
      exact ⟨hz, by simp [upd, hqp, hqz]⟩
    · contradiction

theorem listSound4 (N : Nat) (cs : List Cmd) :
    ∀ {σ σ' : SEnv} {ps ps' : Locks} {s : St4},
      checkL N σ ps cs = some (σ', ps') → Good N σ ps s →
      ∃ s', execL s cs = some s' ∧ Good N σ' ps' s' := by
  induction cs with
  | nil =>
    intro σ σ' ps ps' s hc hg
    simp only [checkL, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨s, rfl, hg⟩
  | cons c cs ih =>
    intro σ σ' ps ps' s hc hg
    simp only [checkL] at hc
    split at hc
    · rename_i σ₁ ps₁ h₁
      obtain ⟨s₁, he₁, hg₁⟩ := step1 h₁ hg
      obtain ⟨s₂, he₂, hg₂⟩ := ih hc hg₁
      exact ⟨s₂, by simp only [execL, he₁, he₂], hg₂⟩
    · contradiction

/-! ## 主定理 -/

/-- **M4（一）主定理。** 检查器接受的程序执行不出错：每一次通过投影读取，
指向的位置都还活着；作用域结束时按 drop flag 释放，之后堆上没有活着的值。 -/
theorem safety_and_no_leak (N : Nat) (cs : List Cmd) (σ' : SEnv) (ps' : Locks)
    (h : checkL N (fun _ => .no) [] cs = some (σ', ps')) :
    ∃ b, (execL St4.empty cs).bind (fun s => dropAll s.b N) = some b ∧
      ∀ l, b.live l = false := by
  obtain ⟨s₁, he₁, hg₁⟩ := listSound4 N cs h (good_empty N)
  obtain ⟨b₂, he₂, hd₂, hf₂⟩ := dropAll_sound hg₁.dinv N
  refine ⟨b₂, by rw [he₁]; exact he₂, ?_⟩
  intro l
  cases hl : b₂.live l with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨x, hx, _⟩ := hd₂.live_owned l hl
    have hxN := hd₂.bound x hx
    rw [hf₂ x hxN] at hx
    contradiction

/-! ## 例子（投影名用 5，不占用拥有者变量的编号） -/

/-- `let p = proj x.f; read p; (p 结束); free x`：接受。 -/
def ok1 : List Cmd := [.base (.alloc 0), .proj 5 0, .readp 5, .endp 5, .base (.free 0)]
example : (checkL 2 (fun _ => .no) [] ok1).isSome = true := rfl

/-- 投影存在期间只读使用源对象：接受；投影结束后再移走源对象：接受。 -/
def ok2 : List Cmd :=
  [.base (.alloc 0), .proj 5 0, .base (.use 0), .readp 5, .endp 5, .base (.move 0 1)]
example : (checkL 2 (fun _ => .no) [] ok2).isSome = true := rfl

/-- 投影还在时释放源对象：拒绝。 -/
def bad1 : List Cmd := [.base (.alloc 0), .proj 5 0, .base (.free 0), .readp 5]
example : (checkL 2 (fun _ => .no) [] bad1).isNone = true := rfl

/-- 投影还在时移走源对象：拒绝。 -/
def bad2 : List Cmd := [.base (.alloc 0), .proj 5 0, .base (.move 0 1), .readp 5]
example : (checkL 2 (fun _ => .no) [] bad2).isNone = true := rfl

/-- 投影结束后不能再通过它读：拒绝。 -/
def bad3 : List Cmd := [.base (.alloc 0), .proj 5 0, .endp 5, .readp 5]
example : (checkL 2 (fun _ => .no) [] bad3).isNone = true := rfl

/-- 不经检查直接执行 `bad1`：通过投影读到了已释放的内存，执行出错。
说明安全性来自检查器，而不是语义本身保守。 -/
example : (execL St4.empty bad1).isNone = true := rfl

end Core.M4
