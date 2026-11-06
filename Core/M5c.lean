import Core.M5
import Core.M4

/-!
# M5（三）：D4，区域里不放带 `Drop` / `linear` 的值

区域结束时整块归还，**不运行析构**。如果区域里放了一个拥有堆内存的值（带 `Drop`），
这块堆内存就再也没人释放，泄漏了。D4 因此规定：分配进区域的类型不能带 `Drop` 或 `linear`。

**模型**：在 M5（一）上加入拥有堆内存的变量（和 M1、M2 相同）：
- `hnew x`：分配一块堆内存，`x` 拥有它；
- `hfree x`：释放 `x` 拥有的堆内存；
- `rstore x k`：把 `x` 拥有的值移进区域 `k`（区域结束时不会释放它）。

**静态检查**：拥有者表 `o` 记录每个拥有者和它的作用域深度。
- 拥有者离开作用域之前必须已经释放（块结束时检查）；
- D4 规则（`D4Rule.d4`）下，`rstore` 一律拒绝；
- 违反 D4 的规则（`D4Rule.noD4`）下，`rstore` 被接受，`x` 不再是拥有者。

**主定理** `safety_and_no_leak`：D4 规则下，检查器接受、并且结束时没有拥有者的程序，
执行不出错，结束时既没有区域残留，也没有堆内存残留。

**反例** `leak`：违反 D4 的规则接受它，执行结束时堆上仍有活着的内存。
-/

namespace Core.M5c
open Core.M5 (REnv restrict St5 enterR leaveR enter_good leave_good)
open Core.M4 (Locks active not_active active_mem)

inductive Cmd
  | base   (c : Core.M5.Cmd5)
  | hnew   (x : Var)
  | hfree  (x : Var)
  | rstore (x : Var) (k : Nat)

inductive P
  | skip
  | cmd   (c : Cmd)
  | seq   (p q : P)
  | block (p : P)

inductive D4Rule | d4 | noD4

/-! ## 静态检查（拥有者表复用 M4 的 `Locks`：`(变量, 作用域深度)`） -/

def check1 (m : D4Rule) (d : Nat) (σ : REnv) (o : Locks) : Cmd → Option (REnv × Locks)
  | .base c =>
    match Core.M5.check1 d σ c with
    | some σ' => some (σ', o)
    | none    => none
  | .hnew x => if active o x = false then some (σ, (x, d) :: o) else none
  | .hfree x =>
    if active o x = true then some (σ, o.filter (fun e => e.1 != x)) else none
  | .rstore x k =>
    match m with
    | .d4     => none
    | .noD4 =>
      if active o x = true ∧ k < d then some (σ, o.filter (fun e => e.1 != x)) else none

def check (m : D4Rule) : P → Nat → REnv → Locks → Option (REnv × Locks)
  | .skip,    _, σ, o => some (σ, o)
  | .cmd c,   d, σ, o => check1 m d σ o c
  | .seq p q, d, σ, o =>
    match check m p d σ o with
    | some (σ₁, o₁) => check m q d σ₁ o₁
    | none          => none
  | .block p, d, σ, o =>
    match check m p (d + 1) σ o with
    | some (σ₁, o₁) =>
      if o₁.all (fun e => decide (e.2 ≤ d)) = true then some (restrict d σ₁, o₁) else none
    | none => none

/-! ## 动态语义 -/

structure Heap where
  ptr  : Var → Option Nat
  live : Nat → Bool
  next : Nat

structure St where
  r : St5
  h : Heap

def St.empty : St := ⟨St5.empty, ⟨fun _ => none, fun _ => false, 0⟩⟩

def exec1 (s : St) : Cmd → Option St
  | .base c =>
    match Core.M5.exec1 s.r c with
    | some r' => some ⟨r', s.h⟩
    | none    => none
  | .hnew x =>
    some ⟨s.r, ⟨upd s.h.ptr x (some s.h.next), upd s.h.live s.h.next true, s.h.next + 1⟩⟩
  | .hfree x =>
    match s.h.ptr x with
    | some l => if s.h.live l = true then some ⟨s.r, { s.h with live := upd s.h.live l false }⟩
                else none
    | none   => none
  | .rstore _ _ => some s   -- 区域接管这个值；区域结束时不运行析构

def exec : P → St → Option St
  | .skip,    s => some s
  | .cmd c,   s => exec1 s c
  | .seq p q, s =>
    match exec p s with
    | some s₁ => exec q s₁
    | none    => none
  | .block p, s =>
    match exec p ⟨⟨s.r.ptr, enterR s.r.rs⟩, s.h⟩ with
    | some s₁ => some ⟨⟨s₁.r.ptr, leaveR s₁.r.rs s.r.rs.d⟩, s₁.h⟩
    | none    => none

/-! ## 堆的不变式 -/

structure HInv (o : Locks) (h : Heap) : Prop where
  owned : ∀ x dx, (x, dx) ∈ o → ∃ l, h.ptr x = some l ∧ h.live l = true
  uniq  : ∀ x dx y dy l, (x, dx) ∈ o → (y, dy) ∈ o → h.ptr x = some l → h.ptr y = some l → x = y
  fresh : ∀ x dx l, (x, dx) ∈ o → h.ptr x = some l → l < h.next
  only  : ∀ l, h.live l = true → ∃ x dx, (x, dx) ∈ o ∧ h.ptr x = some l

theorem old_mem {o : Locks} {x d y dy : Var} (hm : (y, dy) ∈ (x, d) :: o) (hyx : y ≠ x) :
    (y, dy) ∈ o :=
  (List.mem_cons.mp hm).resolve_left (fun h1 => hyx (Prod.mk.inj h1).1)

theorem filt_mem {o : Locks} {x y dy : Var} (hm : (y, dy) ∈ o.filter (fun e => e.1 != x)) :
    (y, dy) ∈ o ∧ y ≠ x := by
  obtain ⟨hm0, hn⟩ := List.mem_filter.mp hm
  exact ⟨hm0, by simpa using hn⟩

theorem hnew_ok {o : Locks} {h : Heap} {x d : Var} (hi : HInv o h) (hx : active o x = false) :
    HInv ((x, d) :: o) ⟨upd h.ptr x (some h.next), upd h.live h.next true, h.next + 1⟩ := by
  constructor
  · intro y dy hm
    by_cases hyx : y = x
    · refine ⟨h.next, ?_, ?_⟩
      · show upd h.ptr x (some h.next) y = some h.next
        rw [hyx, upd_same]
      · show upd h.live h.next true h.next = true
        rw [upd_same]
    · have hm' := old_mem hm hyx
      obtain ⟨l, hl, hlv⟩ := hi.owned y dy hm'
      have hln : l ≠ h.next := Nat.ne_of_lt (hi.fresh y dy l hm' hl)
      refine ⟨l, ?_, ?_⟩
      · show upd h.ptr x (some h.next) y = some l
        rw [upd_other h.ptr (some h.next) hyx]
        exact hl
      · show upd h.live h.next true l = true
        rw [upd_other h.live true hln]
        exact hlv
  · intro a da b db l ha hb hpa hpb
    change upd h.ptr x (some h.next) a = some l at hpa
    change upd h.ptr x (some h.next) b = some l at hpb
    by_cases hax : a = x <;> by_cases hbx : b = x
    · rw [hax, hbx]
    · exfalso
      rw [hax, upd_same] at hpa
      rw [upd_other h.ptr (some h.next) hbx] at hpb
      cases hpa
      exact Nat.lt_irrefl _ (hi.fresh b db _ (old_mem hb hbx) hpb)
    · exfalso
      rw [hbx, upd_same] at hpb
      rw [upd_other h.ptr (some h.next) hax] at hpa
      cases hpb
      exact Nat.lt_irrefl _ (hi.fresh a da _ (old_mem ha hax) hpa)
    · rw [upd_other h.ptr (some h.next) hax] at hpa
      rw [upd_other h.ptr (some h.next) hbx] at hpb
      exact hi.uniq a da b db l (old_mem ha hax) (old_mem hb hbx) hpa hpb
  · intro y dy l hm hp
    change upd h.ptr x (some h.next) y = some l at hp
    show l < h.next + 1
    by_cases hyx : y = x
    · rw [hyx, upd_same] at hp
      cases hp
      exact Nat.lt_succ_self _
    · rw [upd_other h.ptr (some h.next) hyx] at hp
      exact Nat.lt_succ_of_lt (hi.fresh y dy l (old_mem hm hyx) hp)
  · intro l hl
    change upd h.live h.next true l = true at hl
    by_cases hln : l = h.next
    · refine ⟨x, d, by simp, ?_⟩
      show upd h.ptr x (some h.next) x = some l
      rw [upd_same, hln]
    · rw [upd_other h.live true hln] at hl
      obtain ⟨y, dy, hm, hp⟩ := hi.only l hl
      have hyx : y ≠ x := not_active hx hm
      refine ⟨y, dy, by simp [hm], ?_⟩
      show upd h.ptr x (some h.next) y = some l
      rw [upd_other h.ptr (some h.next) hyx]
      exact hp

theorem hfree_ok {o : Locks} {h : Heap} {x : Var} {l : Nat} (hi : HInv o h)
    (hx : active o x = true) (hl : h.ptr x = some l) :
    HInv (o.filter (fun e => e.1 != x)) { h with live := upd h.live l false } := by
  obtain ⟨dx, hxm⟩ := active_mem hx
  constructor
  · intro y dy hm
    obtain ⟨hm0, hyx⟩ := filt_mem hm
    obtain ⟨l', hl', hlv⟩ := hi.owned y dy hm0
    have hne : l' ≠ l := by
      intro he
      rw [he] at hl'
      exact hyx (hi.uniq y dy x dx l hm0 hxm hl' hl)
    refine ⟨l', hl', ?_⟩
    show upd h.live l false l' = true
    rw [upd_other h.live false hne]
    exact hlv
  · intro a da b db l' ha hb hpa hpb
    exact hi.uniq a da b db l' (filt_mem ha).1 (filt_mem hb).1 hpa hpb
  · intro y dy l' hm hp
    exact hi.fresh y dy l' (filt_mem hm).1 hp
  · intro l' hl'
    change upd h.live l false l' = true at hl'
    by_cases hll : l' = l
    · rw [hll, upd_same] at hl'
      cases hl'
    · rw [upd_other h.live false hll] at hl'
      obtain ⟨y, dy, hm, hp⟩ := hi.only l' hl'
      have hyx : y ≠ x := by
        intro he
        rw [he, hl] at hp
        cases hp
        exact hll rfl
      exact ⟨y, dy, List.mem_filter.mpr ⟨hm, by simp [hyx]⟩, hp⟩

/-! ## 单步与程序 -/

structure Good (d : Nat) (σ : REnv) (o : Locks) (s : St) : Prop where
  reg  : Core.M5.Good d σ s.r
  heap : HInv o s.h

theorem step1 {d : Nat} {σ σ' : REnv} {o o' : Locks} {s : St} {c : Cmd}
    (hc : check1 .d4 d σ o c = some (σ', o')) (hg : Good d σ o s) :
    ∃ s', exec1 s c = some s' ∧ Good d σ' o' s' := by
  cases c with
  | base c =>
    simp only [check1] at hc
    split at hc
    · rename_i σ₁ h₁
      cases hc
      obtain ⟨r', he, hg'⟩ := Core.M5.step1 h₁ hg.reg
      exact ⟨⟨r', s.h⟩, by simp [exec1, he], ⟨hg', hg.heap⟩⟩
    · contradiction
  | hnew x =>
    simp only [check1] at hc
    split at hc
    · rename_i hx
      cases hc
      exact ⟨_, rfl, ⟨hg.reg, hnew_ok hg.heap hx⟩⟩
    · contradiction
  | hfree x =>
    simp only [check1] at hc
    split at hc
    · rename_i hx
      cases hc
      obtain ⟨dx, hxm⟩ := active_mem hx
      obtain ⟨l, hl, hlv⟩ := hg.heap.owned x dx hxm
      exact ⟨⟨s.r, { s.h with live := upd s.h.live l false }⟩, by simp [exec1, hl, hlv],
        ⟨hg.reg, hfree_ok hg.heap hx hl⟩⟩
    · contradiction
  | rstore x k => simp [check1] at hc

theorem sound (p : P) : ∀ {d : Nat} {σ σ' : REnv} {o o' : Locks} {s : St},
    check .d4 p d σ o = some (σ', o') → Good d σ o s →
    ∃ s', exec p s = some s' ∧ Good d σ' o' s' := by
  induction p with
  | skip =>
    intro d σ σ' o o' s hc hg
    simp only [check] at hc
    cases hc
    exact ⟨s, rfl, hg⟩
  | cmd c =>
    intro d σ σ' o o' s hc hg
    exact step1 hc hg
  | seq p q ihp ihq =>
    intro d σ σ' o o' s hc hg
    simp only [check] at hc
    split at hc
    · rename_i σ₁ o₁ h₁
      obtain ⟨s₁, he₁, hg₁⟩ := ihp h₁ hg
      obtain ⟨s₂, he₂, hg₂⟩ := ihq hc hg₁
      exact ⟨s₂, by simp [exec, he₁, he₂], hg₂⟩
    · contradiction
  | block p ih =>
    intro d σ σ' o o' s hc hg
    simp only [check] at hc
    split at hc
    · rename_i σ₁ o₁ h₁
      split at hc
      · cases hc
        have hg0 : Good (d + 1) σ o ⟨⟨s.r.ptr, enterR s.r.rs⟩, s.h⟩ :=
          ⟨enter_good hg.reg, hg.heap⟩
        obtain ⟨s₁, he₁, hg₁⟩ := ih h₁ hg0
        refine ⟨⟨⟨s₁.r.ptr, leaveR s₁.r.rs s.r.rs.d⟩, s₁.h⟩, by simp [exec, he₁], ?_⟩
        rw [hg.reg.stk.depth]
        exact ⟨leave_good hg₁.reg, hg₁.heap⟩
      · contradiction
    · contradiction

/-! ## 主定理 -/

/-- **M5（三）主定理。** D4 规则下，检查器接受、并且结束时没有拥有者的程序，
执行不出错；结束时既没有区域残留，也没有堆内存残留。 -/
theorem safety_and_no_leak (p : P) (σ' : REnv)
    (h : check .d4 p 0 (fun _ => none) [] = some (σ', [])) :
    ∃ s', exec p St.empty = some s' ∧
      (∀ i, s'.r.rs.alive i = false) ∧ (∀ l, s'.h.live l = false) := by
  have g0 : Good 0 (fun _ => none) [] St.empty :=
    ⟨Core.M5.good_empty,
     ⟨(fun _ _ hm => by cases hm), (fun _ _ _ _ _ hm => by cases hm),
      (fun _ _ _ hm => by cases hm), (fun l hl => by simp [St.empty] at hl)⟩⟩
  obtain ⟨s', he, hg⟩ := sound p h g0
  refine ⟨s', he, ?_, ?_⟩
  · intro i
    cases hi : s'.r.rs.alive i with
    | false => rfl
    | true =>
      obtain ⟨k, hk, _⟩ := hg.reg.stk.only i hi
      exact absurd hk (Nat.not_lt_zero k)
  · intro l
    cases hl : s'.h.live l with
    | false => rfl
    | true =>
      obtain ⟨_, _, hm, _⟩ := hg.heap.only l hl
      cases hm

/-! ## 例子 -/

def seqL : List P → P
  | []      => .skip
  | p :: ps => .seq p (seqL ps)

/-- 区域里放普通数据，堆内存由变量拥有并在块内释放：接受。 -/
def ok1 : P := .block (seqL
  [.cmd (.base (.decl 0)), .cmd (.base (.ralloc 0 0)), .cmd (.hnew 1), .cmd (.hfree 1)])
example : (check .d4 ok1 0 (fun _ => none) []).isSome = true := rfl

/-- 拥有者离开作用域时还没释放：拒绝。 -/
def scopeLeak : P := .block (.cmd (.hnew 1))
example : (check .d4 scopeLeak 0 (fun _ => none) []).isNone = true := rfl

/-- 重复释放：拒绝。 -/
def twice : P := .block (seqL [.cmd (.hnew 1), .cmd (.hfree 1), .cmd (.hfree 1)])
example : (check .d4 twice 0 (fun _ => none) []).isNone = true := rfl

/-- 反例：把拥有堆内存的值移进区域。 -/
def leak : P := .block (seqL [.cmd (.hnew 1), .cmd (.rstore 1 0)])

/-- 违反 D4 的规则接受它，并且结束时没有拥有者…… -/
example : (check .noD4 leak 0 (fun _ => none) []).map (fun r => r.2) = some [] := rfl
/-- ……但执行结束时堆上仍有活着的内存：泄漏。 -/
example : (exec leak St.empty).map (fun s => s.h.live 0) = some true := rfl
/-- D4 规则拒绝它。 -/
example : (check .d4 leak 0 (fun _ => none) []).isNone = true := rfl

end Core.M5c
