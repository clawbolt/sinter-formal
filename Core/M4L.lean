import Core.M4

/-!
# M4（二）：活跃性（投影的锁定只持续到最后一次使用）

M4（一）里投影的结束点 `endp` 由程序显式写出。真实的源程序里没有这条语句：
编译器做一遍活跃性分析，在每个投影**最后一次使用之后**插入结束点（`ends`），
再交给 M4（一）的检查器。

这样做比“锁定到作用域结束”宽松：

```
let p = proj v.0
read p
move v        -- p 之后不再使用，锁已解除，接受
```

**要证明的**：结束点只是给检查器看的。真正运行的是没有结束点的源程序，
它在运行时会一直保留投影指针。主定理 `nll_safety` 说明：
只要插入结束点之后的程序通过检查，源程序本身执行就不出错，并且结束时没有泄漏。

证明分两步：
- `erase_ends`：插入结束点再擦掉，得到的就是原来的源程序。
- `sim_list`：带结束点的执行和擦掉结束点的执行，堆完全相同；
  前者手里的投影指针是后者的子集。所以前者不出错，后者也不出错。
-/

namespace Core.M4
open Core.M2b (SEnv dropAll dropAll_sound)

/-! ## 插入结束点 -/

/-- 一条语句用到了哪个投影。 -/
def uses : Cmd → Option Var
  | .proj p _ => some p
  | .readp p  => some p
  | _         => none

/-- 后面的语句还会不会用到投影 `p`。 -/
def mentions (p : Var) (cs : List Cmd) : Bool := cs.any (fun c => uses c == some p)

/-- 活跃性分析：在每个投影最后一次使用之后插入 `endp`。 -/
def ends : List Cmd → List Cmd
  | []      => []
  | c :: cs =>
    match uses c with
    | some p => if mentions p cs then c :: ends cs else c :: .endp p :: ends cs
    | none   => c :: ends cs

def isEnd : Cmd → Bool
  | .endp _ => true
  | _       => false

/-- 擦掉所有结束点，得到实际运行的程序。 -/
def erase : List Cmd → List Cmd
  | []      => []
  | c :: cs =>
    match c with
    | .endp _ => erase cs
    | _       => c :: erase cs

theorem erase_ends (cs : List Cmd) : erase (ends cs) = erase cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | base t => simp [ends, uses, erase, ih]
    | proj p x =>
      by_cases h : mentions p cs = true
      · simp [ends, uses, erase, h, ih]
      · simp [ends, uses, erase, h, ih]
    | readp p =>
      by_cases h : mentions p cs = true
      · simp [ends, uses, erase, h, ih]
      · simp [ends, uses, erase, h, ih]
    | endp p => simp [ends, uses, erase, ih]

/-! ## 模拟：擦掉结束点不会让执行出错 -/

/-- `s` 是带结束点的执行状态，`t` 是不带结束点的。堆相同，`s` 的投影指针 `t` 都有。 -/
structure Sim (s t : St4) : Prop where
  eqb : s.b = t.b
  sub : ∀ p l, s.pr p = some l → t.pr p = some l

theorem sim_end {s t s' : St4} {p : Var} (hs : Sim s t)
    (he : exec1 s (.endp p) = some s') : Sim s' t := by
  simp only [exec1, Option.some.injEq] at he
  subst he
  refine ⟨hs.eqb, ?_⟩
  intro q l hq
  by_cases hqp : q = p
  · subst hqp
    simp at hq
  · simp [upd, hqp] at hq
    exact hs.sub q l hq

theorem sim_step {s t s' : St4} {c : Cmd} (hs : Sim s t)
    (he : exec1 s c = some s') (hc : isEnd c = false) :
    ∃ t', exec1 t c = some t' ∧ Sim s' t' := by
  obtain ⟨hb, hpr⟩ := hs
  cases c with
  | base t0 =>
    simp only [exec1] at he
    split at he
    · rename_i b' h'
      cases he
      exact ⟨⟨b', t.pr⟩, by simp [exec1, ← hb, h'], ⟨rfl, hpr⟩⟩
    · contradiction
  | proj p x =>
    simp only [exec1] at he
    split at he
    · rename_i l hl
      split at he
      · rename_i hlive
        cases he
        refine ⟨⟨t.b, upd t.pr p (some l)⟩, by simp [exec1, ← hb, hl, hlive], ⟨hb, ?_⟩⟩
        intro q m hq
        by_cases hqp : q = p
        · subst hqp
          simpa using hq
        · simp [upd, hqp] at hq ⊢
          exact hpr q m hq
      · contradiction
    · contradiction
  | readp p =>
    simp only [exec1] at he
    split at he
    · rename_i l hl
      split at he
      · rename_i hlive
        cases he
        exact ⟨t, by simp [exec1, hpr p l hl, ← hb, hlive], ⟨hb, hpr⟩⟩
      · contradiction
    · contradiction
  | endp p => simp [isEnd] at hc

theorem sim_list (cs : List Cmd) :
    ∀ {s t s' : St4}, Sim s t → execL s cs = some s' →
      ∃ t', execL t (erase cs) = some t' ∧ Sim s' t' := by
  induction cs with
  | nil =>
    intro s t s' hs he
    simp only [execL, Option.some.injEq] at he
    subst he
    exact ⟨t, rfl, hs⟩
  | cons c cs ih =>
    intro s t s' hs he
    simp only [execL] at he
    split at he
    · rename_i s₁ h₁
      cases c
      case endp p =>
        obtain ⟨t', ht, hs'⟩ := ih (sim_end hs h₁) he
        exact ⟨t', by simpa [erase] using ht, hs'⟩
      all_goals
        obtain ⟨t₁, ht₁, hs₁⟩ := sim_step hs h₁ rfl
        obtain ⟨t₂, ht₂, hs₂⟩ := ih hs₁ he
        exact ⟨t₂, by simp only [erase, execL, ht₁, ht₂], hs₂⟩
    · contradiction

/-! ## 主定理 -/

/-- **M4（二）主定理。** 源程序 `cs` 里没有结束点。只要插入结束点后的程序通过
M4（一）的检查，源程序本身执行就不出错，作用域结束时按 drop flag 释放之后堆上没有活着的值。 -/
theorem nll_safety (N : Nat) (cs : List Cmd) (σ' : SEnv) (ps' : Locks)
    (hsrc : erase cs = cs)
    (h : checkL N (fun _ => .no) [] (ends cs) = some (σ', ps')) :
    ∃ s', execL St4.empty cs = some s' ∧
      ∃ b, dropAll s'.b N = some b ∧ ∀ l, b.live l = false := by
  obtain ⟨s₁, he₁, hg₁⟩ := listSound4 N (ends cs) h (good_empty N)
  obtain ⟨t, ht, hs⟩ := sim_list (ends cs) ⟨rfl, fun _ _ h => h⟩ he₁
  rw [erase_ends, hsrc] at ht
  obtain ⟨b, hb, hd, hf⟩ := dropAll_sound hg₁.dinv N
  refine ⟨t, ht, b, by rw [← hs.eqb]; exact hb, ?_⟩
  intro l
  cases hl : b.live l with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨x, hx, _⟩ := hd.live_owned l hl
    have hxN := hd.bound x hx
    rw [hf x hxN] at hx
    contradiction

/-! ## 例子 -/

/-- `let p = proj v.0; read p; move v`。 -/
def nll1 : List Cmd := [.base (.alloc 0), .proj 5 0, .readp 5, .base (.move 0 1)]

/-- 活跃性分析在最后一次读取之后插入结束点。 -/
example : ends nll1 =
    [.base (.alloc 0), .proj 5 0, .readp 5, .endp 5, .base (.move 0 1)] := rfl

/-- 如果锁一直持续到作用域结束，这个程序会被拒绝。 -/
example : (checkL 2 (fun _ => .no) [] nll1).isNone = true := rfl

/-- 按活跃性解锁：接受。 -/
example : (checkL 2 (fun _ => .no) [] (ends nll1)).isSome = true := rfl

/-- 移走 v 之后还要读 p：结束点落在读取之后，move 仍被拒绝。 -/
def nll2 : List Cmd := [.base (.alloc 0), .proj 5 0, .base (.move 0 1), .readp 5]
example : (checkL 2 (fun _ => .no) [] (ends nll2)).isNone = true := rfl

/-- 投影创建后从未使用：结束点紧跟在创建之后，释放源对象被接受。 -/
def nll3 : List Cmd := [.base (.alloc 0), .proj 5 0, .base (.free 0)]
example : (checkL 2 (fun _ => .no) [] (ends nll3)).isSome = true := rfl

end Core.M4
