/-!
# M21：闭包（只能当实参传，可以读、改外面的变量）

闭包 `|x| …` 只能写在实参的位置，传给类型是 `fn(T) -> U` 的参数；不能存进变量、字段、Vec，也不能返回
（second-class）。闭包里用到的外面的变量叫捕获：只读的按 `let` 捕获，赋值或作 `inout` 实参的按 `inout` 捕获。

## 一、排他性：调用处检查一次就够
调用 `h(a₁, …, aₙ, |x| …)` 时，把捕获当成额外的实参，和 `a₁ … aₙ` 一起按 M3n 的规则检查：
两个重叠的位置必须都是 `let`。被调函数 `h` 看不到捕获，它调用闭包 `f(y₁, …)` 或把 `f` 再传给别的函数时，
实参 `yᵢ` 要么是 `h` 自己的局部值（和捕获不重叠），要么来自 `h` 的参数里面的位置（`let` 参数只能按 `let` 传下去）。
`inner_ok`：这时 `yᵢ` 和捕获合在一起仍满足同一条规则——所以闭包的函数体可以当作以捕获和 `yᵢ` 为参数的普通函数检查，
往下传多少层都一样（每一层都是 `inner_ok` 的前提）。

## 二、不会悬空：闭包引用的栈帧一定还活着
闭包里存的是创建它的那个栈帧（捕获的变量在那里）。闭包只能出现在调用的实参里，不能存、不能返回，
于是每个栈帧里的闭包引用的都是更早（更靠下）的帧（`Good`）。`good_reach`：从空栈出发经过调用、
赋值、返回始终成立；`clo_live`：调用闭包时它的帧还在栈上；`pop_clean`：一个帧返回之后，没有任何地方还引用它。
-/

namespace Core.M21

/-! ## 一、排他性 -/

inductive Mode | let_ | inout
  deriving DecidableEq

structure Arg (P : Type) where
  loc : P
  mode : Mode

/-- 位置之间的关系：`ov` 重叠；`sub a b`：`a` 是 `b` 本身或者 `b` 里面的位置（字段、元素、解引用）。 -/
structure Places (P : Type) where
  ov : P → P → Prop
  sub : P → P → Prop
  symm : ∀ a b, ov a b → ov b a
  sub_ov : ∀ a b c, sub a b → ov c a → ov c b

variable {P : Type} (S : Places P)

/-- M3n 的规则：两个实参的位置重叠时都必须是 `let`。 -/
def Compat (a b : Arg P) : Prop := S.ov a.loc b.loc → a.mode = .let_ ∧ b.mode = .let_

def Ok (as : List (Arg P)) : Prop := as.Pairwise (Compat S)

/-- 被调函数里的实参 `y` 的来源：自己的局部值（和捕获不重叠），或者来自参数 `a` 里面的位置，且不把 `let` 升成 `inout`。 -/
def Derived (args caps : List (Arg P)) (y : Arg P) : Prop :=
  (∀ c ∈ caps, ¬ S.ov y.loc c.loc) ∨
  ∃ a ∈ args, S.sub y.loc a.loc ∧ (y.mode = .inout → a.mode = .inout)

theorem inner_ok {args caps ys : List (Arg P)} (h : Ok S (args ++ caps)) (hy : Ok S ys)
    (hd : ∀ y ∈ ys, Derived S args caps y) : Ok S (ys ++ caps) := by
  unfold Ok at *
  rw [List.pairwise_append] at h ⊢
  obtain ⟨_, hc, hx⟩ := h
  refine ⟨hy, hc, fun y hy' c hc' hov => ?_⟩
  rcases hd y hy' with hf | ⟨a, ha, hs, hm⟩
  · exact absurd hov (hf c hc')
  · have hac : S.ov a.loc c.loc := S.symm _ _ (S.sub_ov _ _ _ hs (S.symm _ _ hov))
    obtain ⟨h1, h2⟩ := hx a ha c hc' hac
    refine ⟨?_, h2⟩
    cases e : y.mode with
    | let_ => rfl
    | inout => rw [hm e] at h1; cases h1

/-- 往下传一层：`h` 把闭包和实参 `ys` 交给 `g`，`g` 再用 `zs` 调闭包，`inner_ok` 用两次。 -/
theorem two_levels {args caps ys zs : List (Arg P)} (h : Ok S (args ++ caps)) (hy : Ok S ys)
    (hdy : ∀ y ∈ ys, Derived S args caps y) (hz : Ok S zs) (hdz : ∀ z ∈ zs, Derived S ys caps z) :
    Ok S (zs ++ caps) :=
  inner_ok S (inner_ok S h hy hdy) hz hdz

/-! ### 例子：位置是变量的编号，重叠就是同一个变量（v 是 0，total 是 1） -/

def names : Places Nat where
  ov a b := a = b
  sub a b := a = b
  symm _ _ h := h.symm
  sub_ov _ _ _ h1 h2 := h1 ▸ h2

instance : DecidableRel (Compat names) := fun a b =>
  inferInstanceAs (Decidable (a.loc = b.loc → a.mode = .let_ ∧ b.mode = .let_))

-- vec.for_each(v, |x| { total = total + x })：v 按 let 传，闭包按 inout 捕获 total，接受
example : Ok names [⟨0, .let_⟩, ⟨1, .inout⟩] := by unfold Ok; decide
-- vec.for_each(v, |x| { v.push(x) })：闭包按 inout 捕获 v，和实参 v 重叠，拒绝
example : ¬ Ok names [⟨0, .let_⟩, ⟨0, .inout⟩] := by unfold Ok; decide

/-! ## 二、不会悬空 -/

/-- 值：数（代表所有不是闭包的值）或闭包（记下它的栈帧的编号，栈底是 0）。 -/
inductive Val
  | num (n : Nat)
  | clo (frame : Nat)

/-- 栈，栈顶在前；栈顶帧的编号是下面的帧数。 -/
abbrev Stack := List (List Val)

/-- 每个帧里的闭包引用的都是更靠下的帧。 -/
def Good : Stack → Prop
  | [] => True
  | f :: rest => (∀ j, Val.clo j ∈ f → j < rest.length) ∧ Good rest

/-- 调用：实参是数，或当前帧（编号 `s.length - 1`）新建的闭包，或当前帧的参数里的闭包——都满足 `j < s.length`。
    赋值：只能存数（闭包不能存进变量）。返回：只能返回数（闭包不能返回），放进调用者的帧。 -/
inductive Step : Stack → Stack → Prop
  | call (s : Stack) (args : List Val) : (∀ j, Val.clo j ∈ args → j < s.length) → Step s (args :: s)
  | store (f : List Val) (rest : Stack) (n : Nat) : Step (f :: rest) ((f ++ [.num n]) :: rest)
  | ret (top f : List Val) (rest : Stack) (n : Nat) : Step (top :: f :: rest) ((f ++ [.num n]) :: rest)

inductive Reach : Stack → Prop
  | start : Reach [[]]
  | step {s t : Stack} : Reach s → Step s t → Reach t

theorem step_good {s t : Stack} (hs : Good s) (st : Step s t) : Good t := by
  cases st with
  | call _ args h => exact ⟨h, hs⟩
  | store f rest n =>
    refine ⟨fun j hj => ?_, hs.2⟩
    rcases List.mem_append.1 hj with hj | hj
    · exact hs.1 j hj
    · simp at hj
  | ret top f rest n =>
    obtain ⟨_, hf, hr⟩ := hs
    refine ⟨fun j hj => ?_, hr⟩
    rcases List.mem_append.1 hj with hj | hj
    · exact hf j hj
    · simp at hj

theorem good_reach {s : Stack} (h : Reach s) : Good s := by
  induction h with
  | start => exact ⟨fun j hj => by simp at hj, trivial⟩
  | step _ st ih => exact step_good ih st

/-- 下面的帧里的闭包引用的帧编号都小于下面的帧数。 -/
theorem below : ∀ {rest : Stack}, Good rest → ∀ f ∈ rest, ∀ j, Val.clo j ∈ f → j < rest.length
  | [], _, f, hf, _, _ => by simp at hf
  | g :: r, ⟨hg, hr⟩, f, hf, j, hj => by
    rcases List.mem_cons.1 hf with e | e
    · subst e
      have := hg j hj
      simp only [List.length_cons]
      omega
    · have := below hr f e j hj
      simp only [List.length_cons]
      omega

/-- 调用闭包时，它的帧还在栈上（编号小于栈顶帧的编号）。 -/
theorem clo_live {top : List Val} {rest : Stack} (h : Reach (top :: rest)) {j : Nat}
    (hj : Val.clo j ∈ top) : j < rest.length :=
  (good_reach h).1 j hj

/-- 栈顶的帧返回之后，剩下的帧里没有引用它的闭包。 -/
theorem pop_clean {top : List Val} {rest : Stack} (h : Reach (top :: rest)) :
    ∀ f ∈ rest, Val.clo rest.length ∉ f := by
  intro f hf hc
  have := below (good_reach h).2 f hf _ hc
  omega

/-! ### 反例：如果允许返回闭包，返回后会留下引用已弹出帧的闭包 -/

def badRet : Stack := [[.clo 1]]   -- 帧 1 返回了自己新建的闭包，存进帧 0

example : ¬ Good badRet := by
  intro h
  have := h.1 1 (by simp)
  simp at this

end Core.M21
