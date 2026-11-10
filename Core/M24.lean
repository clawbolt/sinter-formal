/-!
# M24：嵌套模式

C55 允许模式嵌套：`.Some((x, .Cons(y)))`、`(0, _)`、`.Ok(.None)`。模式是 `_`、变量、字面量、变体（可以带一个子模式）、
元组（这里用二元组代表，n 元组的每个分量都按同样的方式处理）。语义：从上到下第一个匹配的分支，
绑定它的各个变量（`select`）。

编译器把带嵌套模式的 `match` 展开成已有的构造，分两步：

1. **测试**（`test`）：按借用（`match let`、`==`）检查值是否匹配一个分支的模式，不移动任何东西。
   前面的分支依次测试，第一个通过的被选中；最后一个分支不测试。
2. **取出**（`extract`）：只对选中的分支按移动拆开（`match`、拆开元组），把各个变量绑定上。
   字面量不再比较；标签不对的位置写成 `panic`，展开后的程序里这些位置走不到。

**定理**：
- `test_eq`：测试的结果就是“模式匹配”（`pmatch` 有结果）；
- `extract_of_pmatch`：匹配时取出的绑定和 `pmatch` 给出的一样；
- `run_correct`：只要有分支匹配（覆盖性检查保证，M24b），展开后的代码选中的分支和绑定就是 `select` 的结果，
  不会走到 `panic`。

所有权不需要新的推理：第一步只借用，第二步是已有的按移动 `match`、拆开元组，由已有的检查和翻译验证负责。
-/

namespace Core.M24

inductive Val
  | lit (n : Int)
  | tag0 (i : Nat)
  | tag1 (i : Nat) (v : Val)
  | pair (a b : Val)
  deriving DecidableEq, Repr

inductive Pat
  | wild
  | bind (x : Nat)
  | lit (n : Int)
  | tag0 (i : Nat)
  | tag1 (i : Nat) (p : Pat)
  | pair (p q : Pat)
  deriving DecidableEq, Repr

/-- 绑定：变量和它得到的值，从左到右。 -/
abbrev Binds := List (Nat × Val)

def ok (b : Bool) (x : Option Binds) : Option Binds := if b then x else none

def both : Option Binds → Option Binds → Option Binds
  | some a, some b => some (a ++ b)
  | _, _ => none

theorem isSome_ok (b : Bool) (x : Option Binds) : (ok b x).isSome = (b && x.isSome) := by
  cases b <;> simp [ok]

theorem isSome_both (a b : Option Binds) : (both a b).isSome = (a.isSome && b.isSome) := by
  cases a <;> cases b <;> simp [both]

theorem ok_some {b : Bool} {x : Option Binds} {l : Binds} : ok b x = some l ↔ b = true ∧ x = some l := by
  cases b <;> simp [ok]

theorem both_some {a b : Option Binds} {l : Binds} (h : both a b = some l) :
    ∃ l1 l2, a = some l1 ∧ b = some l2 ∧ l = l1 ++ l2 :=
  match a, b, h with
  | some x, some y, h => by
    simp only [both, Option.some.injEq] at h
    exact ⟨x, y, rfl, rfl, h.symm⟩
  | none, _, h => by simp [both] at h
  | some _, none, h => by simp [both] at h

/-- 语义：模式匹配值时的绑定。 -/
def pmatch : Pat → Val → Option Binds
  | .wild, _ => some []
  | .bind x, v => some [(x, v)]
  | .lit n, .lit m => ok (n == m) (some [])
  | .tag0 i, .tag0 j => ok (i == j) (some [])
  | .tag1 i p, .tag1 j v => ok (i == j) (pmatch p v)
  | .pair p q, .pair a b => both (pmatch p a) (pmatch q b)
  | _, _ => none

/-- 第一步：按借用测试。 -/
def test : Pat → Val → Bool
  | .wild, _ => true
  | .bind _, _ => true
  | .lit n, .lit m => n == m
  | .tag0 i, .tag0 j => i == j
  | .tag1 i p, .tag1 j v => i == j && test p v
  | .pair p q, .pair a b => test p a && test q b
  | _, _ => false

/-- 第二步：按移动取出。字面量不再比较；标签不对时 `panic`（这里是 `none`）。 -/
def extract : Pat → Val → Option Binds
  | .wild, _ => some []
  | .bind x, v => some [(x, v)]
  | .lit _, _ => some []
  | .tag0 i, .tag0 j => ok (i == j) (some [])
  | .tag1 i p, .tag1 j v => ok (i == j) (extract p v)
  | .pair p q, .pair a b => both (extract p a) (extract q b)
  | _, _ => none

theorem test_eq : ∀ (p : Pat) (v : Val), test p v = (pmatch p v).isSome
  | .wild, _ => by simp [test, pmatch]
  | .bind _, _ => by simp [test, pmatch]
  | .lit _, v => by cases v <;> simp [test, pmatch, isSome_ok]
  | .tag0 _, v => by cases v <;> simp [test, pmatch, isSome_ok]
  | .tag1 _ p, v => by cases v <;> simp [test, pmatch, isSome_ok, test_eq p]
  | .pair p q, v => by cases v <;> simp [test, pmatch, isSome_both, test_eq p, test_eq q]

theorem extract_of_pmatch : ∀ (p : Pat) (v : Val) (l : Binds), pmatch p v = some l → extract p v = some l
  | .wild, _, _, h => by simpa [pmatch, extract] using h
  | .bind _, _, _, h => by simpa [pmatch, extract] using h
  | .lit _, v, _, h => by cases v <;> simp_all [pmatch, extract, ok]
  | .tag0 _, v, _, h => by cases v <;> simp_all [pmatch, extract, ok]
  | .tag1 i p, v, l, h => by
    cases v
    · simp [pmatch] at h
    · simp [pmatch] at h
    · rename_i j w
      simp only [pmatch, extract] at h ⊢
      obtain ⟨e, h2⟩ := ok_some.1 h
      rw [extract_of_pmatch p w l h2]
      simp [ok, e]
    · simp [pmatch] at h
  | .pair p q, v, l, h => by
    cases v
    · simp [pmatch] at h
    · simp [pmatch] at h
    · simp [pmatch] at h
    · rename_i a b
      simp only [pmatch, extract] at h ⊢
      obtain ⟨l1, l2, h1, h2, e⟩ := both_some h
      rw [extract_of_pmatch p a l1 h1, extract_of_pmatch q b l2 h2, e]
      rfl

/-! ## 分支 -/

/-- 分支：模式和分支体的编号。 -/
abbrev Arm := Pat × Nat

/-- 语义：第一个匹配的分支和它的绑定。 -/
def select : List Arm → Val → Option (Nat × Binds)
  | [], _ => none
  | (p, b) :: as, v =>
    match pmatch p v with
    | some l => some (b, l)
    | none => select as v

/-- 展开后的代码：前面的分支先测试，通过的取出；最后一个分支不测试，直接取出。 -/
def run : Arm → List Arm → Val → Option (Nat × Binds)
  | (p, b), [], v => (extract p v).map (fun l => (b, l))
  | (p, b), a :: as, v => if test p v then (extract p v).map (fun l => (b, l)) else run a as v

/-- **有分支匹配时，展开后的代码和语义一致**（选中同一个分支、同样的绑定，不走到 `panic`）。 -/
theorem run_correct : ∀ (a : Arm) (as : List Arm) (v : Val),
    (select (a :: as) v).isSome = true → run a as v = select (a :: as) v
  | (p, b), [], v, h => by
    cases hm : pmatch p v with
    | none => simp [select, hm] at h
    | some l => simp [select, run, hm, extract_of_pmatch p v l hm]
  | (p, b), a :: as, v, h => by
    by_cases ht : test p v = true
    · have hs : (pmatch p v).isSome = true := by rw [← test_eq]; exact ht
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hs
      simp [run, ht, select, hl, extract_of_pmatch p v l hl]
    · have hn : pmatch p v = none := by
        rw [test_eq] at ht
        simpa using ht
      have h' : (select (a :: as) v).isSome = true := by simpa [select, hn] using h
      have e : run (p, b) (a :: as) v = run a as v := by simp [run, ht]
      have e2 : select ((p, b) :: a :: as) v = select (a :: as) v := by simp [select, hn]
      rw [e, e2]
      exact run_correct a as v h'

/-! ## 例子

`enum List { Cons((I64, List)), Nil }`：`Cons` 是 0 号变体、`Nil` 是 1 号。 -/

def cons (n : Int) (rest : Val) : Val := .tag1 0 (.pair (.lit n) rest)
def nil : Val := .tag0 1

/-- `match l { .Cons((x, .Cons((y, _)))) => 0, .Cons((x, rest)) => 1, .Nil => 2 }`，变量 x=0、y=1、rest=2。 -/
def arm0 : Arm := (.tag1 0 (.pair (.bind 0) (.tag1 0 (.pair (.bind 1) .wild))), 0)

def arms : List Arm :=
  [(.tag1 0 (.pair (.bind 0) (.tag1 0 (.pair (.bind 1) .wild))), 0),
   (.tag1 0 (.pair (.bind 0) (.bind 2)), 1),
   (.tag0 1, 2)]

example : select arms (cons 1 (cons 2 nil)) = some (0, [(0, .lit 1), (1, .lit 2)]) := by decide
example : select arms (cons 1 nil) = some (1, [(0, .lit 1), (2, nil)]) := by decide
example : run arm0 (arms.drop 1) (cons 1 nil) = select arms (cons 1 nil) := by decide
example : run arm0 (arms.drop 1) nil = some (2, []) := by decide

end Core.M24
