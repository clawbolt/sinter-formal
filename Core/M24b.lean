import Core.M24

/-!
# M24b：嵌套模式的覆盖性检查

M24 的 `run_correct` 要求“有分支匹配”。编译器用下面的检查保证这一点，并找出永远匹配不到的分支：

- 收集所有分支里的字面量 `L`，再取一个不在 `L` 里的字面量 `fresh`（代表“其他所有字面量”）；
- `d` 是模式的最大深度；`reps d t`：类型 `t` 的代表值——每个变体、每种元组组合、`L` 里的字面量和 `fresh`，
  深度用完的地方是“任意值”`any`（只有 `_` 和变量能匹配它）；
- **穷尽**（`exhaustive`）：每个代表值都有分支匹配；**有用**（`useful`）：某个代表值第一个匹配的就是这个分支。

**关键引理** `abs_match`：真实的值 `v` 对应一个代表值 `abs v`（不在 `L` 里的字面量换成 `fresh`，深度 `d` 以下换成 `any`），
对每个分支，`v` 是否匹配和 `abs v` 是否匹配相同；`abs_mem`：类型为 `t` 的值，`abs v` 在 `reps d t` 里。

**定理**：
- `exhaustive_sound`：检查通过时，每个类型正确的值都有分支匹配（于是 M24 的 `run_correct` 适用，展开后的 `panic` 走不到）；
- `useful_complete`：某个值第一个匹配的是分支 `b`，检查就认为 `b` 有用——“分支永远匹配不到”的报错不会错报。

类型可以递归（`List` 的 `Cons` 载荷里有 `List`）：代表值只展开到深度 `d`，所以总是有限的。
`Bool` 当成有两个无载荷变体的枚举，不需要 `fresh`。
-/

namespace Core.M24b
open Core.M24

inductive Ty
  | int
  | enum (k : Nat)
  | pair (a b : Ty)

/-- 枚举 `k` 的各个变体的载荷类型（`none`：没有载荷）。 -/
abbrev Env := Nat → List (Option Ty)

inductive HasTy (E : Env) : Val → Ty → Prop
  | lit (n : Int) : HasTy E (.lit n) .int
  | tag0 {k i : Nat} : (E k)[i]? = some none → HasTy E (.tag0 i) (.enum k)
  | tag1 {k i : Nat} {t : Ty} {v : Val} : (E k)[i]? = some (some t) → HasTy E v t → HasTy E (.tag1 i v) (.enum k)
  | pair {a b : Val} {s t : Ty} : HasTy E a s → HasTy E b t → HasTy E (.pair a b) (.pair s t)

/-- 代表值：`any` 代表深度用完以后的任意值。 -/
inductive AVal
  | any
  | lit (n : Int)
  | tag0 (i : Nat)
  | tag1 (i : Nat) (v : AVal)
  | pair (a b : AVal)
  deriving DecidableEq, Repr

def amatch : Pat → AVal → Bool
  | .wild, _ => true
  | .bind _, _ => true
  | .lit n, .lit m => n == m
  | .tag0 i, .tag0 j => i == j
  | .tag1 i p, .tag1 j v => i == j && amatch p v
  | .pair p q, .pair a b => amatch p a && amatch q b
  | _, _ => false

def depth : Pat → Nat
  | .wild => 0
  | .bind _ => 0
  | .lit _ => 1
  | .tag0 _ => 1
  | .tag1 _ p => depth p + 1
  | .pair p q => max (depth p) (depth q) + 1

def lits : Pat → List Int
  | .lit n => [n]
  | .tag1 _ p => lits p
  | .pair p q => lits p ++ lits q
  | _ => []

/-- 真实的值对应的代表值。 -/
def abs (L : List Int) (fresh : Int) : Nat → Val → AVal
  | 0, _ => .any
  | _ + 1, .lit n => .lit (if n ∈ L then n else fresh)
  | _ + 1, .tag0 i => .tag0 i
  | d + 1, .tag1 i v => .tag1 i (abs L fresh d v)
  | d + 1, .pair a b => .pair (abs L fresh d a) (abs L fresh d b)

theorem abs_match (L : List Int) (fresh : Int) (hf : fresh ∉ L) :
    ∀ (p : Pat) (v : Val) (d : Nat), depth p ≤ d → (∀ n ∈ lits p, n ∈ L) →
      amatch p (abs L fresh d v) = test p v
  | .wild, _, _, _, _ => by simp [amatch, test]
  | .bind _, _, _, _, _ => by simp [amatch, test]
  | .lit n, v, d, hd, hl => by
    cases d with
    | zero => simp [depth] at hd
    | succ d =>
      have hn : n ∈ L := hl n (by simp [lits])
      cases v with
      | lit m =>
        by_cases hm : m ∈ L
        · simp [abs, hm, amatch, test]
        · have h1 : n ≠ m := fun e => hm (e ▸ hn)
          have h2 : n ≠ fresh := fun e => hf (e ▸ hn)
          have e1 : (n == fresh) = false := beq_false_of_ne h2
          have e2 : (n == m) = false := beq_false_of_ne h1
          simp only [abs, amatch, test, hm, ↓reduceIte, e1, e2]
      | tag0 _ => simp [abs, amatch, test]
      | tag1 _ _ => simp [abs, amatch, test]
      | pair _ _ => simp [abs, amatch, test]
  | .tag0 _, v, d, hd, _ => by
    cases d with
    | zero => simp [depth] at hd
    | succ d => cases v <;> simp [abs, amatch, test]
  | .tag1 i p, v, d, hd, hl => by
    cases d with
    | zero => simp [depth] at hd
    | succ d =>
      have hd' : depth p ≤ d := by simp only [depth] at hd; omega
      cases v with
      | tag1 j w =>
        have := abs_match L fresh hf p w d hd' (fun n hn => hl n (by simpa [lits] using hn))
        simp [abs, amatch, test, this]
      | lit _ => simp [abs, amatch, test]
      | tag0 _ => simp [abs, amatch, test]
      | pair _ _ => simp [abs, amatch, test]
  | .pair p q, v, d, hd, hl => by
    cases d with
    | zero => simp [depth] at hd
    | succ d =>
      have hd' : max (depth p) (depth q) ≤ d := by simp only [depth] at hd; omega
      cases v with
      | pair a b =>
        have ha := abs_match L fresh hf p a d (by omega) (fun n hn => hl n (by simp [lits, hn]))
        have hb := abs_match L fresh hf q b d (by omega) (fun n hn => hl n (by simp [lits, hn]))
        simp [abs, amatch, test, ha, hb]
      | lit _ => simp [abs, amatch, test]
      | tag0 _ => simp [abs, amatch, test]
      | tag1 _ _ => simp [abs, amatch, test]

/-! ## 代表值 -/

def reps (E : Env) (L : List Int) (fresh : Int) : Nat → Ty → List AVal
  | 0, _ => [.any]
  | _ + 1, .int => (L ++ [fresh]).map (fun n => .lit n)
  | d + 1, .enum k => (List.range (E k).length).flatMap (fun i =>
      match (E k)[i]? with
      | some none => [.tag0 i]
      | some (some t) => (reps E L fresh d t).map (fun v => .tag1 i v)
      | none => [])
  | d + 1, .pair s t => (reps E L fresh d s).flatMap (fun a => (reps E L fresh d t).map (fun b => .pair a b))

theorem abs_mem (E : Env) (L : List Int) (fresh : Int) {v : Val} {t : Ty} (h : HasTy E v t) :
    ∀ d, abs L fresh d v ∈ reps E L fresh d t := by
  induction h with
  | lit n =>
    intro d
    cases d with
    | zero => simp [abs, reps]
    | succ d => by_cases hn : n ∈ L <;> simp [abs, reps, hn]
  | @tag0 k i hk =>
    intro d
    cases d with
    | zero => simp [abs, reps]
    | succ d =>
      have hi : i < (E k).length := by
        rcases List.getElem?_eq_some_iff.1 hk with ⟨hi, _⟩
        exact hi
      simp only [abs, reps, List.mem_flatMap, List.mem_range]
      exact ⟨i, hi, by rw [hk]; simp⟩
  | @tag1 k i t v hk _ ih =>
    intro d
    cases d with
    | zero => simp [abs, reps]
    | succ d =>
      have hi : i < (E k).length := by
        rcases List.getElem?_eq_some_iff.1 hk with ⟨hi, _⟩
        exact hi
      simp only [abs, reps, List.mem_flatMap, List.mem_range]
      exact ⟨i, hi, by rw [hk]; simpa using ih d⟩
  | pair _ _ iha ihb =>
    intro d
    cases d with
    | zero => simp [abs, reps]
    | succ d =>
      simp only [abs, reps, List.mem_flatMap, List.mem_map]
      exact ⟨_, iha d, _, ihb d, rfl⟩

/-! ## 不在 `L` 里的字面量 -/

def freshOf (L : List Int) : Int := L.foldr max 0 + 1

theorem le_fold : ∀ (L : List Int) (x : Int), x ∈ L → x ≤ L.foldr max 0
  | [], _, h => by simp at h
  | y :: L, x, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with e | h
    · subst e; omega
    · have := le_fold L x h; omega

theorem fresh_not_mem (L : List Int) : freshOf L ∉ L := by
  intro h
  have := le_fold L _ h
  unfold freshOf at this
  omega

/-! ## 检查 -/

def allLits (as : List Arm) : List Int := as.flatMap (fun a => lits a.1)

def maxDepth (as : List Arm) : Nat := as.foldr (fun a m => max (depth a.1) m) 0

def exhaustive (E : Env) (t : Ty) (as : List Arm) : Bool :=
  (reps E (allLits as) (freshOf (allLits as)) (maxDepth as) t).all (fun r => as.any (fun a => amatch a.1 r))

/-- 代表值第一个匹配的分支。 -/
def aselect : List Arm → AVal → Option Nat
  | [], _ => none
  | (p, b) :: as, r => if amatch p r then some b else aselect as r

def useful (E : Env) (t : Ty) (as : List Arm) (b : Nat) : Bool :=
  (reps E (allLits as) (freshOf (allLits as)) (maxDepth as) t).any (fun r => aselect as r == some b)

theorem depth_le : ∀ {as : List Arm} {a : Arm}, a ∈ as → depth a.1 ≤ maxDepth as
  | [], _, h => by simp at h
  | b :: as, a, h => by
    simp only [maxDepth, List.foldr_cons]
    rcases List.mem_cons.1 h with e | h
    · subst e; omega
    · have := depth_le h
      simp only [maxDepth] at this
      omega

theorem lits_sub {as : List Arm} {a : Arm} (h : a ∈ as) : ∀ n ∈ lits a.1, n ∈ allLits as :=
  fun _ hn => List.mem_flatMap.2 ⟨a, h, hn⟩

theorem select_some : ∀ (as : List Arm) (p : Pat) (b : Nat) (v : Val), (p, b) ∈ as →
    (pmatch p v).isSome = true → (select as v).isSome = true
  | [], _, _, _, h, _ => by simp at h
  | (q, c) :: as, p, b, v, h, hp => by
    simp only [select]
    cases hq : pmatch q v with
    | some l => simp
    | none =>
      rcases List.mem_cons.1 h with e | h
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rw [hq] at hp
        simp at hp
      · exact select_some as p b v h hp

/-- **穷尽检查通过时，每个类型正确的值都有分支匹配。** -/
theorem exhaustive_sound (E : Env) (t : Ty) (as : List Arm) (h : exhaustive E t as = true)
    {v : Val} (hv : HasTy E v t) : (select as v).isSome = true := by
  have hr := abs_mem E (allLits as) (freshOf (allLits as)) hv (maxDepth as)
  have hall := List.all_eq_true.1 h _ hr
  obtain ⟨⟨p, b⟩, ha, hm⟩ := List.any_eq_true.1 hall
  rw [abs_match _ _ (fresh_not_mem _) p v _ (depth_le ha) (lits_sub ha), test_eq] at hm
  exact select_some as p b v ha hm

theorem aselect_abs (L : List Int) (fresh : Int) (hf : fresh ∉ L) (d : Nat) (v : Val) :
    ∀ as : List Arm, (∀ a ∈ as, depth a.1 ≤ d) → (∀ a ∈ as, ∀ n ∈ lits a.1, n ∈ L) →
      aselect as (abs L fresh d v) = (select as v).map Prod.fst
  | [], _, _ => by simp [aselect, select]
  | (p, b) :: as, hd, hl => by
    have e := abs_match L fresh hf p v d (hd (p, b) (by simp)) (hl (p, b) (by simp))
    rw [test_eq] at e
    have ih := aselect_abs L fresh hf d v as (fun a h => hd a (by simp [h])) (fun a h => hl a (by simp [h]))
    cases hm : pmatch p v with
    | some l => simp [aselect, select, e, hm]
    | none => simp [aselect, select, e, hm, ih]

/-- **某个值第一个匹配的是分支 `b` 时，检查认为 `b` 有用**（“分支永远匹配不到”不会错报）。 -/
theorem useful_complete (E : Env) (t : Ty) (as : List Arm) (b : Nat) {v : Val} (hv : HasTy E v t)
    (hs : (select as v).map Prod.fst = some b) : useful E t as b = true := by
  have hr := abs_mem E (allLits as) (freshOf (allLits as)) hv (maxDepth as)
  have e := aselect_abs _ _ (fresh_not_mem (allLits as)) (maxDepth as) v as
    (fun a h => depth_le h) (fun a h => lits_sub h)
  unfold useful
  rw [List.any_eq_true]
  exact ⟨_, hr, by rw [e, hs]; simp⟩

/-! ## 例子：`enum List { Cons((I64, List)), Nil }`（枚举 0），`Option<I64>`（枚举 1：`Some(I64)`、`None`） -/

def Ex : Env := fun k => if k = 0 then [some (.pair .int (.enum 0)), none] else [some .int, none]

-- M24 的三个分支：穷尽，三个都有用
example : exhaustive Ex (.enum 0) arms = true := by decide
example : useful Ex (.enum 0) arms 0 = true ∧ useful Ex (.enum 0) arms 1 = true ∧ useful Ex (.enum 0) arms 2 = true := by
  decide
-- 少了 `.Nil` 分支：不穷尽
example : exhaustive Ex (.enum 0) (arms.take 2) = false := by decide
-- `match o { .Some(0) => 0, .None => 1 }`：`.Some(其他数)` 没有覆盖
example : exhaustive Ex (.enum 1) [(.tag1 0 (.lit 0), 0), (.tag0 1, 1)] = false := by decide
-- `.Some(x)` 写在 `.Some(0)` 前面：后者永远匹配不到
example : useful Ex (.enum 1) [(.tag1 0 (.bind 0), 0), (.tag1 0 (.lit 0), 1), (.tag0 1, 2)] 1 = false := by decide

end Core.M24b
