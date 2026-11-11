import Core.Datatypes.Enum

/-!
# `match` 的通配分支 `_`

`match` 可以有通配分支：`match o { .Some(x) => …, _ => … }`。`_` 分支覆盖前面没有写到的所有变体，
不绑定载荷——按移动匹配时，载荷被丢掉（析构）。

**模型**：沿用 `Datatypes.Enum` 的枚举（`D[i]` 表示第 `i` 个变体是否带 `Box` 载荷）。一个分支是 `(模式, 语句)`，
模式是 `.v i`（第 `i` 个变体）或 `.wild`（`_`）。编译器做两件事：

1. **覆盖检查** `covers`：显式写的变体互不相同、都存在；`_` 最多一个，只能在最后，而且确实还有没写到的变体
   （否则 `_` 多余）；没有 `_` 时每个变体都要写。
2. **检查分支**：显式分支和 `Datatypes.Enum` 一样，从 `armStart`（`x` 已拆开，载荷在 `y` 里）开始检查；
   `_` 分支只检查一次，从“`x` 已拆开、`y` 没有值”的状态开始。

**语义**：把 `_` 展开成 `Datatypes.Enum` 的分支列表 `expand`：第 `i` 个变体用第一个写了 `.v i` 的分支；没写的用 `_` 分支，
带载荷时先把载荷析构（`free y`）。展开后就是一个普通的 `Datatypes.Enum` `match`。

**定理**：
- `expand_some`：通过覆盖检查时展开一定成功，`expand_length`：展开后正好每个变体一个分支（`Datatypes.Enum` 要求的穷尽性）；
- `expand_arm`：展开后第 `i` 个分支的检查结果，就是编译器检查的那个分支的结果——显式分支不变；
  `_` 分支对每个变体都和“只检查一次”相同（`wild_arm`：带载荷时先 `free y`，状态正好回到 `y` 没有值）；
- 所以编译器接受的带 `_` 的 `match`，展开后被 `Datatypes.Enum` 的检查器接受，`Datatypes.Enum` 的 `safety_and_no_leak`
  （不出错、没有泄漏）照样成立。

sinterc 里 `_` 分支的载荷绑定到一个看不见的变量，在分支结束时析构；这里在分支开始时析构。
两种都不泄漏，分支里都用不到这个载荷，区别只在析构的时机。按借用的 `match`（`Datatypes.Enum` 二）里 `_` 不绑定任何东西，
不需要析构，规则不变。
-/

namespace Core.Matching.Wildcard
open Core.Datatypes.Enum

inductive Pat | v (i : Nat) | wild
  deriving DecidableEq, Repr

abbrev Arm := Pat × List Stmt

/-! ## 编译器的覆盖检查 -/

/-- 显式写了的变体。 -/
def explicit : List Arm → List Nat
  | []              => []
  | (.v i, _) :: as => i :: explicit as
  | (.wild, _) :: as => explicit as

/-- `_` 只能是最后一个分支。 -/
def wildLast : List Arm → Bool
  | []                   => true
  | [_]                  => true
  | (.wild, _) :: _ :: _ => false
  | (.v _, _) :: as      => wildLast as

def hasWild (as : List Arm) : Bool := as.any (fun a => a.1 == .wild)

def covers (n : Nat) (as : List Arm) : Bool :=
  decide (explicit as).Nodup && (explicit as).all (· < n) && wildLast as &&
  (if hasWild as then (List.range n).any (fun i => !(explicit as).contains i)
   else (List.range n).all (fun i => (explicit as).contains i))

/-! ## 展开成 `Datatypes.Enum` 的分支 -/

def findArm (i : Nat) : List Arm → Option (List Stmt)
  | []              => none
  | (.v j, b) :: as => if j = i then some b else findArm i as
  | (.wild, _) :: as => findArm i as

def wildBody : List Arm → Option (List Stmt)
  | []               => none
  | (.wild, b) :: _  => some b
  | (.v _, _) :: as  => wildBody as

/-- `_` 用于第 `i` 个变体：带载荷时先把载荷析构。 -/
def wildArm (D : List Bool) (y : Var) (i : Nat) (b : List Stmt) : List Stmt :=
  (if hasPay D i then [.free y] else []) ++ b

def armFor (D : List Bool) (y : Var) (as : List Arm) (i : Nat) : Option (List Stmt) :=
  match findArm i as with
  | some b => some b
  | none   => (wildBody as).map (wildArm D y i)

def expandFrom (D : List Bool) (y : Var) (as : List Arm) : Nat → Nat → Option (List (List Stmt))
  | _, 0     => some []
  | i, k + 1 =>
    match armFor D y as i, expandFrom D y as (i + 1) k with
    | some a, some l => some (a :: l)
    | _, _           => none

def expand (D : List Bool) (y : Var) (as : List Arm) : Option (List (List Stmt)) :=
  expandFrom D y as 0 D.length

/-! ## 展开成功，长度正确 -/

theorem expandFrom_length (D : List Bool) (y : Var) (as : List Arm) :
    ∀ k i l, expandFrom D y as i k = some l → l.length = k
  | 0, i, l, h => by simp [expandFrom] at h; subst h; rfl
  | k + 1, i, l, h => by
    simp only [expandFrom] at h
    split at h
    · rename_i a l' _ h2
      cases h
      simp [expandFrom_length D y as k (i + 1) l' h2]
    · contradiction

theorem expand_length {D : List Bool} {y : Var} {as : List Arm} {l : List (List Stmt)}
    (h : expand D y as = some l) : l.length = D.length :=
  expandFrom_length D y as _ 0 l h

theorem findArm_some {i : Nat} : ∀ {as : List Arm}, (explicit as).contains i = true → (findArm i as).isSome
  | [], h => by simp [explicit] at h
  | (.v j, b) :: as, h => by
    simp only [findArm]
    by_cases hj : j = i
    · simp [hj]
    · simp only [explicit, List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h
      rw [ite_eq_right hj]
      rcases h with h | h
      · exact absurd h.symm hj
      · exact findArm_some (by simpa using h)
  | (.wild, _) :: as, h => by
    simp only [findArm]
    exact findArm_some (by simpa [explicit] using h)

theorem wildBody_some : ∀ {as : List Arm}, hasWild as = true → (wildBody as).isSome
  | [], h => by simp [hasWild] at h
  | (.wild, _) :: _, _ => by simp [wildBody]
  | (.v _, _) :: as, h => by
    simp only [wildBody]
    exact wildBody_some (by simpa [hasWild] using h)

/-- 通过覆盖检查时，每个变体都有分支（显式的或者 `_`）。 -/
theorem covers_arm {n : Nat} {D : List Bool} {y : Var} {as : List Arm} (hc : covers n as = true) :
    ∀ i, i < n → (armFor D y as i).isSome := by
  intro i hi
  simp only [covers, Bool.and_eq_true] at hc
  obtain ⟨_, hw⟩ := hc
  simp only [armFor]
  split
  · simp
  · rename_i hf
    by_cases h : hasWild as = true
    · simp [Option.isSome_map, wildBody_some h]
    · rw [ite_eq_right h] at hw
      have hin : (explicit as).contains i = true := by
        rw [List.all_eq_true] at hw
        exact hw i (List.mem_range.mpr hi)
      have := findArm_some hin
      rw [hf] at this
      contradiction

theorem expandFrom_some {D : List Bool} {y : Var} {as : List Arm} :
    ∀ k i, (∀ j, i ≤ j → j < i + k → (armFor D y as j).isSome) → (expandFrom D y as i k).isSome
  | 0, _, _ => by simp [expandFrom]
  | k + 1, i, h => by
    simp only [expandFrom]
    have h1 := h i (Nat.le_refl i) (by omega)
    have h2 := expandFrom_some k (i + 1) (fun j hj1 hj2 => h j (by omega) (by omega))
    cases ha : armFor D y as i with
    | none => rw [ha] at h1; contradiction
    | some a =>
      cases hl : expandFrom D y as (i + 1) k with
      | none => rw [hl] at h2; contradiction
      | some l => simp

/-- **通过覆盖检查，展开就成功**，而且正好每个变体一个分支。 -/
theorem expand_some {D : List Bool} {y : Var} {as : List Arm} (hc : covers D.length as = true) :
    ∃ l, expand D y as = some l ∧ l.length = D.length := by
  have := expandFrom_some (D := D) (y := y) (as := as) D.length 0
    (fun j _ hj => covers_arm hc j (by omega))
  cases h : expand D y as with
  | none => simp only [expand] at h; rw [h] at this; contradiction
  | some l => exact ⟨l, rfl, expand_length h⟩

/-! ## 分支的检查结果 -/

theorem expandFrom_get {D : List Bool} {y : Var} {as : List Arm} :
    ∀ k i l, expandFrom D y as i k = some l → ∀ j a, l[j]? = some a → armFor D y as (i + j) = some a
  | 0, i, l, h, j, a, hj => by simp [expandFrom] at h; subst h; simp at hj
  | k + 1, i, l, h, j, a, hj => by
    simp only [expandFrom] at h
    split at h
    · rename_i a0 l' h1 h2
      cases h
      cases j with
      | zero => simp at hj; subst hj; simpa using h1
      | succ j =>
        simp at hj
        have := expandFrom_get k (i + 1) l' h2 j a hj
        rw [show i + 1 + j = i + (j + 1) by omega] at this
        exact this
    · contradiction

section
variable (Γ : Var → Ty) (D : List Bool) (N : Nat)

/-- `_` 分支：带载荷时先 `free y`，之后的状态正好是“`x` 已拆开、`y` 没有值”，
所以对每个变体的检查都和只检查一次相同。 -/
theorem wild_arm (σ : SEnv) (x y : Var) (i : Nat) (b : List Stmt) (hΓ : Γ y = .box) :
    checkList Γ D N (armStart D σ x y i) (wildArm D y i b) =
      checkList Γ D N (upd (upd σ x .no) y .no) b := by
  cases hp : hasPay D i with
  | false => simp [wildArm, armStart, hp]
  | true =>
    have e : upd (upd (upd σ x .no) y .yes) y .no = upd (upd σ x .no) y .no := by
      funext z; by_cases hz : z = y <;> simp [upd, hz]
    simp [wildArm, armStart, hp, checkList, checkS, hΓ, e]

/-- 编译器对第 `i` 个变体检查的分支：第一个写了 `.v i` 的分支从 `armStart` 开始，否则 `_` 分支从“`y` 没有值”开始。 -/
def compilerArm (σ : SEnv) (x y : Var) (as : List Arm) (i : Nat) : Option (Option SEnv) :=
  match findArm i as with
  | some b => some (checkList Γ D N (armStart D σ x y i) b)
  | none   => (wildBody as).map (checkList Γ D N (upd (upd σ x .no) y .no))

/-- **展开后第 `i` 个分支的检查结果就是编译器检查的结果。** -/
theorem expand_arm (σ : SEnv) (x y : Var) (as : List Arm) (hΓ : Γ y = .box)
    {l : List (List Stmt)} (h : expand D y as = some l) (i : Nat) (a : List Stmt) (ha : l[i]? = some a) :
    compilerArm Γ D N σ x y as i = some (checkList Γ D N (armStart D σ x y i) a) := by
  have hf := expandFrom_get _ 0 l h i a ha
  rw [Nat.zero_add] at hf
  simp only [armFor] at hf
  simp only [compilerArm]
  split
  · rename_i b hb
    rw [hb] at hf
    cases hf
    rfl
  · rename_i hb
    rw [hb] at hf
    cases hw : wildBody as with
    | none => rw [hw] at hf; simp at hf
    | some w =>
      rw [hw] at hf
      simp at hf
      subst hf
      simp [wild_arm Γ D N σ x y i w hΓ]

/-- **结论**：通过覆盖检查的 `match`，展开后是 `Datatypes.Enum` 的穷尽 `match`；它被 `Datatypes.Enum` 接受时，
整个程序执行和析构都不出错，结束时没有泄漏（`Datatypes.Enum` 的 `safety_and_no_leak`）。 -/
theorem wild_safe (as : List Arm) (pre post : List Item) (x y : Var) (σ' : SEnv)
    (hc : covers D.length as = true) :
    ∃ l, expand D y as = some l ∧ l.length = D.length ∧
      (checkItems Γ D N (fun _ => .no) (pre ++ [.mat x y l] ++ post) = some σ' →
        ∃ s', (execItems St.empty (pre ++ [.mat x y l] ++ post)).bind (fun s => dropAll Γ D s N) = some s' ∧
          ∀ m, s'.live m = false) := by
  obtain ⟨l, h1, h2⟩ := expand_some (y := y) hc
  exact ⟨l, h1, h2, fun h => safety_and_no_leak Γ D N _ σ' h⟩

end

/-! ## 例子：`enum E { A(Box), B, C(Box) }` -/

def Dx : List Bool := [true, false, true]

/-- `match e { .A(y) => free y, _ => {} }`：通过覆盖检查，B、C 用 `_`，C 的载荷先析构。 -/
def ex1 : List Arm := [(.v 0, [.free 2]), (.wild, [])]

example : covers 3 ex1 = true := by decide
example : expand Dx 2 ex1 = some [[.free 2], [], [.free 2]] := rfl

/-- 三个都写了，再写 `_` 是多余的：拒绝。 -/
example : covers 3 [(.v 0, []), (.v 1, []), (.v 2, []), (.wild, [])] = false := by decide
/-- `_` 不在最后：拒绝。 -/
example : covers 3 [(.wild, []), (.v 0, [])] = false := by decide
/-- 同一个变体写两次：拒绝。 -/
example : covers 3 [(.v 0, []), (.v 0, []), (.wild, [])] = false := by decide
/-- 没有 `_`，也没写全：拒绝。 -/
example : covers 3 [(.v 0, []), (.v 1, [])] = false := by decide

/-- 展开后的程序被 `Datatypes.Enum` 接受、运行不泄漏（变量 0 是枚举，1、2 是 Box）。 -/
def Γx : Var → Ty := fun x => if x = 0 then .enum else .box
example : (checkItems Γx Dx 3 (fun _ => .no)
    [.stmt (.alloc 1), .stmt (.mk 0 2 (some 1)), .mat 0 2 [[.free 2], [], [.free 2]]]).isSome = true := rfl
example : ((execItems St.empty
    [.stmt (.alloc 1), .stmt (.mk 0 2 (some 1)), .mat 0 2 [[.free 2], [], [.free 2]]]).bind
      (fun s => dropAll Γx Dx s 3)).isSome = true := rfl

end Core.Matching.Wildcard
