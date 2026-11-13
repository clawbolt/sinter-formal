import Core.Basic

/-!
# 结构化并发：`scope` 与 `spawn`

```
scope |s| {
    for conn in listener.incoming() {
        s.spawn(|| handle(conn, cfg))   // conn 移动进任务，cfg 只读共享
    }
}                                       // 所有任务结束后才离开 scope
```

父作用域（下面叫父任务）的语句里夹着 `spawn i`；任务 `i` 从那一刻起和父任务、别的任务交错执行，
`scope` 结束时所有任务都已结束。任务的捕获只有两种：只读共享（`let`，之后整个 scope 里谁都不能修改）
和移动（`sink`，之后父任务不能再用）；`inout` 捕获被拒绝。

## 模型
内存是变量到值的映射（`none` 是没有值：没分配、已释放）。每个操作有足迹 `fp`（读写的变量）和写集 `wr`。
一次执行由调度决定：每一步任选父任务或一个已经 spawn 的任务，执行它的下一个操作（`Step`）。
调度是任意的，所以这覆盖了任意多个线程、任意的抢占方式（数据无竞争的 C 程序在 C 内存模型里就是顺序一致的）。

## 结论
- 检查（`check`，就是上面的捕获规则）通过 ⇒ 足迹互不冲突（`check_indep`）：一个线程写的变量，别的同时活着的线程都不碰。
- 足迹不冲突、并且每个线程单独执行不出错（`AloneOk`：父任务把 spawn 当空操作执行；任务 `i` 从 spawn 那一刻
  父任务的内存出发执行。任务体是提升出来的普通函数，单线程的检查已经保证这一点）⇒
  - `safe`：任何调度下任何线程的下一步都不出错（没有释放后使用、没有读到不存在的值）；
  - `progress`：没结束时总能走一步（没有死锁）；
  - `deterministic`：所有线程都结束时，内存和调度无关；
  - `scope_eq_seq`：等于按顺序执行——在每个 `spawn i` 处把任务 `i` 整个执行完（`seqRun`）。
    所以 `scope` 的意义就是顺序程序的意义，所有权、析构、不泄漏都沿用单线程的定理。
- 反例：任务写只读共享的变量时，两种调度的结果不同（`race`），`check` 拒绝它。
-/

namespace Core.Concurrency.Scope

abbrev Mem := Var → Option Nat

/-! ## 操作与足迹 -/

inductive Op
  | read (x : Var)
  | write (x : Var) (n : Nat)
  | copy (x y : Var)        -- y := x
  | alloc (x : Var) (n : Nat)
  | free (x : Var)
  deriving DecidableEq

def fp : Op → List Var
  | .read x => [x]
  | .write x _ => [x]
  | .copy x y => [x, y]
  | .alloc x _ => [x]
  | .free x => [x]

def wr : Op → List Var
  | .read _ => []
  | .write x _ => [x]
  | .copy _ y => [y]
  | .alloc x _ => [x]
  | .free x => [x]

def exec : Op → Mem → Option Mem
  | .read x, m => if (m x).isSome then some m else none
  | .write x n, m => if (m x).isSome then some (upd m x (some n)) else none
  | .copy x y, m =>
    match m x with
    | some v => some (upd m y (some v))
    | none => none
  | .alloc x n, m => if (m x).isNone then some (upd m x (some n)) else none
  | .free x, m => if (m x).isSome then some (upd m x none) else none

theorem wr_fp {o : Op} {x : Var} (h : x ∈ wr o) : x ∈ fp o := by
  cases o <;> simp_all [wr, fp]

/-- 操作只改写集里的变量。 -/
theorem frame {o : Op} {m m' : Mem} {x : Var} (h : exec o m = some m') (hx : x ∉ wr o) :
    m' x = m x := by
  cases o with
  | read y =>
    simp only [exec] at h
    split at h
    · cases h; rfl
    · cases h
  | write y n =>
    simp only [wr, List.mem_singleton] at hx
    simp only [exec] at h
    split at h
    · cases h; exact upd_other _ _ hx
    · cases h
  | copy y z =>
    simp only [wr, List.mem_singleton] at hx
    simp only [exec] at h
    split at h
    · cases h; exact upd_other _ _ hx
    · cases h
  | alloc y n =>
    simp only [wr, List.mem_singleton] at hx
    simp only [exec] at h
    split at h
    · cases h; exact upd_other _ _ hx
    · cases h
  | free y =>
    simp only [wr, List.mem_singleton] at hx
    simp only [exec] at h
    split at h
    · cases h; exact upd_other _ _ hx
    · cases h

/-- 操作只看足迹：两个内存在足迹上相同时，一个上成功另一个上也成功，结果在足迹上相同。 -/
theorem local_ {o : Op} {m n m' : Mem} (ha : ∀ x ∈ fp o, m x = n x) (h : exec o m = some m') :
    ∃ n', exec o n = some n' ∧ ∀ x ∈ fp o, m' x = n' x := by
  cases o with
  | read y =>
    have hy := ha y (by simp [fp])
    simp only [exec] at h ⊢
    split at h
    · rename_i hs
      cases h
      refine ⟨n, by rw [← hy]; simp [hs], ?_⟩
      intro x hx
      exact ha x hx
    · cases h
  | write y k =>
    have hy := ha y (by simp [fp])
    simp only [exec] at h ⊢
    split at h
    · rename_i hs
      cases h
      refine ⟨upd n y (some k), by rw [← hy]; simp [hs], ?_⟩
      intro x hx
      simp only [fp, List.mem_singleton] at hx
      rw [hx, upd_same, upd_same]
    · cases h
  | copy y z =>
    have hy := ha y (by simp [fp])
    simp only [exec] at h ⊢
    split at h
    · rename_i v hv
      cases h
      rw [← hy, hv]
      refine ⟨upd n z (some v), rfl, ?_⟩
      intro x hx
      by_cases hxz : x = z
      · rw [hxz, upd_same, upd_same]
      · rw [upd_other _ _ hxz, upd_other _ _ hxz]
        exact ha x hx
    · cases h
  | alloc y k =>
    have hy := ha y (by simp [fp])
    simp only [exec] at h ⊢
    split at h
    · rename_i hs
      cases h
      refine ⟨upd n y (some k), by rw [← hy]; simp [hs], ?_⟩
      intro x hx
      simp only [fp, List.mem_singleton] at hx
      rw [hx, upd_same, upd_same]
    · cases h
  | free y =>
    have hy := ha y (by simp [fp])
    simp only [exec] at h ⊢
    split at h
    · rename_i hs
      cases h
      refine ⟨upd n y none, by rw [← hy]; simp [hs], ?_⟩
      intro x hx
      simp only [fp, List.mem_singleton] at hx
      rw [hx, upd_same, upd_same]
    · cases h

/-! ## 操作序列 -/

def fpL : List Op → List Var
  | [] => []
  | o :: r => fp o ++ fpL r

def wrL : List Op → List Var
  | [] => []
  | o :: r => wr o ++ wrL r

theorem fpL_single (o : Op) : fpL [o] = fp o := by simp [fpL]
theorem wrL_single (o : Op) : wrL [o] = wr o := by simp [wrL]

theorem fp_sub {o : Op} {t : List Op} (h : o ∈ t) {x : Var} (hx : x ∈ fp o) : x ∈ fpL t := by
  induction t with
  | nil => cases h
  | cons a r ih =>
    simp only [fpL, List.mem_append]
    rcases List.mem_cons.1 h with e | e
    · rw [← e]; exact Or.inl hx
    · exact Or.inr (ih e)

theorem wr_sub {o : Op} {t : List Op} (h : o ∈ t) {x : Var} (hx : x ∈ wr o) : x ∈ wrL t := by
  induction t with
  | nil => cases h
  | cons a r ih =>
    simp only [wrL, List.mem_append]
    rcases List.mem_cons.1 h with e | e
    · rw [← e]; exact Or.inl hx
    · exact Or.inr (ih e)

theorem wrL_fpL {t : List Op} {x : Var} (h : x ∈ wrL t) : x ∈ fpL t := by
  induction t with
  | nil => cases h
  | cons a r ih =>
    simp only [wrL, fpL, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (wr_fp h)
    · exact Or.inr (ih h)

def execL : List Op → Mem → Option Mem
  | [], m => some m
  | o :: r, m => (exec o m).bind (execL r)

theorem execL_append (q r : List Op) : ∀ m, execL (q ++ r) m = (execL q m).bind (execL r) := by
  induction q with
  | nil => intro m; rfl
  | cons o q ih =>
    intro m
    show (exec o m).bind (execL (q ++ r)) = ((exec o m).bind (execL q)).bind (execL r)
    cases exec o m with
    | none => rfl
    | some m1 => exact ih m1

theorem bind_some {α β : Type} {x : Option α} {f : α → Option β} {y : β} (h : x.bind f = some y) :
    ∃ a, x = some a ∧ f a = some y := by
  cases x with
  | none => simp at h
  | some a => exact ⟨a, rfl, h⟩

/-- 两段操作不冲突：一段写的变量另一段不碰。 -/
def CF (a b : List Op) : Prop :=
  (∀ x, x ∈ wrL a → x ∉ fpL b) ∧ (∀ x, x ∈ wrL b → x ∉ fpL a)

theorem CF.symm {a b : List Op} (h : CF a b) : CF b a := ⟨h.2, h.1⟩

/-! ## 父任务 -/

inductive POp
  | op (o : Op)
  | spawn (i : Nat)

def spawns : List POp → List Nat
  | [] => []
  | .op _ :: r => spawns r
  | .spawn i :: r => i :: spawns r

theorem spawns_append (p q : List POp) : spawns (p ++ q) = spawns p ++ spawns q := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    cases a with
    | op o => simp only [List.cons_append, spawns]; exact ih
    | spawn i => simp only [List.cons_append, spawns, ih]

theorem sp_op (p : List POp) (o : Op) : spawns (p ++ [.op o]) = spawns p := by
  simp [spawns_append, spawns]

theorem sp_spawn (p : List POp) (i : Nat) : spawns (p ++ [.spawn i]) = spawns p ++ [i] := by
  simp [spawns_append, spawns]

/-- 父任务单独执行：`spawn` 是空操作。 -/
def aloneP : List POp → Mem → Option Mem
  | [], m => some m
  | .op o :: r, m => (exec o m).bind (aloneP r)
  | .spawn _ :: r, m => aloneP r m

theorem aloneP_append (p q : List POp) : ∀ m, aloneP (p ++ q) m = (aloneP p m).bind (aloneP q) := by
  induction p with
  | nil => intro m; rfl
  | cons a p ih =>
    intro m
    cases a with
    | op o =>
      show (exec o m).bind (aloneP (p ++ q)) = ((exec o m).bind (aloneP p)).bind (aloneP q)
      cases exec o m with
      | none => rfl
      | some m1 => exact ih m1
    | spawn i => exact ih m

/-- 父任务单独执行到 `spawn i` 时的内存：任务 `i` 从这里出发。 -/
def snapOf : List POp → Mem → Nat → Option Mem
  | [], _, _ => none
  | .op o :: r, m, i => (exec o m).bind (fun m' => snapOf r m' i)
  | .spawn j :: r, m, i => if j = i then some m else snapOf r m i

theorem snapOf_append_mem (p q : List POp) (i : Nat) :
    ∀ m, i ∈ spawns p → snapOf (p ++ q) m i = snapOf p m i := by
  induction p with
  | nil => intro m h; cases h
  | cons a p ih =>
    intro m h
    cases a with
    | op o =>
      simp only [spawns] at h
      show (exec o m).bind (fun m' => snapOf (p ++ q) m' i) = (exec o m).bind (fun m' => snapOf p m' i)
      cases exec o m with
      | none => rfl
      | some m1 => exact ih m1 h
    | spawn j =>
      simp only [List.cons_append, snapOf]
      by_cases hj : j = i
      · simp [hj]
      · simp only [spawns, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hj
        · simp only [hj, ↓reduceIte]; exact ih m h

theorem snapOf_append_not (p q : List POp) (i : Nat) :
    ∀ m, i ∉ spawns p → snapOf (p ++ q) m i = (aloneP p m).bind (fun a => snapOf q a i) := by
  induction p with
  | nil => intro m _; rfl
  | cons a p ih =>
    intro m h
    cases a with
    | op o =>
      simp only [spawns] at h
      show (exec o m).bind (fun m' => snapOf (p ++ q) m' i) =
        ((exec o m).bind (aloneP p)).bind (fun a => snapOf q a i)
      cases exec o m with
      | none => rfl
      | some m1 => exact ih m1 h
    | spawn j =>
      simp only [spawns, List.mem_cons, not_or] at h
      simp only [List.cons_append, snapOf, aloneP]
      have hne : ¬ j = i := Ne.symm h.1
      simp only [hne, ↓reduceIte]
      exact ih m h.2

/-! ## 调度 -/

section Sched
variable (T : Nat → List Op) (P : List POp) (m0 : Mem)

/-- 执行到一半的 scope。`pp`、`done` 只用于证明：父任务和每个任务已经执行的部分。 -/
structure Cfg where
  pp : List POp
  par : List POp
  done : Nat → List Op
  rest : Nat → List Op
  mem : Mem

inductive Step : Cfg → Cfg → Prop
  | parOp {c : Cfg} {o : Op} {r : List POp} {m' : Mem} :
      c.par = .op o :: r → exec o c.mem = some m' →
      Step c ⟨c.pp ++ [.op o], r, c.done, c.rest, m'⟩
  | parSpawn {c : Cfg} {i : Nat} {r : List POp} :
      c.par = .spawn i :: r →
      Step c ⟨c.pp ++ [.spawn i], r, upd c.done i [], upd c.rest i (T i), c.mem⟩
  | task {c : Cfg} {i : Nat} {o : Op} {r : List Op} {m' : Mem} :
      i ∈ spawns c.pp → c.rest i = o :: r → exec o c.mem = some m' →
      Step c ⟨c.pp, c.par, upd c.done i (c.done i ++ [o]), upd c.rest i r, m'⟩

def init : Cfg := ⟨[], P, fun _ => [], T, m0⟩

inductive Reach : Cfg → Prop
  | init : Reach (init T P m0)
  | step {c c' : Cfg} : Reach c → Step T c c' → Reach c'

/-- 每个线程单独执行不出错。 -/
def AloneOk : Prop :=
  (∃ A, aloneP P m0 = some A) ∧
  ∀ i ∈ spawns P, ∃ a s, snapOf P m0 i = some a ∧ execL (T i) a = some s

/-- 足迹不冲突：`S` 是已经 spawn 的任务。父任务之后的每个操作和它们不冲突；新任务和它们不冲突、编号不重复。 -/
def IndepP : List POp → List Nat → Prop
  | [], _ => True
  | .op o :: r, S => (∀ i ∈ S, CF [o] (T i)) ∧ IndepP r S
  | .spawn i :: r, S => i ∉ S ∧ (∀ j ∈ S, CF (T i) (T j)) ∧ IndepP r (i :: S)

/-- 不变式：父任务在它单独执行的内存 `A` 上前进（在没有任务写的变量上一致）；
    任务 `i` 在它单独执行的内存 `s` 上前进（在它的足迹上一致）。 -/
structure Inv (c : Cfg) : Prop where
  split : c.pp ++ c.par = P
  tasks : ∀ i ∈ spawns c.pp, c.done i ++ c.rest i = T i
  indep : ∃ S : List Nat, (∀ i, i ∈ S ↔ i ∈ spawns c.pp) ∧ IndepP T c.par S
  pair : ∀ i ∈ spawns c.pp, ∀ j ∈ spawns c.pp, i ≠ j → CF (T i) (T j)
  par : ∃ A, aloneP c.pp m0 = some A ∧
    ∀ x, (∀ i ∈ spawns c.pp, x ∉ wrL (T i)) → c.mem x = A x
  task : ∀ i ∈ spawns c.pp, ∃ a s, snapOf c.pp m0 i = some a ∧ execL (c.done i) a = some s ∧
    ∀ x ∈ fpL (T i), c.mem x = s x

theorem inv_init (hI : IndepP T P []) : Inv T P m0 (init T P m0) where
  split := rfl
  tasks := fun i h => by simp [init, spawns] at h
  indep := ⟨[], fun i => by simp [init, spawns], hI⟩
  pair := fun i h => by simp [init, spawns] at h
  par := ⟨m0, rfl, fun _ _ => rfl⟩
  task := fun i h => by simp [init, spawns] at h

/-- 父任务的下一个操作：它在父任务单独执行的内存上成功，两边在它的足迹上一致。 -/
theorem par_next (hA : AloneOk T P m0) {c : Cfg} (hc : Inv T P m0 c) {o : Op} {r : List POp}
    (hp : c.par = .op o :: r) :
    ∃ A A1, aloneP c.pp m0 = some A ∧ exec o A = some A1 ∧ (∀ x ∈ fp o, c.mem x = A x) ∧
      (∀ x, (∀ i ∈ spawns c.pp, x ∉ wrL (T i)) → c.mem x = A x) ∧
      ∀ i ∈ spawns c.pp, CF [o] (T i) := by
  obtain ⟨A, hAl, hAm⟩ := hc.par
  obtain ⟨S, hS, hI⟩ := hc.indep
  rw [hp] at hI
  simp only [IndepP] at hI
  have hcf : ∀ i ∈ spawns c.pp, CF [o] (T i) := fun i hi => hI.1 i ((hS i).2 hi)
  obtain ⟨Af, hAf⟩ := hA.1
  rw [← hc.split, hp, aloneP_append, hAl] at hAf
  obtain ⟨A1, hA1, _⟩ := bind_some (show (exec o A).bind (aloneP r) = some Af from hAf)
  refine ⟨A, A1, hAl, hA1, fun x hx => hAm x (fun i hi hw => (hcf i hi).2 x hw ?_), hAm, hcf⟩
  rw [fpL_single]; exact hx

/-- 任务 `i` 的下一个操作：它在任务单独执行的内存上成功，两边在任务的足迹上一致。 -/
theorem task_next (hA : AloneOk T P m0) {c : Cfg} (hc : Inv T P m0 c) {i : Nat} {o : Op}
    {r : List Op} (hi : i ∈ spawns c.pp) (hr : c.rest i = o :: r) :
    ∃ a s s1, snapOf c.pp m0 i = some a ∧ execL (c.done i) a = some s ∧ exec o s = some s1 ∧
      (∀ x ∈ fpL (T i), c.mem x = s x) ∧ o ∈ T i := by
  obtain ⟨a, s, hsn, hex, hag⟩ := hc.task i hi
  have ht : c.done i ++ o :: r = T i := by rw [← hr]; exact hc.tasks i hi
  have hiP : i ∈ spawns P := by
    rw [← hc.split, spawns_append]; exact List.mem_append_left _ hi
  obtain ⟨a', s', hsn', hex'⟩ := hA.2 i hiP
  rw [← hc.split, snapOf_append_mem _ _ _ _ hi, hsn] at hsn'
  rw [← Option.some.inj hsn', ← ht, execL_append, hex] at hex'
  obtain ⟨s1, hs1, _⟩ := bind_some (show (exec o s).bind (execL r) = some s' from hex')
  exact ⟨a, s, s1, hsn, hex, hs1, hag, by rw [← ht]; simp⟩

theorem inv_parOp (hA : AloneOk T P m0) {c : Cfg} (hc : Inv T P m0 c) {o : Op} {r : List POp}
    {m' : Mem} (hp : c.par = .op o :: r) (he : exec o c.mem = some m') :
    Inv T P m0 ⟨c.pp ++ [.op o], r, c.done, c.rest, m'⟩ := by
  obtain ⟨A, A1, hAl, hA1, hag, hAm, hcf⟩ := par_next T P m0 hA hc hp
  obtain ⟨n', hn', hagr⟩ := local_ hag he
  rw [hA1] at hn'
  rw [← Option.some.inj hn'] at hagr
  obtain ⟨S, hS, hI⟩ := hc.indep
  rw [hp] at hI
  simp only [IndepP] at hI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [List.append_assoc, List.singleton_append, ← hp]; exact hc.split
  · dsimp only
    intro i hi; rw [sp_op] at hi; exact hc.tasks i hi
  · dsimp only
    exact ⟨S, fun i => by rw [sp_op]; exact hS i, hI.2⟩
  · dsimp only
    intro i hi j hj; rw [sp_op] at hi hj; exact hc.pair i hi j hj
  · dsimp only
    refine ⟨A1, by simp [aloneP_append, hAl, aloneP, hA1], fun x hx => ?_⟩
    rw [sp_op] at hx
    by_cases hw : x ∈ wr o
    · exact hagr x (wr_fp hw)
    · rw [frame he hw, frame hA1 hw]; exact hAm x hx
  · dsimp only
    intro i hi
    rw [sp_op] at hi
    obtain ⟨a, s, hsn, hex, hag2⟩ := hc.task i hi
    refine ⟨a, s, by rw [snapOf_append_mem _ _ _ _ hi]; exact hsn, hex, fun x hx => ?_⟩
    have hw : x ∉ wr o := fun hw => (hcf i hi).1 x (by rw [wrL_single]; exact hw) hx
    rw [frame he hw]; exact hag2 x hx

theorem inv_parSpawn {c : Cfg} (hc : Inv T P m0 c) {i : Nat} {r : List POp}
    (hp : c.par = .spawn i :: r) :
    Inv T P m0 ⟨c.pp ++ [.spawn i], r, upd c.done i [], upd c.rest i (T i), c.mem⟩ := by
  obtain ⟨S, hS, hI⟩ := hc.indep
  rw [hp] at hI
  simp only [IndepP] at hI
  obtain ⟨hiS, hnew, hI⟩ := hI
  have hni : i ∉ spawns c.pp := fun h => hiS ((hS i).2 h)
  obtain ⟨A, hAl, hAm⟩ := hc.par
  have mem_new : ∀ j, j ∈ spawns (c.pp ++ [.spawn i]) ↔ j ∈ spawns c.pp ∨ j = i := by
    intro j; rw [sp_spawn, List.mem_append, List.mem_singleton]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [List.append_assoc, List.singleton_append, ← hp]; exact hc.split
  · dsimp only
    intro j hj
    by_cases hji : j = i
    · rw [hji]; simp
    · rw [upd_other _ _ hji, upd_other _ _ hji]
      rcases (mem_new j).1 hj with hj | hj
      · exact hc.tasks j hj
      · exact absurd hj hji
  · dsimp only
    refine ⟨i :: S, fun j => ?_, hI⟩
    rw [mem_new j, List.mem_cons, hS j]
    exact Or.comm
  · dsimp only
    intro j hj k hk hjk
    rcases (mem_new j).1 hj with hj | hj <;> rcases (mem_new k).1 hk with hk | hk
    · exact hc.pair j hj k hk hjk
    · rw [hk]; exact (hnew j ((hS j).2 hj)).symm
    · rw [hj]; exact hnew k ((hS k).2 hk)
    · exact absurd (hj.trans hk.symm) hjk
  · dsimp only
    exact ⟨A, by simp [aloneP_append, hAl, aloneP],
      fun x hx => hAm x (fun j hj => hx j ((mem_new j).2 (Or.inl hj)))⟩
  · dsimp only
    intro j hj
    by_cases hji : j = i
    · rw [hji]
      refine ⟨A, A, ?_, by simp [execL], ?_⟩
      · rw [snapOf_append_not _ _ _ _ hni, hAl]; simp [snapOf]
      · intro x hx
        exact hAm x (fun k hk hw => (hnew k ((hS k).2 hk)).2 x hw hx)
    · rcases (mem_new j).1 hj with hj | hj
      · obtain ⟨a, s, hsn, hex, hag⟩ := hc.task j hj
        exact ⟨a, s, by rw [snapOf_append_mem _ _ _ _ hj]; exact hsn,
          by rw [upd_other _ _ hji]; exact hex, hag⟩
      · exact absurd hj hji

theorem inv_task (hA : AloneOk T P m0) {c : Cfg} (hc : Inv T P m0 c) {i : Nat} {o : Op}
    {r : List Op} {m' : Mem} (hi : i ∈ spawns c.pp) (hr : c.rest i = o :: r)
    (he : exec o c.mem = some m') :
    Inv T P m0 ⟨c.pp, c.par, upd c.done i (c.done i ++ [o]), upd c.rest i r, m'⟩ := by
  obtain ⟨a, s, s1, hsn, hex, hs1, hag, ho⟩ := task_next T P m0 hA hc hi hr
  obtain ⟨n', hn', hagr⟩ := local_ (fun x hx => hag x (fp_sub ho hx)) he
  rw [hs1] at hn'
  rw [← Option.some.inj hn'] at hagr
  refine ⟨hc.split, ?_, hc.indep, hc.pair, ?_, ?_⟩
  · dsimp only
    intro j hj
    by_cases hji : j = i
    · rw [hji, upd_same, upd_same, List.append_assoc, List.singleton_append, ← hr]
      exact hc.tasks i hi
    · rw [upd_other _ _ hji, upd_other _ _ hji]; exact hc.tasks j hj
  · obtain ⟨A, hAl, hAm⟩ := hc.par
    refine ⟨A, hAl, fun x hx => ?_⟩
    have hw : x ∉ wr o := fun hw => hx i hi (wr_sub ho hw)
    show m' x = A x
    rw [frame he hw]; exact hAm x hx
  · dsimp only
    intro j hj
    by_cases hji : j = i
    · rw [hji]
      refine ⟨a, s1, hsn, ?_, fun x hx => ?_⟩
      · rw [upd_same, execL_append, hex]; simp [execL, hs1]
      · by_cases hw : x ∈ wr o
        · exact hagr x (wr_fp hw)
        · rw [frame he hw, frame hs1 hw]; exact hag x hx
    · obtain ⟨a2, s2, h1, h2, h3⟩ := hc.task j hj
      refine ⟨a2, s2, h1, by rw [upd_other _ _ hji]; exact h2, fun x hx => ?_⟩
      have hw : x ∉ wr o := fun hw => (hc.pair i hi j hj (Ne.symm hji)).1 x (wr_sub ho hw) hx
      rw [frame he hw]; exact h3 x hx

theorem inv_step (hA : AloneOk T P m0) {c c' : Cfg} (hc : Inv T P m0 c) (hs : Step T c c') :
    Inv T P m0 c' := by
  cases hs with
  | parOp hp he => exact inv_parOp T P m0 hA hc hp he
  | parSpawn hp => exact inv_parSpawn T P m0 hc hp
  | task hi hr he => exact inv_task T P m0 hA hc hi hr he

theorem inv_reach (hI : IndepP T P []) (hA : AloneOk T P m0) {c : Cfg} (h : Reach T P m0 c) :
    Inv T P m0 c := by
  induction h with
  | init => exact inv_init T P m0 hI
  | step _ hs ih => exact inv_step T P m0 hA ih hs

/-! ## 主定理 -/

/-- **安全**：任何调度下，父任务和每个已经 spawn 的任务的下一个操作都不出错。 -/
theorem safe (hI : IndepP T P []) (hA : AloneOk T P m0) {c : Cfg} (h : Reach T P m0 c) :
    (∀ o r, c.par = .op o :: r → ∃ m', exec o c.mem = some m') ∧
    (∀ i o r, i ∈ spawns c.pp → c.rest i = o :: r → ∃ m', exec o c.mem = some m') := by
  have hc := inv_reach T P m0 hI hA h
  constructor
  · intro o r hp
    obtain ⟨A, A1, _, hA1, hag, _, _⟩ := par_next T P m0 hA hc hp
    obtain ⟨n', hn', _⟩ := local_ (fun x hx => (hag x hx).symm) hA1
    exact ⟨n', hn'⟩
  · intro i o r hi hr
    obtain ⟨a, s, s1, _, _, hs1, hag, ho⟩ := task_next T P m0 hA hc hi hr
    obtain ⟨n', hn', _⟩ := local_ (fun x hx => (hag x (fp_sub ho hx)).symm) hs1
    exact ⟨n', hn'⟩

/-- 所有线程都结束了：`scope` 可以离开。 -/
abbrev Final (c : Cfg) : Prop := c.par = [] ∧ ∀ i ∈ spawns c.pp, c.rest i = []

/-- **没有死锁**：没结束时总能走一步。 -/
theorem progress (hI : IndepP T P []) (hA : AloneOk T P m0) {c : Cfg} (h : Reach T P m0 c)
    (hn : ¬ Final c) : ∃ c', Step T c c' := by
  have hs := safe T P m0 hI hA h
  cases hp : c.par with
  | cons x r =>
    cases x with
    | op o =>
      obtain ⟨m', he⟩ := hs.1 o r hp
      exact ⟨_, Step.parOp hp he⟩
    | spawn i => exact ⟨_, Step.parSpawn hp⟩
  | nil =>
    have : ∃ i ∈ spawns c.pp, c.rest i ≠ [] := by
      apply Classical.byContradiction
      intro hno
      exact hn ⟨hp, fun i hi => Classical.byContradiction (fun hne => hno ⟨i, hi, hne⟩)⟩
    obtain ⟨i, hi, hne⟩ := this
    cases hr : c.rest i with
    | nil => exact absurd hr hne
    | cons o r =>
      obtain ⟨m', he⟩ := hs.2 i o r hi hr
      exact ⟨_, Step.task hi hr he⟩

/-- 结束时：任务没写的变量是父任务单独执行的结果，任务 `i` 写的变量是任务 `i` 单独执行的结果。 -/
theorem final_facts (hI : IndepP T P []) (hA : AloneOk T P m0) {c : Cfg} (h : Reach T P m0 c)
    (hf : Final c) :
    (∃ A, aloneP P m0 = some A ∧ ∀ x, (∀ i ∈ spawns P, x ∉ wrL (T i)) → c.mem x = A x) ∧
    ∀ i ∈ spawns P, ∃ a s, snapOf P m0 i = some a ∧ execL (T i) a = some s ∧
      ∀ x ∈ fpL (T i), c.mem x = s x := by
  have hc := inv_reach T P m0 hI hA h
  have hpp : c.pp = P := by
    have := hc.split; rw [hf.1, List.append_nil] at this; exact this
  constructor
  · obtain ⟨A, hAl, hAm⟩ := hc.par
    rw [hpp] at hAl hAm
    exact ⟨A, hAl, hAm⟩
  · intro i hi
    have hi' : i ∈ spawns c.pp := by rw [hpp]; exact hi
    obtain ⟨a, s, hsn, hex, hag⟩ := hc.task i hi'
    have hd : c.done i = T i := by
      have := hc.tasks i hi'; rw [hf.2 i hi', List.append_nil] at this; exact this
    rw [hpp] at hsn
    rw [hd] at hex
    exact ⟨a, s, hsn, hex, hag⟩

/-- **结果和调度无关**。 -/
theorem deterministic (hI : IndepP T P []) (hA : AloneOk T P m0) {c c' : Cfg}
    (h : Reach T P m0 c) (h' : Reach T P m0 c') (hf : Final c) (hf' : Final c') :
    c.mem = c'.mem := by
  obtain ⟨⟨A, hA1, hAm⟩, ht⟩ := final_facts T P m0 hI hA h hf
  obtain ⟨⟨A', hA1', hAm'⟩, ht'⟩ := final_facts T P m0 hI hA h' hf'
  funext x
  by_cases hx : ∃ i ∈ spawns P, x ∈ wrL (T i)
  · obtain ⟨i, hi, hw⟩ := hx
    obtain ⟨a, s, h1, h2, h3⟩ := ht i hi
    obtain ⟨a', s', h1', h2', h3'⟩ := ht' i hi
    rw [h1] at h1'
    rw [← Option.some.inj h1', h2] at h2'
    rw [h3 x (wrL_fpL hw), h3' x (wrL_fpL hw), Option.some.inj h2']
  · have hn : ∀ i ∈ spawns P, x ∉ wrL (T i) := fun i hi hw => hx ⟨i, hi, hw⟩
    rw [hA1] at hA1'
    rw [hAm x hn, hAm' x hn, Option.some.inj hA1']

/-! ## 和按顺序执行相同 -/

/-- 按顺序执行：在 `spawn i` 处把任务 `i` 整个执行完（`scope` 最简单的实现）。 -/
def seqRun : List POp → Mem → Option Mem
  | [], m => some m
  | .op o :: r, m => (exec o m).bind (seqRun r)
  | .spawn i :: r, m => (execL (T i) m).bind (seqRun r)

/-- 一直调度任务 `i`，直到它结束。 -/
theorem run_task (hI : IndepP T P []) (hA : AloneOk T P m0) (ops : List Op) :
    ∀ {c : Cfg} {i : Nat}, Reach T P m0 c → i ∈ spawns c.pp → c.rest i = ops →
    ∃ c', Reach T P m0 c' ∧ c'.pp = c.pp ∧ c'.par = c.par ∧ c'.rest i = [] ∧
      (∀ j, j ≠ i → c'.rest j = c.rest j) ∧ execL ops c.mem = some c'.mem := by
  induction ops with
  | nil => intro c i h _ hr; exact ⟨c, h, rfl, rfl, hr, fun _ _ => rfl, rfl⟩
  | cons o r ih =>
    intro c i h hi hr
    obtain ⟨m', he⟩ := (safe T P m0 hI hA h).2 i o r hi hr
    have h1 := Reach.step h (Step.task hi hr he)
    obtain ⟨c', h', hpp, hpar, hri, hrj, hex⟩ := ih h1 hi (by simp)
    refine ⟨c', h', hpp, hpar, hri, fun j hj => by rw [hrj j hj]; exact upd_other _ _ hj, ?_⟩
    show (exec o c.mem).bind (execL r) = some c'.mem
    rw [he]; exact hex

/-- 按顺序的调度走得通，结果就是 `seqRun`。 -/
theorem run_seq (hI : IndepP T P []) (hA : AloneOk T P m0) (l : List POp) :
    ∀ {c : Cfg}, Reach T P m0 c → c.par = l → (∀ i ∈ spawns c.pp, c.rest i = []) →
    ∃ c', Reach T P m0 c' ∧ Final c' ∧ seqRun T l c.mem = some c'.mem := by
  induction l with
  | nil => intro c h hp hd; exact ⟨c, h, ⟨hp, hd⟩, rfl⟩
  | cons x r ih =>
    intro c h hp hd
    cases x with
    | op o =>
      obtain ⟨m', he⟩ := (safe T P m0 hI hA h).1 o r hp
      have h1 := Reach.step h (Step.parOp hp he)
      obtain ⟨c', h', hf, hs⟩ := ih h1 rfl (fun i hi => by
        have hi' : i ∈ spawns c.pp := by simpa [sp_op] using hi
        exact hd i hi')
      refine ⟨c', h', hf, ?_⟩
      show (exec o c.mem).bind (seqRun T r) = some c'.mem
      rw [he]; exact hs
    | spawn i =>
      have h1 := Reach.step h (Step.parSpawn (T := T) hp)
      obtain ⟨c2, h2, hpp, hpar, hri, hrj, hex⟩ :=
        run_task T P m0 hI hA (T i) (i := i) h1 (by simp [sp_spawn]) (by simp)
      obtain ⟨c', h', hf, hs⟩ := ih h2 hpar (fun j hj => by
        have hj' : j ∈ spawns c.pp ∨ j = i := by
          rw [hpp] at hj; simpa [sp_spawn] using hj
        by_cases hji : j = i
        · rw [hji]; exact hri
        · rw [hrj j hji]
          show upd c.rest i (T i) j = []
          rw [upd_other _ _ hji]
          exact hd j (hj'.resolve_right hji))
      refine ⟨c', h', hf, ?_⟩
      show (execL (T i) c.mem).bind (seqRun T r) = some c'.mem
      rw [show execL (T i) c.mem = some c2.mem from hex]; exact hs

/-- **`scope` 的意义就是按顺序执行**：任何调度下所有线程结束时，内存等于 `seqRun` 的结果。 -/
theorem scope_eq_seq (hI : IndepP T P []) (hA : AloneOk T P m0) {c : Cfg} (h : Reach T P m0 c)
    (hf : Final c) : seqRun T P m0 = some c.mem := by
  obtain ⟨c', h', hf', hs⟩ :=
    run_seq T P m0 hI hA P Reach.init rfl (fun i hi => by simp [init, spawns] at hi)
  rw [deterministic T P m0 hI hA h h' hf hf']
  exact hs

/-! ## 捕获规则 ⇒ 足迹不冲突

编译器的规则：任务 `i` 只读共享 `L i`（`let` 捕获），拥有 `O i`（`sink` 捕获和它自己的局部变量）；
它只写 `O i`、只碰 `L i ∪ O i`。`F` 是已经被只读共享的变量（直到 scope 结束都不能写），
`M` 是已经移进任务的变量（父任务不能再碰）。不能移动被共享的变量，不能共享或再移动已经移走的变量。 -/

def check (L O : Nat → List Var) : List POp → List Var → List Var → List Nat → Bool
  | [], _, _, _ => true
  | .op o :: r, F, M, S =>
    decide ((∀ x ∈ fp o, x ∉ M) ∧ (∀ x ∈ wr o, x ∉ F)) && check L O r F M S
  | .spawn i :: r, F, M, S =>
    decide (i ∉ S ∧ (∀ x ∈ L i, x ∉ M) ∧ (∀ x ∈ O i, x ∉ F ∧ x ∉ M) ∧
      (∀ x ∈ wrL (T i), x ∈ O i) ∧ (∀ x ∈ fpL (T i), x ∈ L i ∨ x ∈ O i)) &&
    check L O r (L i ++ F) (O i ++ M) (i :: S)

theorem check_indep (L O : Nat → List Var) (l : List POp) :
    ∀ F M S, (∀ j ∈ S, (∀ x ∈ wrL (T j), x ∈ O j) ∧ (∀ x ∈ fpL (T j), x ∈ L j ∨ x ∈ O j) ∧
      (∀ x ∈ L j, x ∈ F) ∧ (∀ x ∈ O j, x ∈ M)) →
    check T L O l F M S = true → IndepP T l S := by
  induction l with
  | nil => intro _ _ _ _ _; trivial
  | cons p r ih =>
    intro F M S hS h
    cases p with
    | op o =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hfM, hwF⟩, hr⟩ := h
      simp only [IndepP, CF]
      refine ⟨fun j hj => ⟨?_, ?_⟩, ih F M S hS hr⟩
      · intro x hx hxj
        rw [wrL_single] at hx
        obtain ⟨_, hfj, hLF, hOM⟩ := hS j hj
        rcases hfj x hxj with hxL | hxO
        · exact hwF x hx (hLF x hxL)
        · exact hfM x (wr_fp hx) (hOM x hxO)
      · intro x hxj hx
        rw [fpL_single] at hx
        obtain ⟨hwj, _, _, hOM⟩ := hS j hj
        exact hfM x hx (hOM x (hwj x hxj))
    | spawn i =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hiS, hLM, hOFM, hwO, hfLO⟩, hr⟩ := h
      simp only [IndepP, CF]
      refine ⟨hiS, fun j hj => ⟨?_, ?_⟩, ih _ _ _ ?_ hr⟩
      · intro x hx hxj
        obtain ⟨_, hfj, hLF, hOM⟩ := hS j hj
        have hxO := hwO x hx
        rcases hfj x hxj with hxL | hxO'
        · exact (hOFM x hxO).1 (hLF x hxL)
        · exact (hOFM x hxO).2 (hOM x hxO')
      · intro x hxj hx
        obtain ⟨hwj, _, _, hOM⟩ := hS j hj
        have hxM := hOM x (hwj x hxj)
        rcases hfLO x hx with hxL | hxO
        · exact hLM x hxL hxM
        · exact (hOFM x hxO).2 hxM
      · intro j hj
        rcases List.mem_cons.1 hj with e | hj
        · rw [e]
          exact ⟨hwO, hfLO, fun x hx => List.mem_append_left _ hx,
            fun x hx => List.mem_append_left _ hx⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hS j hj
          exact ⟨h1, h2, fun x hx => List.mem_append_right _ (h3 x hx),
            fun x hx => List.mem_append_right _ (h4 x hx)⟩

/-- **主定理**：捕获规则通过、每个线程单独执行不出错时，任何调度下都不出错、不死锁，
    结束时的内存就是按顺序执行的结果。 -/
theorem checked_scope (L O : Nat → List Var) (hk : check T L O P [] [] [] = true)
    (hA : AloneOk T P m0) {c : Cfg} (h : Reach T P m0 c) :
    ((∀ o r, c.par = .op o :: r → ∃ m', exec o c.mem = some m') ∧
     (∀ i o r, i ∈ spawns c.pp → c.rest i = o :: r → ∃ m', exec o c.mem = some m')) ∧
    (¬ Final c → ∃ c', Step T c c') ∧
    (Final c → seqRun T P m0 = some c.mem) := by
  have hI := check_indep T L O P [] [] [] (fun _ h => by simp at h) hk
  exact ⟨safe T P m0 hI hA h, progress T P m0 hI hA h, scope_eq_seq T P m0 hI hA h⟩

end Sched

/-! ## 例子（变量 0 是只读共享的 cfg，1 是移进任务的 conn） -/

/-- `let conn = …; s.spawn(|| handle(conn, cfg)); read cfg`：任务读 cfg、改写并释放 conn。接受。 -/
def Tok : Nat → List Op := fun i => if i = 1 then [.read 0, .write 1 8, .free 1] else []
def Lc : Nat → List Var := fun i => if i = 1 then [0] else []
def Oc : Nat → List Var := fun i => if i = 1 then [1] else []

example : check Tok Lc Oc [.op (.alloc 1 7), .spawn 1, .op (.read 0)] [] [] [] = true := by decide

/-- conn 移进任务之后父任务还写它：拒绝。 -/
example : check Tok Lc Oc [.op (.alloc 1 7), .spawn 1, .op (.write 1 9)] [] [] [] = false := by decide

/-- 任务写只读共享的 cfg：拒绝。 -/
def Tw : Nat → List Op := fun i => if i = 1 then [.write 0 5] else []
example : check Tw Lc Oc [.spawn 1, .op (.read 0)] [] [] [] = false := by decide

/-! ### 反例：数据竞争。任务把 cfg 复制到 1，同时父任务改写 cfg；两种调度结果不同，`check` 拒绝。 -/

def Tr : Nat → List Op := fun i => if i = 1 then [.copy 0 1] else []
def Pr : List POp := [.spawn 1, .op (.write 0 2)]
def mr : Mem := fun x => if x = 0 then some 1 else none

example : check Tr Lc Oc Pr [] [] [] = false := by decide

theorem race : ∃ c c', Reach Tr Pr mr c ∧ Reach Tr Pr mr c' ∧ Final c ∧ Final c' ∧
    c.mem 1 ≠ c'.mem 1 := by
  have h1 := Reach.step (Reach.init (T := Tr) (P := Pr) (m0 := mr))
    (Step.parSpawn (T := Tr) (c := init Tr Pr mr) (i := 1) (r := [.op (.write 0 2)]) rfl)
  -- 先任务后父任务：1 里是旧的 cfg
  have ha := Reach.step h1 (Step.task (i := 1) (o := .copy 0 1) (r := [])
    (m' := upd mr 1 (some 1)) (by decide) rfl rfl)
  have ha2 := Reach.step ha (Step.parOp (o := .write 0 2) (r := [])
    (m' := upd (upd mr 1 (some 1)) 0 (some 2)) rfl rfl)
  -- 先父任务后任务：1 里是新的 cfg
  have hb := Reach.step h1 (Step.parOp (o := .write 0 2) (r := [])
    (m' := upd mr 0 (some 2)) rfl rfl)
  have hb2 := Reach.step hb (Step.task (i := 1) (o := .copy 0 1) (r := [])
    (m' := upd (upd mr 0 (some 2)) 1 (some 2)) (by decide) rfl rfl)
  exact ⟨_, _, ha2, hb2, ⟨rfl, by decide⟩, ⟨rfl, by decide⟩, by decide⟩

end Core.Concurrency.Scope
