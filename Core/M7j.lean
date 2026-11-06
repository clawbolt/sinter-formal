import Core.M7i

/-!
# M7（七·上）：降级正确——模拟关系

目标：结构化程序 `p` 和它降级后的 CFG `lower p` 执行结果**完全相同**（同一个结束状态、同一个剩余选择序列）。
这一轮先证明“从嵌入关系出发的模拟”；下一轮证明 `lower` 产生的 CFG 满足嵌入关系。

**嵌入关系** `Emb g q i k e`：程序片段 `q` 在 CFG `g` 里以节点 `i` 为入口，正常结束走到 `k`，出错退出走到 `e`。
它的每条规则和 M7（六）的 `lw` 一一对应。

**模拟** `sim`：`Emb g q i k e` 时，结构化执行 `exec n q st cs`
- 正常结束于 `(st', cs')` ⇒ CFG 从 `(i, st, cs)` 走若干步到 `(k, st', cs')`；
- 出错退出于 `(st', cs')` ⇒ CFG 走到 `(e, st', cs')`；
- 运行出错 ⇒ CFG 走到某个执行出错的节点。

块的 `leave` 节点用“当前深度减一”离开区域，结构化执行用“进入前的深度”；
二者相同靠 `exec_d`：执行不改变区域深度。

**本轮主定理** `sim_run`：入口、正常出口、出错出口三个节点就位时，结构化执行只要没有耗尽燃料，
CFG 用足够的燃料执行得到**同一个结果**。
-/

namespace Core.M7j
open Core.M7d (C4 Q St Res exec execC4 enterSt leaveSt)
open Core.M7h (Op Node CFG stepOp run)
open Core.M7g (pick)

/-! ## 嵌入关系 -/

inductive Emb (g : CFG) : Q → Nat → Nat → Nat → Prop
  | skip {k e : Nat} : Emb g .skip k k e
  | cmd {c : C4} {i k e : Nat} :
      g[i]? = some ⟨.cmd c, [k], false⟩ → Emb g (.cmd c) i k e
  | seq {p q : Q} {i j k e : Nat} :
      Emb g q j k e → Emb g p i j e → Emb g (.seq p q) i k e
  | branch {p q : Q} {i ip iq k e : Nat} :
      Emb g p ip k e → Emb g q iq k e → g[i]? = some ⟨.nop, [ip, iq], false⟩ →
      Emb g (.branch p q) i k e
  | loop {b : Q} {h ib k e : Nat} :
      g[h]? = some ⟨.nop, [ib, k], false⟩ → Emb g b ib h e → Emb g (.loop b) h k e
  | fail {k e : Nat} : Emb g .fail e k e
  | guard {x : Var} {p : Q} {r i c k e : Nat} :
      g[c]? = some ⟨.cmd (.base (.lin (.consume x))), [e], false⟩ → Emb g p i k c →
      g[r]? = some ⟨.nop, [i], false⟩ → Emb g (.guard x p) r k e
  | block {p : Q} {i ip l le k e : Nat} :
      g[l]? = some ⟨.leave, [k], false⟩ → g[le]? = some ⟨.leave, [e], false⟩ →
      Emb g p ip l le → g[i]? = some ⟨.enter, [ip], false⟩ → Emb g (.block p) i k e

/-! ## CFG 上的多步执行 -/

abbrev Cfg := Nat × St × List Bool

inductive StepsN (g : CFG) : Nat → Cfg → Cfg → Prop
  | refl (c : Cfg) : StepsN g 0 c c
  | step {pc t n : Nat} {st st' : St} {cs cs' : List Bool} {nd : Node} {c : Cfg} :
      g[pc]? = some nd → stepOp st nd.op = some st' → pick nd.succ cs = some (t, cs') →
      StepsN g n (t, st', cs') c → StepsN g (n + 1) (pc, st, cs) c

theorem step1 {g : CFG} {pc t : Nat} {st st' : St} {cs cs' : List Bool} {nd : Node}
    (hn : g[pc]? = some nd) (hs : stepOp st nd.op = some st') (hp : pick nd.succ cs = some (t, cs')) :
    StepsN g 1 (pc, st, cs) (t, st', cs') :=
  .step hn hs hp (.refl _)

theorem steps_trans {g : CFG} {a : Nat} {c1 c2 : Cfg} (h1 : StepsN g a c1 c2) :
    ∀ {b : Nat} {c3 : Cfg}, StepsN g b c2 c3 → StepsN g (a + b) c1 c3 := by
  induction h1 with
  | refl => intro b c3 h2; simpa using h2
  | step hn hs hp _ ih =>
    intro b c3 h2
    rw [Nat.add_right_comm]
    exact .step hn hs hp (ih h2)

theorem run_steps {g : CFG} {n : Nat} {c c' : Cfg} (h : StepsN g n c c') :
    ∀ m, run g (n + m) c.1 c.2.1 c.2.2 = run g m c'.1 c'.2.1 c'.2.2 := by
  induction h with
  | refl => intro m; simp
  | step hn hs hp _ ih =>
    intro m
    rw [Nat.add_right_comm]
    simp only [run, hn, hs, hp]
    exact ih m

theorem run_steps' {g : CFG} {n pc pc' : Nat} {st st' : St} {cs cs' : List Bool}
    (h : StepsN g n (pc, st, cs) (pc', st', cs')) (m : Nat) :
    run g (n + m) pc st cs = run g m pc' st' cs' :=
  run_steps h m

/-! ## 执行不改变区域深度 -/

theorem exec1_rs {s s' : Core.M5b.St} {c : Core.M5b.Cmd} (h : Core.M5b.exec1 s c = some s') :
    s'.rs = s.rs := by
  cases c with
  | decl x k => simp only [Core.M5b.exec1] at h; cases h; rfl
  | ralloc x j =>
    simp only [Core.M5b.exec1] at h
    split at h
    · cases h; rfl
    · contradiction
  | copy x y => simp only [Core.M5b.exec1] at h; cases h; rfl
  | read x =>
    simp only [Core.M5b.exec1] at h
    split at h
    · split at h
      · cases h; rfl
      · contradiction
    · contradiction
  | cdecl c k => simp only [Core.M5b.exec1] at h; cases h; rfl
  | cview v c k => simp only [Core.M5b.exec1] at h; cases h; rfl
  | cset v x =>
    simp only [Core.M5b.exec1] at h
    split at h
    · cases h; rfl
    · contradiction
  | cget c y => simp only [Core.M5b.exec1] at h; cases h; rfl

theorem execC4_d {s s' : St} {c : C4} (h : execC4 s c = some s') : s'.r.rs.d = s.r.rs.d := by
  cases c with
  | base c =>
    simp only [execC4] at h
    split at h
    · cases h; rfl
    · contradiction
  | reg c =>
    simp only [execC4] at h
    split at h
    · rename_i r' h₁
      cases h
      show r'.rs.d = s.r.rs.d
      rw [exec1_rs h₁]
    · contradiction

def DR (d : Nat) : Res → Prop
  | .ok s _  => s.r.rs.d = d
  | .exn s _ => s.r.rs.d = d
  | _        => True

theorem exec_d (n : Nat) : ∀ (q : Q) (st : St) (cs : List Bool), DR st.r.rs.d (exec n q st cs) := by
  induction n with
  | zero => intro q st cs; simp [exec, DR]
  | succ n ih =>
    intro q st cs
    cases q with
    | skip => simp [exec, DR]
    | cmd c =>
      cases h : execC4 st c with
      | none => simp [exec, h, DR]
      | some s' =>
        simp only [exec, h, DR]
        exact execC4_d h
    | seq p q =>
      have h1 := ih p st cs
      cases h : exec n p st cs with
      | ok s1 cs1 =>
        rw [h] at h1
        simp only [DR] at h1
        simp only [exec, h]
        have h2 := ih q s1 cs1
        rw [h1] at h2
        exact h2
      | exn s1 cs1 =>
        rw [h] at h1
        simp only [exec, h]
        exact h1
      | err => simp [exec, h, DR]
      | oof => simp [exec, h, DR]
    | branch p q =>
      simp only [exec]
      split
      · exact ih p st cs.tail
      · exact ih q st cs.tail
    | loop b =>
      simp only [exec]
      split
      · have h1 := ih b st cs.tail
        cases h : exec n b st cs.tail with
        | ok s1 cs1 =>
          rw [h] at h1
          simp only [DR] at h1
          show DR st.r.rs.d (exec n (.loop b) s1 cs1)
          have h2 := ih (.loop b) s1 cs1
          rw [h1] at h2
          exact h2
        | exn s1 cs1 =>
          rw [h] at h1
          exact h1
        | err => simp [DR]
        | oof => simp [DR]
      · simp [DR]
    | fail => simp [exec, DR]
    | guard x p =>
      have h1 := ih p st cs
      cases h : exec n p st cs with
      | exn s1 cs1 =>
        rw [h] at h1
        simp only [DR] at h1
        cases h2 : Core.M6.execS s1.m.l (.consume x) with
        | none => simp [exec, h, h2, DR]
        | some l' =>
          simp only [exec, h, h2, DR]
          exact h1
      | ok s1 cs1 =>
        rw [h] at h1
        simp only [exec, h]
        exact h1
      | err => simp [exec, h, DR]
      | oof => simp [exec, h, DR]
    | block p =>
      cases h : exec n p (enterSt st) cs with
      | ok s1 cs1 => simp [exec, h, DR, leaveSt, Core.M5.leaveR]
      | exn s1 cs1 => simp [exec, h, DR, leaveSt, Core.M5.leaveR]
      | err => simp [exec, h, DR]
      | oof => simp [exec, h, DR]

/-- 两个后继时按选择序列的第一个值选边（不展开 `headD`，避免 `simp` 把它改写成别的形式）。 -/
theorem pick2 {a b : Nat} {cs : List Bool} (hc : cs.headD false = true) :
    pick [a, b] cs = some (a, cs.tail) := by
  simp only [pick]
  rw [ite_eq_left hc]

theorem pick2n {a b : Nat} {cs : List Bool} (hc : ¬cs.headD false = true) :
    pick [a, b] cs = some (b, cs.tail) := by
  simp only [pick]
  rw [ite_eq_right hc]


/-! ## 模拟 -/

def Sim (g : CFG) (i k e : Nat) (st : St) (cs : List Bool) : Res → Prop
  | .ok st' cs'  => ∃ n, StepsN g n (i, st, cs) (k, st', cs')
  | .exn st' cs' => ∃ n, StepsN g n (i, st, cs) (e, st', cs')
  | .err         => ∃ n pc st₁ cs₁ nd, StepsN g n (i, st, cs) (pc, st₁, cs₁) ∧
                      g[pc]? = some nd ∧ stepOp st₁ nd.op = none
  | .oof         => True

theorem sim_prepend {g : CFG} {a i j k e : Nat} {st s1 : St} {cs cs1 : List Bool} {r : Res}
    (h : StepsN g a (i, st, cs) (j, s1, cs1)) (s : Sim g j k e s1 cs1 r) : Sim g i k e st cs r := by
  cases r with
  | ok st' cs' =>
    simp only [Sim] at s ⊢
    obtain ⟨b, hb⟩ := s
    exact ⟨a + b, steps_trans h hb⟩
  | exn st' cs' =>
    simp only [Sim] at s ⊢
    obtain ⟨b, hb⟩ := s
    exact ⟨a + b, steps_trans h hb⟩
  | err =>
    simp only [Sim] at s ⊢
    obtain ⟨b, pc, st₁, cs₁, nd, hb, hn, hs⟩ := s
    exact ⟨a + b, pc, st₁, cs₁, nd, steps_trans h hb, hn, hs⟩
  | oof => simp [Sim]

theorem sim (g : CFG) (n : Nat) : ∀ (q : Q) (i k e : Nat) (st : St) (cs : List Bool),
    Emb g q i k e → Sim g i k e st cs (exec n q st cs) := by
  induction n with
  | zero => intro q i k e st cs _; simp [exec, Sim]
  | succ n ih =>
    intro q i k e st cs hq
    cases hq with
    | skip =>
      simp only [exec, Sim]
      exact ⟨0, .refl _⟩
    | cmd hi =>
      rename_i c
      cases hc : execC4 st c with
      | none =>
        simp only [exec, hc, Sim]
        exact ⟨0, i, st, cs, _, .refl _, hi, hc⟩
      | some s' =>
        simp only [exec, hc, Sim]
        exact ⟨1, step1 hi hc rfl⟩
    | seq hq hp =>
      rename_i p q j
      have g1 := ih p i j e st cs hp
      cases h1 : exec n p st cs with
      | ok s1 cs1 =>
        rw [h1] at g1
        simp only [Sim] at g1
        obtain ⟨a, ha⟩ := g1
        simp only [exec, h1]
        exact sim_prepend ha (ih q j k e s1 cs1 hq)
      | exn s1 cs1 =>
        rw [h1] at g1
        simp only [exec, h1]
        simp only [Sim] at g1 ⊢
        exact g1
      | err =>
        rw [h1] at g1
        simp only [exec, h1]
        simp only [Sim] at g1 ⊢
        exact g1
      | oof => simp only [exec, h1, Sim]
    | branch hp hq hi =>
      rename_i p q ip iq
      simp only [exec]
      by_cases hc : cs.headD false = true
      · rw [ite_eq_left hc]
        exact sim_prepend (step1 hi rfl (pick2 hc)) (ih p ip k e st cs.tail hp)
      · rw [ite_eq_right hc]
        exact sim_prepend (step1 hi rfl (pick2n hc)) (ih q iq k e st cs.tail hq)
    | loop hi hb =>
      rename_i b ib
      simp only [exec]
      by_cases hc : cs.headD false = true
      · rw [ite_eq_left hc]
        have s0 : StepsN g 1 (i, st, cs) (ib, st, cs.tail) := step1 hi rfl (pick2 hc)
        have g1 := ih b ib i e st cs.tail hb
        cases h1 : exec n b st cs.tail with
        | ok s1 cs1 =>
          rw [h1] at g1
          simp only [Sim] at g1
          obtain ⟨a, ha⟩ := g1
          show Sim g i k e st cs (exec n (.loop b) s1 cs1)
          exact sim_prepend (steps_trans s0 ha) (ih (.loop b) i k e s1 cs1 (.loop hi hb))
        | exn s1 cs1 =>
          rw [h1] at g1
          simp only [Sim] at g1 ⊢
          obtain ⟨a, ha⟩ := g1
          exact ⟨1 + a, steps_trans s0 ha⟩
        | err =>
          rw [h1] at g1
          simp only [Sim] at g1 ⊢
          obtain ⟨a, pc, st₁, cs₁, nd, ha, hn, hs⟩ := g1
          exact ⟨1 + a, pc, st₁, cs₁, nd, steps_trans s0 ha, hn, hs⟩
        | oof => simp only [Sim]
      · rw [ite_eq_right hc]
        simp only [Sim]
        exact ⟨1, step1 hi rfl (pick2n hc)⟩
    | fail =>
      simp only [exec, Sim]
      exact ⟨0, .refl _⟩
    | guard hc hp hr =>
      rename_i x p i' c
      have s0 : StepsN g 1 (i, st, cs) (i', st, cs) := step1 hr rfl rfl
      have g1 := ih p i' k c st cs hp
      cases h1 : exec n p st cs with
      | ok s1 cs1 =>
        rw [h1] at g1
        simp only [Sim] at g1
        obtain ⟨a, ha⟩ := g1
        simp only [exec, h1, Sim]
        exact ⟨1 + a, steps_trans s0 ha⟩
      | exn s1 cs1 =>
        rw [h1] at g1
        simp only [Sim] at g1
        obtain ⟨a, ha⟩ := g1
        cases h2 : Core.M6.execS s1.m.l (.consume x) with
        | none =>
          simp only [exec, h1, h2, Sim]
          exact ⟨1 + a, c, s1, cs1, _, steps_trans s0 ha, hc,
            by simp [stepOp, execC4, Core.M7b.execC, h2]⟩
        | some l' =>
          simp only [exec, h1, h2, Sim]
          exact ⟨1 + a + 1, steps_trans (steps_trans s0 ha)
            (step1 hc (by simp [stepOp, execC4, Core.M7b.execC, h2]) rfl)⟩
      | err =>
        rw [h1] at g1
        simp only [exec, h1, Sim]
        simp only [Sim] at g1
        obtain ⟨a, pc, st₁, cs₁, nd, ha, hn, hs⟩ := g1
        exact ⟨1 + a, pc, st₁, cs₁, nd, steps_trans s0 ha, hn, hs⟩
      | oof => simp only [exec, h1, Sim]
    | block hl hle hp hi =>
      rename_i p ip l le
      have s0 : StepsN g 1 (i, st, cs) (ip, enterSt st, cs) := step1 hi rfl rfl
      have g1 := ih p ip l le (enterSt st) cs hp
      have hd := exec_d n p (enterSt st) cs
      have hen : (enterSt st).r.rs.d = st.r.rs.d + 1 := rfl
      cases h1 : exec n p (enterSt st) cs with
      | ok s1 cs1 =>
        rw [h1] at g1 hd
        simp only [Sim] at g1
        simp only [DR] at hd
        obtain ⟨a, ha⟩ := g1
        have hd' : s1.r.rs.d = st.r.rs.d + 1 := hd.trans hen
        have hlv : stepOp s1 .leave = some (leaveSt st.r.rs.d s1) := by simp [stepOp, hd']
        simp only [exec, h1, Sim]
        exact ⟨1 + a + 1, steps_trans (steps_trans s0 ha) (step1 hl hlv rfl)⟩
      | exn s1 cs1 =>
        rw [h1] at g1 hd
        simp only [Sim] at g1
        simp only [DR] at hd
        obtain ⟨a, ha⟩ := g1
        have hd' : s1.r.rs.d = st.r.rs.d + 1 := hd.trans hen
        have hlv : stepOp s1 .leave = some (leaveSt st.r.rs.d s1) := by simp [stepOp, hd']
        simp only [exec, h1, Sim]
        exact ⟨1 + a + 1, steps_trans (steps_trans s0 ha) (step1 hle hlv rfl)⟩
      | err =>
        rw [h1] at g1
        simp only [exec, h1, Sim]
        simp only [Sim] at g1
        obtain ⟨a, pc, st₁, cs₁, nd, ha, hn, hs⟩ := g1
        exact ⟨1 + a, pc, st₁, cs₁, nd, steps_trans s0 ha, hn, hs⟩
      | oof => simp only [exec, h1, Sim]

/-! ## 本轮主定理 -/

/-- 入口节点 0 指向 `q` 的入口，节点 1、2 是正常出口和出错出口时：结构化执行没有耗尽燃料，
CFG 用足够的燃料执行得到同一个结果（同一个结束状态、同一个剩余选择序列）。 -/
theorem sim_run {g : CFG} {q : Q} {i : Nat} (hq : Emb g q i 1 2)
    (h0 : g[0]? = some ⟨.nop, [i], false⟩) (h1 : g[1]? = some ⟨.nop, [], false⟩)
    (h2 : g[2]? = some ⟨.nop, [], true⟩)
    (n : Nat) (st : St) (cs : List Bool) (hr : exec n q st cs ≠ .oof) :
    ∃ m, run g m 0 st cs = exec n q st cs := by
  have s := sim g n q i 1 2 st cs hq
  have s0 : StepsN g 1 (0, st, cs) (i, st, cs) := step1 h0 rfl rfl
  cases hx : exec n q st cs with
  | ok st' cs' =>
    rw [hx] at s
    simp only [Sim] at s
    obtain ⟨a, ha⟩ := s
    refine ⟨1 + a + 1, ?_⟩
    rw [run_steps' (steps_trans s0 ha) 1]
    simp [run, h1, stepOp, pick]
  | exn st' cs' =>
    rw [hx] at s
    simp only [Sim] at s
    obtain ⟨a, ha⟩ := s
    refine ⟨1 + a + 1, ?_⟩
    rw [run_steps' (steps_trans s0 ha) 1]
    simp [run, h2, stepOp, pick]
  | err =>
    rw [hx] at s
    simp only [Sim] at s
    obtain ⟨a, pc, st₁, cs₁, nd, ha, hn, hs⟩ := s
    refine ⟨1 + a + 1, ?_⟩
    rw [run_steps' (steps_trans s0 ha) 1]
    simp [run, hn, hs]
  | oof => exact absurd hx hr

end Core.M7j
