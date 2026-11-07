-- 由 sinterc --emit=core 生成，不要手工修改。
import Core.C5
set_option maxRecDepth 100000
open Core.M7h

/-- get -/
def f0 : CFG := [
  ⟨.nop, [], false⟩]

/-- inc -/
def f1 : CFG := [
  ⟨.nop, [], false⟩]

/-- reset -/
def f2 : CFG := [
  ⟨.cmd (.base (.own (.c (.base (.alloc 0))))), [1], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 0))))), [2], false⟩,
  ⟨.nop, [], false⟩]

/-- sum -/
def f3 : CFG := [
  ⟨.nop, [], false⟩]

/-- main -/
def f4 : CFG := [
  ⟨.cmd (.base (.own (.c (.base (.alloc 0))))), [1], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 0 1))))), [2], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.read, 1⟩] []))), [3], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.inout, 1⟩] []))), [4], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.read, 1⟩] []))), [5], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 2))))), [6], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 2))))), [7], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 3))))), [8], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 3 4))))), [9], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.read, 4⟩, ⟨.read, 4⟩] []))), [10], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.use 4))))), [11], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.use 4))))), [12], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.use 4))))), [13], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 5))))), [14], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 5))))), [15], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 6))))), [16], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 6 7))))), [17], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.use 7))))), [18], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.read, 7⟩] []))), [19], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 8))))), [20], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 8))))), [21], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 9))))), [22], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 7))))), [23], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 9 7))))), [24], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.read, 7⟩] []))), [25], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.inout, 7⟩] []))), [26], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.read, 7⟩] []))), [27], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 10))))), [28], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 10 11))))), [29], false⟩,
  ⟨.cmd (.base (.own (.call [⟨.read, 11⟩] []))), [30], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 11))))), [31], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 7))))), [32], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 4))))), [33], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 1))))), [34], false⟩,
  ⟨.nop, [], false⟩]

#eval Core.C5.report [("get", 1, f0), ("inc", 1, f1), ("reset", 1, f2), ("sum", 1, f3), ("main", 12, f4)] true
