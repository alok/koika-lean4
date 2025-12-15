/-
  Koika/Semantics/Logs.lean - Port of coq/Logs.v
  Logs of reads and writes for tracking register access
-/

import Koika.Types

namespace Koika

/-! ## Log Entry Types -/

/-- Kind of log entry -/
inductive LogEntryKind where
  | read
  | write
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A single log entry recording a read or write -/
structure LogEntry (T : Type) where
  kind : LogEntryKind
  port : Port
  val : Option T  -- None for reads, Some v for writes
  deriving Repr

/-- A register log is a list of entries -/
abbrev RLog (T : Type) := List (LogEntry T)

/-! ## Read/Write Predicates -/

def isRead0 (k : LogEntryKind) (p : Port) : Bool :=
  k == .read && p == .p0

def isRead1 (k : LogEntryKind) (p : Port) : Bool :=
  k == .read && p == .p1

def isWrite0 (k : LogEntryKind) (p : Port) : Bool :=
  k == .write && p == .p0

def isWrite1 (k : LogEntryKind) (p : Port) : Bool :=
  k == .write && p == .p1

/-! ## Simple Log Structure -/

/-- A log maps each register to a list of entries.
    Each entry stores a dependent pair of (register, value). -/
structure SimpleLog {reg_t : Type} (R : reg_t → Type) where
  entries : reg_t → List (LogEntry (Σ r : reg_t, R r))

namespace SimpleLog

variable {reg_t : Type} [DecidableEq reg_t] {R : reg_t → Type}

instance : Inhabited (SimpleLog R) := ⟨⟨fun _ => []⟩⟩

/-- Empty log -/
def empty : SimpleLog R := ⟨fun _ => []⟩

/-- Add an entry to a register's log -/
def cons (r : reg_t) (kind : LogEntryKind) (port : Port)
    (val : Option (R r)) (l : SimpleLog R) : SimpleLog R :=
  ⟨fun r' =>
    if r = r' then
      ⟨kind, port, val.map fun v => ⟨r, v⟩⟩ :: l.entries r'
    else
      l.entries r'⟩

/-- Check if any entry for a register satisfies a predicate -/
def existsb (l : SimpleLog R) (r : reg_t)
    (f : LogEntryKind → Port → Bool) : Bool :=
  (l.entries r).any fun e => f e.kind e.port

/-- Check if all entries for a register satisfy a predicate -/
def forallb (l : SimpleLog R) (r : reg_t)
    (f : LogEntryKind → Port → Bool) : Bool :=
  (l.entries r).all fun e => f e.kind e.port

/-- Append two logs -/
def append (l1 l2 : SimpleLog R) : SimpleLog R :=
  ⟨fun r => l1.entries r ++ l2.entries r⟩

/-- Find latest write on port 0 for a register -/
def latestWrite0 (l : SimpleLog R) (r : reg_t) : Option (R r) :=
  (l.entries r).findSome? fun e =>
    if e.kind == .write && e.port == .p0 then
      e.val.bind fun ⟨r', v⟩ =>
        if h : r' = r then some (h ▸ v) else none
    else none

/-- Find latest write on port 1 for a register -/
def latestWrite1 (l : SimpleLog R) (r : reg_t) : Option (R r) :=
  (l.entries r).findSome? fun e =>
    if e.kind == .write && e.port == .p1 then
      e.val.bind fun ⟨r', v⟩ =>
        if h : r' = r then some (h ▸ v) else none
    else none

/-- Find latest write (any port) for a register -/
def latestWrite (l : SimpleLog R) (r : reg_t) : Option (R r) :=
  (l.entries r).findSome? fun e =>
    if e.kind == .write then
      e.val.bind fun ⟨r', v⟩ =>
        if h : r' = r then some (h ▸ v) else none
    else none

/-- Check if reading from a register is allowed -/
def mayRead (schedLog : SimpleLog R) (port : Port) (r : reg_t) : Bool :=
  match port with
  | .p0 => !schedLog.existsb r isWrite0 && !schedLog.existsb r isWrite1
  | .p1 => !schedLog.existsb r isWrite1

/-- Check if writing to a register is allowed -/
def mayWrite (schedLog ruleLog : SimpleLog R) (port : Port) (r : reg_t) : Bool :=
  let combined := ruleLog.append schedLog
  match port with
  | .p0 => !combined.existsb r isRead1 &&
           !combined.existsb r isWrite0 &&
           !combined.existsb r isWrite1
  | .p1 => !combined.existsb r isWrite1

end SimpleLog

/-! ## Commit Updates -/

/-- Commit log updates to register state -/
def commitUpdate {reg_t : Type} [DecidableEq reg_t] {R : reg_t → Type}
    (r0 : (r : reg_t) → R r) (log : SimpleLog R) : (r : reg_t) → R r :=
  fun r =>
    match log.latestWrite r with
    | some v => v
    | none => r0 r

end Koika
