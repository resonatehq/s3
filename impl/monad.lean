import impl.doc

/-!  # The implementation's monad — one transaction against one document

The specification writes every step in `H`: a reader of the state, a
writer of `Effect`s, folded onto the state at the end. The
implementation writes every commit in `C`, which has the same shape and
a different vocabulary.

What `C` READS is a snapshot: the one document a transaction began by
fetching, with the version it was fetched at — or the fact that there
was no document. Nothing else in the bucket is visible; nothing
written during the transaction is visible either, because `bind` hands
the same environment to its continuation, exactly as the
specification's `H` does. One transaction is one read.

What `C` WRITES is what the S3 shell performs:

  `putDoc d`      the whole document, CONDITIONALLY — against the version
                  the snapshot was read at, or against absence if there
                  was none. This is the one write that can be refused.
  `armTimer at`   an unconditional PUT of the timer key for `at`.
  `delTimer at`   a DELETE of that key.
  `send a m`      a message to the transport.

The effects are applied IN ORDER, and the order is load-bearing: arm the
new timer before the document is committed, so a crash between the two
leaves an orphan timer (harmless — firing it sweeps a document with
nothing due) rather than a document with an uncovered deadline; delete
the old timer only after the commit it belonged to is gone; send only
after the commit, so no worker learns of a state that did not land.

A REFUSED `putDoc` stops the transaction there. The effects before it
have landed — that is the orphan-timer case above — and the effects
after it are dropped. The caller gets no answer and re-decides against
the fresh document; nothing was applied twice and nothing stale was
applied at all. That is the whole concurrency story, and `system.lean`
is where it is shown to be enough. -/

namespace Impl

open ServerModel (Message)
open AbstractModel (ServerConfig)

/-- What a transaction sees. -/
structure Env where
  origin   : String
  snapshot : Option (OriginDoc × Cas.Version)
  mat      : Bool
  config   : ServerConfig := {}

/-- The condition the document write is made under: the version the
    snapshot was read at, or absence. -/
def Env.cond (e : Env) : Cas.Cond :=
  match e.snapshot with
  | some (_, v) => .version v
  | none        => .absent

/-- The document the transaction decides against: the snapshot, or the
    empty document for an origin that has never been written. -/
def Env.doc (e : Env) : OriginDoc :=
  match e.snapshot with
  | some (d, _) => d
  | none        => {}

inductive Effect
  | putDoc   (d : OriginDoc)
  | armTimer (dl : Nat)
  | delTimer (dl : Nat)
  | send     (address : String) (msg : Message)
  deriving Repr

def C (α : Type) : Type := Env → α × List Effect

instance : Monad C where
  pure a   := fun _ => (a, [])
  bind x f := fun e =>
    let (a, w₁) := x e
    let (b, w₂) := f a e
    (b, w₁ ++ w₂)

def ask : C Env := fun e => (e, [])

def emit (f : Effect) : C Unit := fun _ => ((), [f])

def putDoc (d : OriginDoc) : C Unit := emit (.putDoc d)
def armTimer (dl : Nat) : C Unit := emit (.armTimer dl)
def delTimer (dl : Nat) : C Unit := emit (.delTimer dl)
def send (address : String) (msg : Message) : C Unit := emit (.send address msg)

def sendAll : List (String × Message) → C Unit
  | []             => pure ()
  | (a, m) :: rest => do send a m; sendAll rest

/-! ## Performing the effects -/

/-- One effect against the world. Only `putDoc` can be refused. -/
def Effect.apply (origin : String) (cond : Cas.Cond) (w : World) :
    Effect → Cas.Outcome World
  | .putDoc d =>
      match w.store.put (.doc origin) (.doc d) cond with
      | .ok (s, _) => .ok { w with store := s }
      | .rejected  => .rejected
  | .armTimer dl =>
      match w.store.put (.timer dl origin) .timer .any with
      | .ok (s, _) => .ok { w with store := s }
      | .rejected  => .rejected
  | .delTimer dl =>
      match w.store.del (.timer dl origin) .any with
      | .ok s     => .ok { w with store := s }
      | .rejected => .rejected
  | .send a m => .ok (w.send a m)

/-- Apply effects in order, stopping at the first refusal. Returns the
    world as it stands — including whatever landed before the refusal —
    and whether everything landed. -/
def applyEffects (origin : String) (cond : Cas.Cond) : World → List Effect → World × Bool
  | w, []      => (w, true)
  | w, f :: fs =>
      match f.apply origin cond w with
      | .ok w'    => applyEffects origin cond w' fs
      | .rejected => (w, false)

/-- Run a transaction: decide from the environment, perform the effects.
    The answer is delivered only if every effect landed. -/
def runC (act : C α) (e : Env) (w : World) : Option α × World :=
  let (a, fx) := act e
  let (w', ok) := applyEffects e.origin e.cond w fx
  (if ok then some a else none, w')

end Impl
