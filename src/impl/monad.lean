import impl.doc

namespace Impl

open ServerModel (Message)
open AbstractModel (ServerConfig)

structure Env where
  origin   : String
  snapshot : Option (OriginDoc × Cas.Version)
  mat      : Bool
  config   : ServerConfig := {}

def Env.cond (e : Env) : Cas.Cond :=
  match e.snapshot with
  | some (_, v) => .version v
  | none        => .absent

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

def applyEffects (origin : String) (cond : Cas.Cond) : World → List Effect → World × Bool
  | w, []      => (w, true)
  | w, f :: fs =>
      match f.apply origin cond w with
      | .ok w'    => applyEffects origin cond w' fs
      | .rejected => (w, false)

def runC (act : C α) (e : Env) (w : World) : Option α × World :=
  let (a, fx) := act e
  let (w', ok) := applyEffects e.origin e.cond w fx
  (if ok then some a else none, w')

end Impl
