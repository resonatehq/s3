import impl.refinement

namespace Impl.Demo

open ServerModel Equivalence Impl

def oid (s : String) : Ident := { origin := "o", suffix := s }

def scenario : List (Step × Nat) :=
  [ (.begin "o" (.request (.taskCreate
      { pid := "p1", ttl := 1000,
        action := { id := oid "root", timeoutAt := 10000, param := {},
                    tags := [("resonate:target", "w1")] } })), 0)
  , (.commit 0, 100)
  , (.begin "o" (.request (.promiseGet { id := oid "root" })), 200)
  , (.begin "o" (.request (.taskRelease { id := oid "root", version := 1 })), 200)
  , (.commit 1, 300)
  , (.commit 0, 400)
  , (.begin "o" (.sweep (some 300)), 5000)
  , (.commit 0, 6000) ]

def result := Impl.run true scenario State.init

#eval result.1.map fun ob => (ob.now, ob.res)

#eval result.2.world.store.entries.map (·.1)

#eval result.2.world.wire

#eval (Refinement.linearize true scenario State.init).map fun (st, n) =>
  (n, match st with
      | .external rq => s!"external {repr rq |>.pretty 200 |>.take 40}…"
      | .internal st => s!"internal {repr st |>.pretty 200}"
      | .idle => "idle")

end Impl.Demo
