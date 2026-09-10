import impl.refinement

/-!  # A run, and its linearization

One scenario through the implementation, printed: what the bucket holds,
what the wire carries, what a client saw — and the specification run the
refinement says it stands for.

Origin `o`. A worker creates and acquires a task (`taskCreate`), a client
reads the promise and the worker releases the task; the two transactions
overlap, and the release commits first. The client's read then commits
against a stale snapshot and is refused by the CAS — no answer, and the
shell would re-decide. Finally the timer daemon, woken by the retry key
the release armed, sweeps the origin: the task is re-dispatched, an
`execute` message reaches the wire, the retry is re-armed, and the promise
timeout is now the nearest deadline.

`lake build impl.demo` prints the four evaluations. -/

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
  , (.commit 1, 300)      -- the release commits first
  , (.commit 0, 400)      -- the read's snapshot is stale: refused, silent
  , (.begin "o" (.sweep (some 300)), 5000)
  , (.commit 0, 6000) ]

def result := Impl.run true scenario State.init

-- What a client saw: two answers. The refused read is not among them.
#eval result.1.map fun ob => (ob.now, ob.res)

-- What the bucket holds: the document and the one armed timer key.
#eval result.2.world.store.entries.map (·.1)

-- What the wire carries: the `execute` the sweep dispatched.
#eval result.2.world.wire

-- The specification run this stands for: the two external steps, and the
-- internal steps each commit's sweep performed.
#eval (Refinement.linearize true scenario State.init).map fun (st, n) =>
  (n, match st with
      | .external rq => s!"external {repr rq |>.pretty 200 |>.take 40}…"
      | .internal st => s!"internal {repr st |>.pretty 200}"
      | .idle => "idle")

end Impl.Demo
