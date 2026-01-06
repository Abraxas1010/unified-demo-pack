import Lean
import Lean.Data.Json

open Lean

structure GNode where
  id    : Nat
  kind  : String
  depth : Nat
  label : String
deriving Repr

structure GEdge where
  src   : Nat
  dst   : Nat
  label : String := ""
deriving Repr

structure GState where
  next : Nat := 0
  nodes : Array GNode := #[]
  edges : Array GEdge := #[]

abbrev GM := StateM GState

private def walkFuel (fuel : Nat) (e : Expr) (depth : Nat) : GM Nat := do
  match fuel with
  | 0 =>
      let id := (← get).next
      modify fun s => { s with next := s.next + 1, nodes := s.nodes.push { id, kind := "term", depth, label := "_" } }
      return id
  | fuel + 1 =>
      let kind : String :=
        match e with
        | .forallE .. => "forall"
        | .lam ..     => "lam"
        | .app ..     => "app"
        | .const ..   => "const"
        | .sort ..    => "sort"
        | .letE ..    => "let"
        | .mdata ..   => "mdata"
        | .proj ..    => "proj"
        | _           => "term"
      let label : String :=
        match e with
        | .const n _ => n.toString
        | .sort _    => "Sort"
        | .forallE n _ _ _ => s!"∀ {n}"
        | .lam n _ _ _     => s!"λ {n}"
        | .proj n i _      => s!"proj {n}:{i}"
        | _                => ""
      let id := (← get).next
      modify fun s => { s with next := s.next + 1, nodes := s.nodes.push { id, kind, depth, label } }
      let attach (child : Expr) (lbl : String := "") : GM Unit := do
        let cid ← walkFuel fuel child (depth + 1)
        modify fun s => { s with edges := s.edges.push { src := id, dst := cid, label := lbl } }
      match e with
      | .forallE _ ty b _ => do attach ty "ty"; attach b "body"
      | .lam _ ty b _     => do attach ty "ty"; attach b "body"
      | .app f a          => do attach f "f"; attach a "a"
      | .letE _ ty v b _  => do attach ty "ty"; attach v "val"; attach b "body"
      | .mdata _ b        => do attach b "m"
      | .proj _ _ b       => do attach b "struct"
      | _                 => pure ()
      return id

def walk (e : Expr) (depth : Nat) (fuel : Nat := 512) : GM Nat :=
  walkFuel fuel e depth

def jsonOf (nodes : Array GNode) (edges : Array GEdge) (root : Nat) : Json :=
  Json.mkObj
    [ ("nodes", Json.arr <| nodes.map (fun n => Json.mkObj
        [ ("id", Json.num n.id)
        , ("kind", Json.str n.kind)
        , ("depth", Json.num n.depth)
        , ("label", Json.str n.label)
        ]))
    , ("edges", Json.arr <| edges.map (fun e => Json.mkObj
        [ ("src", Json.num e.src)
        , ("dst", Json.num e.dst)
        , ("label", Json.str e.label)
        ]))
    , ("root", Json.num root)
    ]

def parseArg (args : List String) (flag : String) : Option String :=
  match args with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

def parseArgsMany (args : List String) (flag : String) : List String :=
  match args with
  | [] => []
  | x :: y :: rest =>
      if x = flag then
        y :: parseArgsMany rest flag
      else
        parseArgsMany (y :: rest) flag
  | _ => []

def nameOfDotted (s : String) : Name :=
  s.splitOn "." |>.foldl (fun n part => Name.str n part) Name.anonymous

def importProject (extraModules : List String) : IO Environment := do
  let sys ← Lean.findSysroot
  -- Initialize to sysroot + paths provided by Lake (via LEAN_PATH in `lake exe`).
  Lean.initSearchPath sys
  let extras : Array Import := extraModules.toArray.map (fun s => { module := nameOfDotted s })
  try
    importModules (#[{module := `Init}, {module := `HeytingLean}] ++ extras) {}
  catch _ =>
    -- Fallback: keep a minimal environment if the project library is unavailable.
    importModules #[{module := `Init}] {}

def findConst (env : Environment) (full : String) : Option Name :=
  env.constants.toList.findSome? (fun (n, _ci) => if n.toString = full then some n else none)

/-- Dump a structural graph of the type of a constant as JSON. -/
def main (argv : List String) : IO Unit := do
  let some full := parseArg argv "--const"
    | IO.println (toString <| Json.mkObj [("nodes", Json.arr #[]), ("edges", Json.arr #[]), ("root", Json.num 0)]); return
  let extraMods := parseArgsMany argv "--module"
  let fuel :=
    match parseArg argv "--fuel" with
    | some s => s.toNat?.getD 512
    | none => 512
  let env ← importProject extraMods
  let some n := findConst env full
    | IO.println (toString <| Json.mkObj [("nodes", Json.arr #[]), ("edges", Json.arr #[]), ("root", Json.num 0)]); return
  let some ci := env.constants.find? n
    | IO.println (toString <| Json.mkObj [("nodes", Json.arr #[]), ("edges", Json.arr #[]), ("root", Json.num 0)]); return
  let e := ci.type
  let (_, st) := (walk e 0 fuel).run {}
  let root := match st.nodes[0]? with
    | some n => n.id
    | none   => 0
  let j := jsonOf st.nodes st.edges root
  IO.println (toString j)
