import Wilkies.EncoderSimplified

open Wilkies

def usage : String :=
  "usage: wilkies_cnf [n >= 5] [output-file]\n"

def validateN (n : Nat) : Except String Nat :=
  if n < 5 then
    .error "error: n must be at least 5\n"
  else
    .ok n

def parseArgs : List String → Except String (Nat × Option String)
  | [] => .ok (8, none)
  | [n] =>
      match n.toNat? with
      | some value => validateN value |>.map (fun value => (value, none))
      | none => .error usage
  | [n, output] =>
      match n.toNat? with
      | some value => validateN value |>.map (fun value => (value, some output))
      | none => .error usage
  | _ => .error usage

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error message =>
      IO.eprint message
      return 2
  | .ok (n, output?) =>
      let text := cnfToDimacs (encode n)
      match output? with
      | none => IO.print text
      | some output => IO.FS.writeFile output text
      return 0
