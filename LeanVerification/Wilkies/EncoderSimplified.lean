namespace Wilkies

abbrev Lit := Int
abbrev Clause := List Lit
abbrev CNF := List Clause

def values (n : Nat) : List Nat :=
  (List.range n).map (fun i => i + 1)

def rangeFromTo (lo hi : Nat) : List Nat :=
  (List.range (hi + 1 - lo)).map (fun d => lo + d)

def flatMap {α β : Type} : List α → (α → List β) → List β
  | [], _ => []
  | x :: xs, f => f x ++ flatMap xs f

def enumerateFrom {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | i, x :: xs => (i, x) :: enumerateFrom (i + 1) xs

def enumerate {α : Type} (xs : List α) : List (Nat × α) :=
  enumerateFrom 0 xs

def symPairs (n : Nat) : List (Nat × Nat) :=
  flatMap (values n) (fun i => (rangeFromTo i n).map (fun j => (i, j)))

def product2 (xs ys : List Nat) : List (Nat × Nat) :=
  flatMap xs (fun x => ys.map (fun y => (x, y)))

def product3 (xs ys zs : List Nat) : List (Nat × Nat × Nat) :=
  flatMap xs (fun x => flatMap ys (fun y => zs.map (fun z => (x, y, z))))

def product4 (xs ys zs ws : List Nat) : List (Nat × Nat × Nat × Nat) :=
  flatMap xs (fun x =>
    flatMap ys (fun y =>
      flatMap zs (fun z =>
        ws.map (fun w => (x, y, z, w)))))

def indexOf {α : Type} [DecidableEq α] (needle : α) : List α → Nat
  | [] => 0
  | x :: xs => if needle = x then 0 else indexOf needle xs + 1

def swapNat (a b x : Nat) : Nat :=
  if x = a then b else if x = b then a else x

def pairCount (n : Nat) : Nat :=
  (symPairs n).length

def symIndex (n i j : Nat) : Nat :=
  indexOf (min i j, max i j) (symPairs n)

def pos (v : Nat) : Lit :=
  Int.ofNat v

def neg (v : Nat) : Lit :=
  -Int.ofNat v

def addVar (n i j k : Nat) : Nat :=
  symIndex n i j * n + (k - 1) + 1

def mulVar (n i j k : Nat) : Nat :=
  pairCount n * n + symIndex n i j * n + (k - 1) + 1

def expVar (n i j k : Nat) : Nat :=
  2 * pairCount n * n + (i - 1) * n * n + (j - 1) * n + (k - 1) + 1

def primaryCount (n : Nat) : Nat :=
  2 * pairCount n * n + n * n * n

def symAuxBlockSize (n : Nat) : Nat :=
  pairCount n * n * n

def add2Base (n : Nat) : Nat := primaryCount n
def mul2Base (n : Nat) : Nat := add2Base n + symAuxBlockSize n
def distBase (n : Nat) : Nat := mul2Base n + symAuxBlockSize n
def expAddBase (n : Nat) : Nat := distBase n + symAuxBlockSize n
def expMulBase (n : Nat) : Nat := expAddBase n + symAuxBlockSize n
def exp2Base (n : Nat) : Nat := expMulBase n + symAuxBlockSize n
def wilkieTermBase (n : Nat) : Nat := exp2Base n + n * n * n * n

def add2Var (n i j k l : Nat) : Nat :=
  add2Base n + (symIndex n i k * n + (j - 1)) * n + (l - 1) + 1

def mul2Var (n i j k l : Nat) : Nat :=
  mul2Base n + (symIndex n i k * n + (j - 1)) * n + (l - 1) + 1

def distVar (n x y z l : Nat) : Nat :=
  distBase n + ((x - 1) * pairCount n + symIndex n y z) * n + (l - 1) + 1

def expAddVar (n x y z l : Nat) : Nat :=
  expAddBase n + ((x - 1) * pairCount n + symIndex n y z) * n + (l - 1) + 1

def expMulVar (n x y z l : Nat) : Nat :=
  expMulBase n + (symIndex n x y * n + (z - 1)) * n + (l - 1) + 1

def exp2Var (n x y z l : Nat) : Nat :=
  exp2Base n + ((x - 1) * n * n * n + (y - 1) * n * n + (z - 1) * n + (l - 1)) + 1

def termVar (n termIndex value : Nat) : Nat :=
  wilkieTermBase n + termIndex * n + (value - 1) + 1

def atMostOnePairwise : List Nat → CNF
  | [] => []
  | x :: xs => xs.map (fun y => [neg x, neg y]) ++ atMostOnePairwise xs

def exactlyOnePairwise (xs : List Nat) : CNF :=
  atMostOnePairwise xs ++ [xs.map pos]

inductive Op where
  | add
  | mul
  | exp
deriving DecidableEq, Repr

inductive Arg where
  | const (value : Nat)
  | term (termIndex : Nat)
deriving DecidableEq, Repr

structure TermSpec where
  op : Op
  left : Arg
  right : Arg
deriving DecidableEq, Repr

def opVar (n : Nat) : Op → Nat → Nat → Nat → Nat
  | .add, i, j, k => addVar n i j k
  | .mul, i, j, k => mulVar n i j k
  | .exp, i, j, k => expVar n i j k

def termSpecs : List TermSpec := [
  ⟨.add, .const 1, .const 4⟩,
  ⟨.exp, .term 0, .const 5⟩,
  ⟨.exp, .term 0, .const 4⟩,
  ⟨.mul, .const 4, .const 4⟩,
  ⟨.add, .term 0, .term 3⟩,
  ⟨.exp, .term 4, .const 4⟩,
  ⟨.exp, .term 4, .const 5⟩,
  ⟨.mul, .term 3, .const 4⟩,
  ⟨.add, .const 1, .term 7⟩,
  ⟨.exp, .term 8, .const 4⟩,
  ⟨.exp, .term 8, .const 5⟩,
  ⟨.mul, .term 7, .const 4⟩,
  ⟨.add, .const 1, .term 3⟩,
  ⟨.add, .term 12, .term 11⟩,
  ⟨.exp, .term 13, .const 4⟩,
  ⟨.exp, .term 13, .const 5⟩,
  ⟨.add, .term 1, .term 6⟩,
  ⟨.add, .term 2, .term 5⟩,
  ⟨.exp, .term 17, .const 5⟩,
  ⟨.exp, .term 16, .const 4⟩,
  ⟨.add, .term 9, .term 14⟩,
  ⟨.add, .term 10, .term 15⟩,
  ⟨.exp, .term 20, .const 5⟩,
  ⟨.exp, .term 21, .const 4⟩,
  ⟨.mul, .term 19, .term 22⟩,
  ⟨.mul, .term 18, .term 23⟩
]

def wilkieTermCount : Nat :=
  termSpecs.length

def termClauses (n termIndex : Nat) (spec : TermSpec) : CNF :=
  let vals := values n
  exactlyOnePairwise (vals.map (termVar n termIndex)) ++
  match spec.left, spec.right with
  | .const left, .const right =>
      vals.map (fun v => [neg (opVar n spec.op left right v), pos (termVar n termIndex v)])
  | .const left, .term right =>
      (product2 vals vals).map (fun (u, v) =>
        [neg (opVar n spec.op left u v), neg (termVar n right u), pos (termVar n termIndex v)])
  | .term left, .const right =>
      (product2 vals vals).map (fun (u, v) =>
        [neg (opVar n spec.op u right v), neg (termVar n left u), pos (termVar n termIndex v)])
  | .term left, .term right =>
      (product3 vals vals vals).map (fun (u, v, w) =>
        [neg (opVar n spec.op u v w), neg (termVar n left u), neg (termVar n right v),
          pos (termVar n termIndex w)])

def totalityClauses (n : Nat) : CNF :=
  let vals := values n
  let syms := symPairs n
  flatMap syms (fun (i, j) => exactlyOnePairwise (vals.map (fun k => addVar n i j k))) ++
  flatMap syms (fun (i, j) => exactlyOnePairwise (vals.map (fun k => mulVar n i j k))) ++
  flatMap (product2 vals vals) (fun (i, j) => exactlyOnePairwise (vals.map (fun k => expVar n i j k)))

def unitIdentityClauses (n : Nat) : CNF :=
  (values n).map (fun x => [pos (mulVar n x 1 x)]) ++
  (values n).map (fun x => [pos (expVar n 1 x 1)]) ++
  (values n).map (fun x => [pos (expVar n x 1 x)])

def addAssocClauses (n : Nat) : CNF :=
  let vals := values n
  flatMap (symPairs n) (fun (i, k) =>
    flatMap vals (fun j =>
      atMostOnePairwise (vals.map (fun l => add2Var n i j k l)) ++
      flatMap (product2 vals vals) (fun (l, m) => [
        [neg (addVar n j k m), neg (addVar n i m l), pos (add2Var n i j k l)],
        [neg (addVar n i j m), neg (addVar n m k l), pos (add2Var n i j k l)]
      ])))

def mulAssocClauses (n : Nat) : CNF :=
  let vals := values n
  flatMap (symPairs n) (fun (i, k) =>
    flatMap vals (fun j =>
      atMostOnePairwise (vals.map (fun l => mul2Var n i j k l)) ++
      flatMap (product2 vals vals) (fun (l, m) => [
        [neg (mulVar n j k m), neg (mulVar n i m l), pos (mul2Var n i j k l)],
        [neg (mulVar n i j m), neg (mulVar n m k l), pos (mul2Var n i j k l)]
      ])))

def distClauses (n : Nat) : CNF :=
  let vals := values n
  flatMap (values n) (fun x =>
    flatMap (symPairs n) (fun (y, z) =>
      atMostOnePairwise (vals.map (fun l => distVar n x y z l)) ++
      (product2 vals vals).map (fun (l, m) =>
        [neg (addVar n y z m), neg (mulVar n x m l), pos (distVar n x y z l)]) ++
      (product3 vals vals vals).map (fun (l, m1, m2) =>
        [neg (mulVar n x y m1), neg (mulVar n x z m2), neg (addVar n m1 m2 l),
          pos (distVar n x y z l)])))

def expAddClauses (n : Nat) : CNF :=
  let vals := values n
  flatMap (values n) (fun x =>
    flatMap (symPairs n) (fun (y, z) =>
      atMostOnePairwise (vals.map (fun l => expAddVar n x y z l)) ++
      (product2 vals vals).map (fun (l, m) =>
        [neg (addVar n y z m), neg (expVar n x m l), pos (expAddVar n x y z l)]) ++
      (product3 vals vals vals).map (fun (l, m1, m2) =>
        [neg (expVar n x y m1), neg (expVar n x z m2), neg (mulVar n m1 m2 l),
          pos (expAddVar n x y z l)])))

def expMulClauses (n : Nat) : CNF :=
  let vals := values n
  flatMap (symPairs n) (fun (x, y) =>
    flatMap vals (fun z =>
      atMostOnePairwise (vals.map (fun l => expMulVar n x y z l)) ++
      (product2 vals vals).map (fun (l, m) =>
        [neg (mulVar n x y m), neg (expVar n m z l), pos (expMulVar n x y z l)]) ++
      (product3 vals vals vals).map (fun (l, m1, m2) =>
        [neg (expVar n x z m1), neg (expVar n y z m2), neg (mulVar n m1 m2 l),
          pos (expMulVar n x y z l)])))

def expAssocClauses (n : Nat) : CNF :=
  let vals := values n
  flatMap (product3 vals vals vals) (fun (x, y, z) =>
    atMostOnePairwise (vals.map (fun l => exp2Var n x y z l)) ++
    flatMap (product2 vals vals) (fun (l, m) => [
      [neg (expVar n x y m), neg (expVar n m z l), pos (exp2Var n x y z l)],
      [neg (mulVar n y z m), neg (expVar n x m l), pos (exp2Var n x y z l)]
    ]))

def wilkieDiseqClauses (n : Nat) : CNF :=
  (values n).map (fun v => [neg (termVar n 24 v), neg (termVar n 25 v)])

def wilkieClauses (n : Nat) : CNF :=
  flatMap (enumerate termSpecs) (fun (termIndex, spec) => termClauses n termIndex spec) ++
  wilkieDiseqClauses n

def lexStepClauses (aux a b next : Nat) : CNF :=
  [
    [neg aux, neg a, pos b],
    [neg aux, neg a, pos next],
    [neg aux, pos b, pos next]
  ]

def lexCompareClausesFrom : Nat → List (Nat × Nat) → CNF
  | _, [] => []
  | aux, (a, b) :: rest =>
      if a = b then
        lexCompareClausesFrom aux rest
      else
        let next := aux + 1
        lexStepClauses aux a b next ++ lexCompareClausesFrom next rest

def lexSmallerEqClausesFrom (aux : Nat) (pairs : List (Nat × Nat)) : CNF :=
  [[pos aux]] ++ lexCompareClausesFrom aux pairs

def lexCompareAuxCount : List (Nat × Nat) → Nat
  | [] => 0
  | (a, b) :: rest =>
      if a = b then lexCompareAuxCount rest else lexCompareAuxCount rest + 1

def lexSmallerEqAuxCount (pairs : List (Nat × Nat)) : Nat :=
  lexCompareAuxCount pairs + 1

def strictPairs (n : Nat) : List (Nat × Nat) :=
  flatMap (values n) (fun i => (rangeFromTo (i + 1) n).map (fun j => (i, j)))

def lexPairsForOp (n : Nat) : Op → List (Nat × Nat)
  | .add => strictPairs n
  | .mul => strictPairs n
  | .exp => product2 (values n) (values n)

/--
The operation-table Boolean sequence used by `simp_enc.py` for lex leaders:
strict unordered input pairs for `+` and `*`, ordered input pairs for
exponentiation, and all possible output values.
-/
def lexTableEntries (n : Nat) : List (Op × Nat × Nat × Nat) :=
  flatMap [.add, .mul, .exp] (fun op =>
    flatMap (lexPairsForOp n op) (fun (x, y) =>
      (values n).map (fun value => (op, x, y, value))))

def lexEntryVar (n : Nat) : Op × Nat × Nat × Nat → Nat
  | (op, x, y, value) => opVar n op x y value

def lexTranspositionImageVar (n left right : Nat) :
    Op × Nat × Nat × Nat → Nat
  | (op, x, y, value) =>
      opVar n op (swapNat left right x) (swapNat left right y)
        (swapNat left right value)

def lexTranspositionVarPairs (n left right : Nat) : List (Nat × Nat) :=
  (lexTableEntries n).map (fun entry =>
    (lexEntryVar n entry, lexTranspositionImageVar n left right entry))

def lexTranspositionClausesFrom
    (n left right aux : Nat) : CNF :=
  lexSmallerEqClausesFrom aux (lexTranspositionVarPairs n left right)

def simpEncLexTranspositionPairs (n : Nat) : List (Nat × Nat) :=
  flatMap (rangeFromTo 6 n) (fun left =>
    (rangeFromTo (left + 1) n).map (fun right => (left, right)))

def lexTranspositionAuxCount (n left right : Nat) : Nat :=
  lexSmallerEqAuxCount (lexTranspositionVarPairs n left right)

def simpEncLexClausesFromAux (n : Nat) : Nat → List (Nat × Nat) → CNF
  | _, [] => []
  | aux, (left, right) :: rest =>
      lexTranspositionClausesFrom n left right aux ++
        simpEncLexClausesFromAux n
          (aux + lexTranspositionAuxCount n left right) rest

def simpEncLexClauses (n auxStart : Nat) : CNF :=
  simpEncLexClausesFromAux n auxStart (simpEncLexTranspositionPairs n)

def simpEncLexAuxStart (n : Nat) : Nat :=
  wilkieTermBase n + wilkieTermCount * n + 1

/--
Extra search clauses from Zhang Section 3, after normalizing the first three
integers to 1,2,3 and the failing pair to a=4, b=5.  These include the used
Burris-Lee M exclusions, the Jackson linear-core fragment, and Lee L2-L5 for
P,Q,R,S.  See `ZhangPaperConsequences` and `ZHANG_EXTRAS.md`.
-/
def simpEncExtraClauses (n : Nat) : CNF :=
  let vals := values n
  let x := 4
  let y := 5
  [
    [pos (addVar n 1 1 2)],
    [pos (addVar n 2 1 3)],
    [neg (addVar n 1 x 1)],
    [neg (addVar n 2 x 1)],
    [neg (addVar n x x 1)],
    [neg (mulVar n x x 1)],
    [neg (addVar n x x x)],
    [neg (mulVar n x x x)],
    [neg (addVar n 1 x x)],
    [neg (addVar n 2 x x)],
    [neg (termVar n 12 1)],
    [neg (termVar n 7 1)],
    [neg (termVar n 12 x)]
  ] ++
  flatMap vals (fun value => [
    [neg (addVar n 2 x value), neg (termVar n 0 value)],
    [neg (mulVar n x x value), neg (termVar n 0 value)],
    [neg (termVar n 7 value), neg (termVar n 0 value)],
    [neg (mulVar n x x value), neg (addVar n 2 x value)],
    [neg (mulVar n x x value), neg (addVar n x x value)],
    [neg (termVar n 12 value), neg (mulVar n x x value)]
  ]) ++
  vals.map (fun v => [neg (mulVar n x v y)]) ++
  flatMap [1, 2, 3] (fun j =>
    flatMap vals (fun z =>
      [1, 2, 3].map (fun i =>
        [neg (addVar n i z y), neg (mulVar n j x z)]))) ++
  flatMap (product3 [1, 2, 3] [1, 2, 3] [1, 2, 3]) (fun (i, j, k) =>
    (product4 vals vals vals vals).map
      (fun (x2Value, jxValue, kx2Value, tailValue) => [
        neg (termVar n 3 x2Value),
        neg (mulVar n j x jxValue),
        neg (mulVar n k x2Value kx2Value),
        neg (addVar n jxValue kx2Value tailValue),
        neg (addVar n i tailValue y)
      ])) ++
  flatMap vals (fun v =>
    flatMap (product2 vals vals) (fun (i, l) => [
      [neg (termVar n 0 i), neg (termVar n 4 l), neg (mulVar n i v l)],
      [neg (termVar n 4 i), neg (termVar n 0 l), neg (mulVar n i v l)],
      [neg (termVar n 8 i), neg (termVar n 13 l), neg (mulVar n i v l)],
      [neg (termVar n 13 i), neg (termVar n 8 l), neg (mulVar n i v l)]
    ]))

def hsiClauses (n : Nat) : CNF :=
  totalityClauses n ++
  unitIdentityClauses n ++
  addAssocClauses n ++
  mulAssocClauses n ++
  distClauses n ++
  expAddClauses n ++
  expMulClauses n ++
  expAssocClauses n

def coreClauses (n : Nat) : CNF :=
  hsiClauses n ++ wilkieClauses n

def encode (n : Nat) : CNF :=
  coreClauses n ++ simpEncLexClauses n (simpEncLexAuxStart n) ++ simpEncExtraClauses n

def litVar (l : Lit) : Nat :=
  if l < 0 then Int.toNat (-l) else Int.toNat l

def maxVarClause (clause : Clause) : Nat :=
  clause.foldl (fun acc lit => max acc (litVar lit)) 0

def maxVarCNF (cnf : CNF) : Nat :=
  cnf.foldl (fun acc clause => max acc (maxVarClause clause)) 0

def joinSep (sep : String) : List String → String
  | [] => ""
  | x :: xs => xs.foldl (fun acc s => acc ++ sep ++ s) x

def concatStrings (xs : List String) : String :=
  xs.foldl (fun acc s => acc ++ s) ""

def clauseToDimacs (clause : Clause) : String :=
  joinSep " " (clause.map toString) ++ " 0\n"

def cnfToDimacs (cnf : CNF) : String :=
  s!"p cnf {maxVarCNF cnf} {cnf.length}\n" ++ concatStrings (cnf.map clauseToDimacs)

end Wilkies
