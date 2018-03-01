> {-# OPTIONS_GHC -Wall -fno-warn-unused-imports -fno-warn-name-shadowing #-}
> {-# LANGUAGE TemplateHaskell,FlexibleContexts, FlexibleInstances #-}

Here we present a tableau-based decision procedure for Linear Temporal
Logic over finite traces (LTLf).

> module Tableau where

We hide standard library functions with interfering names.

> import Prelude hiding (negate, or, and, until)

> import Data.List hiding (or, and)
> import Data.List.Split (endBy)
> 
> import Data.Maybe (mapMaybe, isNothing, isJust, fromMaybe)
> 
> import Data.Map (Map)
> import qualified Data.Map as Map
>
> import Data.Set (Set)
> import qualified Data.Set as Set

For the full syntax, see `Syntax.hs`. Terms are, in general, of type
`LTL a`. The parameter `a` of the type `LTL` represents primitive
propositions.

Our decision procedure is for LTLf, but we call the type LTL because
the syntax of the two logics are identical.

> import Syntax

The concrete syntax we use is minimal: as plain propositions, we have
variables, false, and implication (encoding other propositions is not
hard: see `Syntax.hs`); as temporal propositions, we have the *next
modality*, which we write `X :: LTL a -> LTL a`, and the *weak until
modality*, which we write `W :: LTL a -> LTL a -> LTL a`.

Formulae in the logic are evaluated over *traces*, which are finite
sequences of *valuation functions* mapping variables to truth
values. Formulae are evaluated in a given index of the trace, from the
`i`th valuation onwards.

Lifting valuations to each valuation is straightforward. To check `X
phi` in the `i`th state, we check `phi` in the `i+1`th state. To check
`phi W psi` in the `i`th state, we need some (possibly empty) trace of
states where `phi` holds followed by one where `psi` holds. Other
temporal encodings---always, ever, strong until---follow (see
`Syntax.hs`).

Our goal in defining a decision procedure is to take an arbitrary LTLf
formula `f` and determine whether there exists a trace `t` such that
`f` holds in `t` at position 0. If there is such a trace, then `f` is
"satsifiable"; otherwise, `f` is unsatisfiable. To decide whether `f`
is satisfiable, we construct a *tableau* structure (type
`Tableau`). Our construction procedure unrolls implications and
temporal formulae, searching for a contradiction---if we can't find
one, we can conclude that the formula is satisfiable.

The tableau is a graph of *positive-negative pairs*, a pair of sets of
formulae: a set of positive formulae `pos` and a set of negative
formulae `neg`.

As described above, the nodes of the Tableau structures called
PNPs. Intuitively, the `pos` set is the set of LTLf formulae that are
true, and the `neg` set is the set of formulae that are false.

The labels represent the different roles that PNPs will play in our
tableau. `Norm` PNPs represent the proof-theoretic exploration of the
current time step; `Temp` PNPs represent the first PNP to explore a
new time step; finally `Term` PNPs represent the exploration of the
end of time. When we create tableau nodes we make it so that once a
node is a `Term` node, it can never not be terminal, however since
`Temp` nodes represent a boundary, they must be a boundary. Then, the
default for stepping a `Norm` PNP is to step it to another `Norm` PNP;
if we want different behvaior (and we will) we will have to do it
manually.

> data PNPType
>   = Norm | Temp | Term
>     deriving (Show, Eq, Ord)
>
> stepType :: PNPType -> PNPType
> stepType Term = Term
> stepType _ = Norm

Now we can define PNPs and their `Show` instance

> data PNP a
>   = PNP {typ :: PNPType, pos :: Set (LTL a), neg :: Set (LTL a) }
>   deriving (Eq, Ord)
>
> instance (Eq a, Show a) => Show (PNP a) where
>   show (PNP Temp p n) = "<|" ++ show (PNP Norm p n) ++ "|>"
>   show (PNP Term p n) = show (PNP Norm p n) ++ "EOT"
>   show (PNP Norm p n) =
>     -- "\\left(" ++ showSet p ++ ", " ++ showSet n ++ "\\right)"                       
>     "( " ++ showSet p ++ ", " ++ showSet n ++ ")"
>
> showSet :: Show a => Set a -> String
> showSet s  | Set.null s = "" -- "\\emptyset"
>            | otherwise = "\\{" ++ (intercalate "," (map show $ Set.toAscList s)) ++ "\\}"
>

We want to define a kind of semantics for these PNPs, so we say that a
PNP is closed if `F` is a member of the positive set, or its positive
and negative sets have a non-empty intersection. If we think of the
positive set as "things that are true" and the negative set as "things
that are false" then we certainly dont want `F` to be true, nor do we
want a formula to be both true and false. This gives us the intuition
that closed PNPs represent impossible and unsatisfiable states. When
we construct the Tableau we will say that the root node is
unsatisfiable if every path from it contains a closed node.

> closed :: Ord a => PNP a -> Bool
> closed p = (F `Set.member` pos p)
>   || not (Set.null (pos p `Set.intersection` neg p))


Now we define the tableau using the adjacency list representation of a
digraph. The edges are unlabeled and the nodes are PNPs.

> newtype Tableau a = Tableau (Map (PNP a) [PNP a])

> instance (Eq a, Show a) => Show (Tableau a) where
>   show (Tableau t) =
>     intercalate "\n" $ map showEdges (Map.toList t)
>     where
>       showEdges (p,succs) =
>         "STATE : " ++ show p ++ "\n  "
>            ++ intercalate "\n  " (map show succs)

We define a few helper functions for the tableau, the `emptyTableau`
term appropriately wraps the Map.empty term. The unseen function takes
a Tableau t and a PNP n and returns true if n is not one of the nodes
of the tableau. Here we tacitly assume that all of the nodes are
represented as a key to the adjacency list. The `addEdges` function
takes a PNP `p` and a list of PNPs `succs` and inserts edges between
each p and each of the successors in `succs`. This is simply a
concatenation with the adjacency list. The `successors` function just
looks up the successors of `p`, returning an empty list if `p` cannot
be found in the tableau. The `tunion` function simply takes the union
of two tableaux.

> emptyTableau :: Tableau a
> emptyTableau = Tableau Map.empty
>
> unseen :: Ord a => Tableau a -> PNP a -> Bool
> unseen (Tableau t) n = Map.notMember n t
>
> addEdges :: Ord a => PNP a -> [PNP a] -> Tableau a -> Tableau a
> addEdges p succs (Tableau t) = Tableau (Map.insert p succs t)
>
> successors :: Ord a => PNP a -> Tableau a -> [PNP a]
> successors p (Tableau t) = Map.findWithDefault [] p t
>
> tunion :: Ord a => Tableau a -> Tableau a -> Tableau a
> tunion (Tableau t) (Tableau t') = Tableau $ t `Map.union` t'


Now that we've defined the Tableau data structure and some helper
functions, we can start constructing it. The tableau is constructed in
three main parts: a `buildRoot` function which creates a PNP from an
arbitrary LTLf formula, a `makeSucc` function which computes a list of
the PNP successors of a PNP, and a `buildTableau` function which
computes the least fixpoint of `makeSucc` when given the result of
`buildRoot`. There are a lot more auxiliary and helper functions that
we'll get to along the way, but lets start with `buildRoot`. Once
we've built the tableau we need to find a finite path in it that
represents a finite-length trace that satisfies the input formula.

The basic idea of `buildRoot` is that it injects a formula `f` into
the positive set of an empty PNP. In an LTL decision procedure that's
all we would need to do, but in an LTLf decision procedure we need to
take another simple step, which is to "inject finiteness". In other
words, we insert one of the axioms of LTLf, FINITE, into the positive
set. The FINITE axiom says `ever end` which means that eventually time
will end. By including this axiom in our root node, we are
automatically going to be checking whether or not it is the last state
in time, before we can take a step. We could have easily built this
into our decision procedure itself from scratch, but this version
doesn't require much modification to the Tableau decision procedure
for LTL.

> buildRoot :: Ord a => LTL a -> PNP a
> buildRoot f = PNP Norm (Set.fromList [f, ever end]) Set.empty

The functions `ever` and `end` are new, but can be defined in terms of
`W`, `F` and `->`. For the full definition, see `./Syntax.hs`.

Now we can move onto defining the `makeSucc` function, which takes a
PNP and return a list of successor PNPs. Since we are searching for a
contradiction, we want to define the `makeSucc` function such that for
a PNP `P`, if every successor in `makeSucc P` is unsatisfiable, tnhen
`P` is also unsatisfiable. Since closed PNPs are unsatisfiable, we
will eventually need to find a path that ends in a `Term` PNP with no
closed nodes on it. For now, we are just concerned with how to define
the `makeSucc` function.

For each syntactic term in the positive and negative sets we define a
rule that explores some aspect of the current time moves time
forwards. Since we want to explore ever aspect of the current time
step before moving to the next one, we prioritize non-temporal
formulae before taking a step in the `X` modality. Below are the rules
we use to explore the current modality (note that these rules will
conflict so in our implementation we apply them in order, so that rule
`i` is checked before rule `i+1`).

Before we can define the rules, we must define a quick helper function
that lets us pattern match on the contents of a set. The `satisfying`
function finds a member `x` of a set satisfying a given predicate and
returns a pair of `x` and the set without `x`.

> satisfying :: Ord a => (a -> Bool) -> Set a -> Maybe (a, Set a)
> satisfying pred s = do
>   let (sat, unsat) = Set.partition pred s
>   (v,sat') <- Set.maxView sat
>   return (v, sat' `Set.union` unsat)

Now we can define the rules on the outputs of this formula

1. For a PNP `Q`, if `Q` is closed, take no step.

If we have found a contradictory PNP, there is chance of finding a
path that contains this node with no closed node in it, so we don't
waste our time by exploring more successors of `Q`. It's not like it
can get any more contradictory!

2. For a PNP `Q` with `a -> b` in `pos Q`, define two successors `Ql`
and `Qr`:

  + Let `pos Ql = (pos Q \ {a -> b}) union {b}` and `neg Ql = neg Q`

  + Let `pos Qr = (pos Q \ {a -> b})` and `neg Qr = neg Q union {a}`

In classical logic, `a -> b == ~a \/ b`, which means have a choice
between `~a` holding and `b` holding, so, we create a successor for
each of those possible worlds implied by `a -> b`.

In this function we assume that `Imp a b` is not a member of `posq'`

> posImp :: Ord a => PNPType -> LTL a -> LTL a -> Set (LTL a) -> Set (LTL a) -> [PNP a]
> posImp t a b posq' negq = let t' = stepType t in
>   [
>     PNP t' (Set.insert b $ posq') negq ,
>     PNP t' posq' (Set.insert a $ negq)
>   ]

3. For a PNP `Q` with `a -> b` in `neg Q`, define one successors `Q'`,
such that `pos Q' = pos Q union {a}` and `neg Q = (neg Q \ {a -> b})
union {b}`.

Again, we can use the classical logic tautology `~ a -> b == a /\ ~b`,
and so we put a in the positve set and `b` in the negative set. We
could have just as easily made `pos Q = {a,~b}`, but then we would
eventually have to put `b` in the negative set, and that is extra,
unnecessary work that we can do here in one step.

In the `negImp` function we assume that `Imp a b` is not in `negq'`.

> negImp :: Ord a => PNPType -> LTL a -> LTL a -> Set (LTL a) -> Set (LTL a) -> [PNP a]
> negImp t a b posq negq' =
>   [ PNP (stepType t) (Set.insert a posq) (Set.insert b negq') ]


Notice that these first three rules take care of the entirety of
classical logic; every conjunction, disjunction, negation, and
implication that we would want to express is a combination of
variables, implication and `F`. For more information about these
incodings, see `./Syntax.hs`

Now we want to move onto temporal operators. The obvious step would be
to consider the `X` modality; however, that operator forces us to take
a step in time, were as the weak-until operator has properties that
can be expressed in the current time step, so before we can say that
we have evaluated the current time step fully, we must check whether
all occurences of weak-until have been discharged.

4. For a PNP `Q` with `a W b` in `pos Q`, we define two successors
`Ql` and `Qr`:

  + Let `pos Ql = (pos Q \ {a W b}) union {b}` and `neg Ql = neg Q`.

  + Let `pos Qr = (pos Q \ {a W b}) union {a}` and `neg Ql = neg Q union {X~ a W b}`.

As mentioned above, these rules come from the WeakUntilUnroll axiom,
which says that `a W b == b \/ a /\ ~X~ a W b`. If we wanted to, we
could have defined a single successor which replaced `a W b` with `b
\/ a /\ ~X~ a W b`, but this way we can skip the steps for conjunction
and disjunction (which are really encoded as a bunch of implications),
because the not-closed successors we would get from following this
procedure on `b \/ a/\ ~X~ a W b` are exactly the `Ql` and `Qr` above.

> posW :: Ord a => PNPType -> LTL a -> LTL a -> Set (LTL a) -> Set (LTL a) -> [PNP a]
> posW t a b posq' negq = let t' = stepType t in
>   [
>     PNP t' (Set.insert b posq') negq,
>     PNP t' (Set.insert a $ Set.insert (wkX (a `W` b)) $ posq') negq
>   ]


5. For a PNP `Q` with `a W b` in `neg Q`, we define two successors,
`Ql` and `Qr`:

  + Let `pos Ql = pos Q`, and let `neg Ql = (neg Q \ {a W b}) union {a,b}`

  + Let `pos Qr = pos Q union {X~(a W b)}`, and `neg Qr = (neg Q \ {a W b}) union {b}`

This comes from a simple consequence of the WeakUntilUnroll axiom,
namely that `~ (a W b) == (~b /\ ~a) \/ ~b /\ X~(a W b)`, so we
appropriately take each branch. Similar to the previous steps, we use
all of the information we have to avoid duplicating work by stepping
through all of the conjunctions, disjunctions and negations.

> negW :: Ord a => PNPType -> LTL a -> LTL a -> Set (LTL a) -> Set (LTL a) -> [PNP a]
> negW t a b posq negq' = let t' = stepType t in
>   [
>     PNP t' posq (Set.insert a $ Set.insert b negq'),
>     PNP t' (Set.insert (X $ negate $ W a b) posq) (Set.insert b negq')
>   ]

Now that we can explore each individual state in time, we can step
forward in time. There are two cases to consider here, either we are
at then end of time, and `X top` is in the positive set, or we are not
at the end of time, and we can take a step forwards.

If we decide that we can take a step forwards, we will apply the
`step` function to both the positive and negative sets of the
PNP. When applied to a set `S`, this function computes the set `{f | X
f in S}`. It drops all formulae that were expanded in the previous
time step and keeps only those that must be evaluated in the next time
step. Then we can use this on the positive and negative sets to define `stepPNP`

> step :: Ord a => Set (LTL a) -> Set (LTL a)
> step = Set.foldr (\f nextSet ->
>            case f of
>              (X f) -> Set.insert f nextSet
>              _ -> nextSet
>         ) Set.empty
>
> stepPNP :: Ord a => PNP a -> [PNP a]
> stepPNP (PNP _ posq negq) = [PNP Temp (step posq) (step negq)]

On the other hand, if we are at the end of time, we cannot take any
steps, and so we can define a function `dropTemporal` that converts a
formula `f` into another one representing the fact that `end /\ X y =
F` for any formula `y`. This means that we will convert `X y` to `F`,
and `a W b` to `a \/ b` before recursing on both `a` and `b`. We also
define a function `terminalPNP` which lifts `dropTemporal` to PNPs,
and makes sure that `end` information is still maintained by the PNP,
namely `X top` is in the negative set.
    
> dropTemporal :: LTL a -> LTL a
> dropTemporal F = F
> dropTemporal (X _) = F
> dropTemporal (P a) = P a
> dropTemporal (W a b) = dropTemporal a `or` dropTemporal b
> dropTemporal (Imp a b) = Imp (dropTemporal a) (dropTemporal b)
>
> terminalPNP :: Ord a => PNP a -> [PNP a]
> terminalPNP q = [PNP Term (Set.map dropTemporal $ pos q)
>                          (Set.insert (X top) $ Set.map dropTemporal $ neg q)]

Now, we can put all of these pieces together into one `makeSucc` function!

> makeSucc :: Ord a => PNP a -> [PNP a]
> makeSucc q =  
>   if closed q  -- Bot
>   then []
>   else case satisfying isImp (pos q) of -- (->+)
>     -- Just (Imp F _, posq') -> [q {pos = posq'}] -- opt for forms equiv to TOP
>     Just (Imp a b, posq') -> posImp (typ q) a b posq' (neg q)
>     Just _ -> error "Expected Imp in posImp Case"
>     Nothing ->
>       case satisfying isImp (neg q) of -- ( -> -)
>         Just (Imp a b, negq') -> negImp (typ q) a b (pos q) negq'
>         Just _ -> error "Expected Imp in negImp case"
>         Nothing ->
>           case satisfying isW (pos q) of -- (W+)
>             Just (W a b, posq') -> posW (typ q) a b posq' (neg q)
>             Just _ -> error " expected W in posW case"
>             Nothing ->
>               case satisfying isW (neg q) of -- (W-)
>                 Just (W a b, negq') -> negW (typ q) a b (pos q) negq'
>                 Just _ -> error "expected W in negW case"
>                 Nothing ->
>                   if (X top `Set.member` neg q) --  && null posq'
>                   then terminalPNP q                -- (end)
>                   else stepPNP q                    -- (o)

Now we can define the fixpoint that applies the `makeSucc` function
until there are no new PNPs to be added; we call this function
`buildTableau`. We define a wrapper function `tableau` that obscures
the continuation-passing needed for the fix-point.

> buildTableau :: Ord a => (PNP a -> [PNP a]) -> [PNP a] -> Tableau a -> Tableau a
> buildTableau _ [] t = t
> buildTableau succRule (p:worklist)  t =
>   let succs    = succRule p in
>   let t'       = addEdges p succs t in
>   let newNodes = filter (unseen t) succs in
>   buildTableau succRule (worklist ++ newNodes) t'
>
> tableau :: Ord a => LTL a -> Tableau a
> tableau f = buildTableau makeSucc [buildRoot f] emptyTableau


Now that we've built the tableau, we need to determine whether or not
the root node is closed. If the root node is closed is then it is
unsatisfiable, and otherwise it is satisfiable. Unfortunately our
definition of closed-ness only accounts for whether a node is
contradictory in the moment, which many nodes are not. Even in the
example of `a /\ ~a` it took several steps before we got to a closed
node. To lift the definition to trees, we say that a node is closed if
all of its successors are closed, or if its PNP is closed in the
traditional sense. So, to conclude that a node is satsifiable, we only
need to find a path that explores every possibility until the end of
time, i.e. we get to a `Term` node. We call such paths "terminal
paths" and the `terminalPath` function searches its input Tableau for
these paths. 

> terminalPath :: Ord a => Tableau a -> Set (PNP a) -> PNP a -> Maybe [PNP a]
> terminalPath _ _    p | closed p            = Nothing
> terminalPath _ seen p | p `Set.member` seen = Nothing
> terminalPath _ _    p | typ p == Term       = Just [p]
> terminalPath t seen p =
>   let succs = successors p t in
>   let paths = mapMaybe (terminalPath t (Set.insert p seen)) succs in
>   case paths of
>     []       -> Nothing
>     (path:_) -> Just (p:path)

However, everything about "building a tableau" up until
now has been a complete lie, and we dont actually need to build the
structure, we can just use `makeSucc` to run a depth-first search, and
avoid all of the unnecessary effort of creating the whole structure if
we don't need to; `terminalPath'` performs the search in this
manner.

> terminalPath' :: Ord a => Set (PNP a) -> PNP a -> Maybe [PNP a]
> terminalPath' _    p | closed p            = Nothing
> terminalPath' seen p | p `Set.member` seen = Nothing
> terminalPath' _    p | typ p == Term       = Just [p]
> terminalPath' seen p =
>   let succs = makeSucc p in 
>   let paths = mapMaybe (terminalPath' (Set.insert p seen)) succs in
>   case paths of
>     []       -> Nothing
>     (path:_) -> Just (p:path)
> 

We can improve the performance even more by checking for only the
existence of a terminal path without actually calculating it.

> existsTerminalPath :: Ord a => Set (PNP a) -> PNP a -> Bool
> existsTerminalPath _    p | closed p = False
> existsTerminalPath seen p | p `Set.member` seen = False
> existsTerminalPath _    p | typ p == Term = True
> existsTerminalPath seen p =
>   foldr (\q found -> existsTerminalPath (Set.insert p seen) q || found) False (makeSucc p)


Now as defined before we can process the result of the `path` function
as `sat`, `unsat` and `valid` which take LTLf formulae and return
whether or not they are satisfiable, unsatisfiable or valid,
respectively.

> sat, unsat, valid :: Ord a => LTL a -> Bool
> sat f = existsTerminalPath Set.empty (buildRoot f)
> unsat = not . sat
> valid = not . sat . negate

We also define a few useful functions for making interfacing with the
decision procedure easier. `satString` returns `"sat"` if its input
formula is satisfiable, and `"unsat"` otherwise.

> satString :: Ord a => LTL a -> String
> satString f = if sat f then "sat" else "unsat"

The `check` function returns the strongest descriptor possible for an
LTLf formula, i.e. if it is valid, it returns `"valid"`, if it is
satisfiable it returns `"sat"`, and otherwise, it returns `"unsat"`.

> check :: Ord a => LTL a -> String
> check f =
>   if valid f
>   then "valid"
>   else if sat f
>        then "sat" else "unsat"

The `doCheck` function does exactly what the `check` function does,
except it parses the string first.

> doCheck :: String -> String
> doCheck = check . parse'

The `doSatCheck` function does what `satString` does, except it parses
an input string first.

> doSatCheck :: String -> String
> doSatCheck = satString . parse'

We also define a couple of other functions for consistency with our
Proof Graph presentation (see `./ProofGraph.hs`), but they are not
part of the decision procedure.

> sigma_one :: Ord a => PNP a -> Set (LTL a)  
> sigma_one  p = step $ pos p
>
> sigma_four :: Ord a => PNP a -> Set (LTL a)
> sigma_four p = step $ neg p
>
> sigma_two :: Ord a => PNP a -> Set (LTL a)
> sigma_two  p = Set.filter
>                (\f -> case f of
>                       (W _ b) -> b `Set.member` neg p
>                       _      -> False
>                ) (pos p)

> sigma_three :: Ord a => PNP a -> Set (LTL a)               
> sigma_three p = Set.filter
>               (\f -> case f of
>                       (W a _) -> (X top) `Set.member` neg p
>                                  && a `Set.member` pos p
>                       _      -> False
>               ) (pos p)
>
> sigma_five :: Ord a => PNP a -> Set (LTL a)
> sigma_five  p= Set.filter
>              (\f -> case f of
>                      (W a b) -> a `Set.member` pos p
>                                 || b `Set.member` neg p
>                      _      -> False)
>              (neg p)
>
> sigma :: Ord a => PNP a -> PNP a
> sigma p = p {
>   pos = sigma_one p `Set.union` sigma_two p `Set.union` sigma_three p,
>   neg = sigma_four p `Set.union` sigma_five p
>   }
>
> getPrimitives :: PNP a -> PNP a
> getPrimitives p = p { pos = Set.filter isProp (pos p),
>                       neg = Set.filter isProp (neg p)}
  
