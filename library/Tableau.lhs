< {-# OPTIONS_GHC -Wall -fno-warn-unused-imports -fno-warn-name-shadowing #-}
< {-# LANGUAGE TemplateHaskell,FlexibleContexts, FlexibleInstances #-}

Here we present a tableau-based decision procedure for Linear Temporal
Logic over finite traces (LTLf). There are two versions of the
decision procedure: one which explicitly builds a tableau data
structure (`terminalPath`), and another which simply performs
depth-first search (`terminalPath'` and `existsTerminalPath'`).

> module Tableau where

We hide standard library functions with interfering names.

> import Prelude hiding (negate, or, and, until)

> import Data.List hiding (or, and)
> 
> import Data.Maybe (mapMaybe)
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

<h3>Positive-negative pairs</h3>

The tableau is a graph of *positive-negative pairs*, a pair of sets of
formulae: a set of positive formulae `pos` and a set of negative
formulae `neg`. The `PNP` type is parameterized by the type of
propositions.

> data PNP a
>   = PNP {typ :: PNPType, pos :: Set (LTL a), neg :: Set (LTL a) }
>   deriving (Eq, Ord)

Each PNP has one additional piece of information: a *label* of type `PNPType`.

> data PNPType
>   = Norm | Temp | Term
>     deriving (Show, Eq, Ord)
>
> stepType :: PNPType -> PNPType
> stepType Term = Term
> stepType _ = Norm

The labels represent the different roles that PNPs will play in our
tableau. `Norm` PNPs represent the proof-theoretic exploration of the
current time step; `Temp` PNPs represent the first PNP to explore a
new time step; finally `Term` PNPs represent the exploration of the
end of time. When we create tableau nodes we make it so that once a
node is a `Term` node, it can never not be terminal.  Since
`Temp` nodes represent a boundary, they must be a boundary. Then, the
default for stepping a `Norm` PNP is to step it to another `Norm` PNP;
when we want different behavior, we will have to set the PNPType
manually (see `stepTerm`).

We customize the show instance for each type of PNP, which should aid
debugging.

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

PNPs may or may not represent possible states. For example, a PNP with
`F` in the true set represents an impossible world; a PNP with the
same formula in both the positive and negative sets is similarly
impossible. We call such PNPs *closed*.

> closed :: Ord a => PNP a -> Bool
> closed p = (F `Set.member` pos p)
>   || not (Set.null (pos p `Set.intersection` neg p))

<h3>Defining the tableau</h3>

We define the tableau as a directed graph where the states are
PNPs. We use an adjacency list representation, i.e., a finite map from
PNPs to PNPs.

> newtype Tableau a = Tableau (Map (PNP a) [PNP a])

> instance (Eq a, Show a) => Show (Tableau a) where
>   show (Tableau t) = intercalate "\n" $ map showEdges (Map.toList t)
>     where showEdges (p,succs) =
>             "STATE : " ++ show p ++ "\n  "
>                        ++ intercalate "\n  " (map show succs)

We can define the empty tableau:

> emptyTableau :: Tableau a
> emptyTableau = Tableau Map.empty

We can determine whether or not a given PNP has been seen yet, i.e.,
is a state in our Tableau:

> unseen :: Ord a => Tableau a -> PNP a -> Bool
> unseen (Tableau t) n = Map.notMember n t

We can add edges to the tableau, either one at a time or by merging
two tableaux:

> addEdges :: Ord a => PNP a -> [PNP a] -> Tableau a -> Tableau a
> addEdges p succs (Tableau t) = Tableau (Map.insert p succs t)
>
> tunion :: Ord a => Tableau a -> Tableau a -> Tableau a
> tunion (Tableau t) (Tableau t') = Tableau $ t `Map.union` t'

And we can determine the successors of a given PNP in the tableau:

> successors :: Ord a => PNP a -> Tableau a -> [PNP a]
> successors p (Tableau t) = Map.findWithDefault [] p t

Now that we've defined the Tableau data structure and some helper
functions, we can start constructing it; once we've built the tableau
we need to find a finite path in it that represents a finite-length
trace that satisfies the input formula.

The tableau is constructed in three main parts: a `buildRoot` function
which creates a PNP from an arbitrary LTLf formula, a `makeSucc`
function which computes a list of the PNP successors of a PNP, and a
`buildTableau` function which computes the least fixpoint of
`makeSucc` when given the result of `buildRoot`. There are other
auxiliary functions that we'll get to along the way, but lets start
with `buildRoot`.

The `buildRoot` function takes a formula `f` and creates an empty PNP
with `f` in the true set the positive set of an empty PNP. In an
ordinary LTL decision procedure that's all we would need to do, but
we're trying to decide LTL**f**, i.e., we want to restrict our
attention to finite traces. Accordingly, we also "inject finiteness",
inserting `ever end` into the positive set as well. It turns out that
`ever end` is one of the axioms of LTLf, FINITE; it requires that time
eventually ends. By injecting this axiom into our root node, we
guarantee that our tableau algorithm will repeatedly check whether or
not time has ended. We could have built a different decision procedure
from scratch, but injecting finiteness allows us to reuse the LTL
procedure.

> buildRoot :: Ord a => LTL a -> PNP a
> buildRoot f = PNP Norm (Set.fromList [f, ever end]) Set.empty

The `makeSucc` function takes a PNP and returns a list of successor
PNPs. Since we are searching for a contradiction, the `makeSucc`
function is sound, for all PNPs `P`, if every successor in `makeSucc
P` is unsatisfiable, then `P` is also unsatisfiable. Since closed PNPs
are unsatisfiable, finding a contradiction amounts to finding a path
that ends in a `Term` PNP with no closed nodes on it.

To construct the tableau, we use a `worklist` method: given a queue of
PNPs, we take the PNP on the front, compute its successors, add edges
to the tableau, and add any new nodes to the end of the worklist. We
parameterize `buildTableau` so other code can reuse it (see
`ProofGraph.hs`).

> buildTableau :: Ord a => (PNP a -> [PNP a]) -> [PNP a] -> Tableau a -> Tableau a
> buildTableau _ [] t = t
> buildTableau next (p:worklist) t =
>   let succs    = next p in
>   let t'       = addEdges p succs t in
>   let newNodes = filter (unseen t) succs in
>   buildTableau next (worklist ++ newNodes) t'

Actually constructing the tableau is the matter of kickstarting the
queue with the root node.

> tableau :: Ord a => LTL a -> Tableau a
> tableau f = buildTableau makeSucc [buildRoot f] emptyTableau

The bulk of work takes place in the `makeSucc` function. Each kind of
formula has a particular effect on the successor when in the positive
or negative set of a PNP. The general pattern is to explore the
non-temporal parts of each moment completely: we unfold implication
first, and then we address temporal formulae.

In order to apply these rules, we define a quick helper function that
lets us select an arbitray element matching a predicate from a
set. The `satisfying` function finds a member `x` of a set satisfying
a given predicate and returns a pair of `x` and the set without `x`.

> satisfying :: Ord a => (a -> Bool) -> Set a -> Maybe (a, Set a)
> satisfying p s = do
>   let (ok, notok) = Set.partition p s
>   (v,ok') <- Set.maxView ok
>   return (v, ok' `Set.union` notok)

In particular, we'll use `satisfying` to pull formulae with a
particular shape out of the positive and negative sets. There is
surely an opportunity for optimization here: a set representation that
partitioned by outermost constructor would allow for a faster
implementation of this common operation.

The `makeSucc` function is defined as a series of case analyses:

  1. Contradictory formulae don't take a step (`closed`)
  2. Unfolding implications in the positive set (`posImp`)
  3. Unfolding implications in the negative set (`negImp`)
  4. Unfolding weak until in the positive set (`posW`)
  5. Unfolding weak until in the negative set (`negW`)
  6. Checking for the end of time (`Set.member (X top) (neg q)`)

The definition of `makeSucc` serves as an outline for the the
rule-based algorithm in the style of Kröger and Merz given below.

> makeSucc :: Ord a => PNP a -> [PNP a]
> makeSucc q =  
>   if closed q  -- Bot
>   then []
>   else case satisfying isImp (pos q) of -- (->+)
>     -- Just (Imp F _, posq') -> [q {pos = posq'}] -- opt for forms equiv to TOP
>     Just (Imp a b, posq') -> posImp (typ q) a b posq' (neg q)
>     Just _ -> error "BROKEN INVARIANT: expected Imp in posImp Case"
>     Nothing ->
>       case satisfying isImp (neg q) of -- ( -> -)
>         Just (Imp a b, negq') -> negImp (typ q) a b (pos q) negq'
>         Just _ -> error "BROKEN INVARIANT: expected Imp in negImp case"
>         Nothing ->
>           case satisfying isW (pos q) of -- (W+)
>             Just (W a b, posq') -> posW (typ q) a b posq' (neg q)
>             Just _ -> error "BROKEN INVARIANT: expected W in posW case"
>             Nothing ->
>               case satisfying isW (neg q) of -- (W-)
>                 Just (W a b, negq') -> negW (typ q) a b (pos q) negq'
>                 Just _ -> error "BROKEN INVARIANT: expected W in negW case"
>                 Nothing ->
>                   if (X top `Set.member` neg q) --  && null posq'
>                   then terminalPNP q                -- (end)
>                   else stepPNP q                    -- (o)


The rules for computing successors are applied iteratively in order
from 1 through 5. Each rule is defined as a function that takes (a)
the `PNPType` of the current PNP, (b) the parts of the formula we're
working with, (c) the positive set of the current PNP, and (d) the
negative set of the current PNP; the functions return a list of
successor PNPs.

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

To implement rule 2, we compute both possible successor PNPs. We
assume that `Imp a b` is not a member of `posq'`, i.e., we got here by
using `satisfying` to remove `Imp a b` from the `posq'`.

> posImp :: Ord a => PNPType -> LTL a -> LTL a -> Set (LTL a) -> Set (LTL a) -> [PNP a]
> posImp t a b posq' negq = let t' = stepType t in
>   [
>     PNP t' (Set.insert b $ posq') negq 
>   , PNP t' posq' (Set.insert a $ negq)
>   ]

3. For a PNP `Q` with `a -> b` in `neg Q`, define one successor `Q'`,
such that `pos Q' = pos Q union {a}` and `neg Q = (neg Q \ {a -> b})
union {b}`.

We have `~ (a -> b) == a /\ ~b`, and so we put `a` in the positve set
and `b` in the negative set. We could have just as easily made `pos Q
= {a,~b}`, but then we would eventually have to put `b` in the
negative set---we might as well do the work now.

In the `negImp` function we assume that `Imp a b` is not in `negq'`.

> negImp :: Ord a => PNPType -> LTL a -> LTL a -> Set (LTL a) -> Set (LTL a) -> [PNP a]
> negImp t a b posq negq' =
>   [
>      PNP (stepType t) (Set.insert a posq) (Set.insert b negq')
>   ]

Notice that these first three rules take care of the entirety of
classical logic; every conjunction, disjunction, negation, and
implication that we would want to express is a combination of
variables, implication and `F`. For more information about these
encodings, see `Syntax.hs`

Now we want to move onto temporal operators: `X` and `W`. We consider
`W`, the weak until operator, first, because it could possibly be true
without advancing time at all.

4. For a PNP `Q` with `a W b` in `pos Q`, we define two successors
`Ql` and `Qr`:

  + Let `pos Ql = (pos Q \ {a W b}) union {b}` and `neg Ql = neg Q`.

  + Let `pos Qr = (pos Q \ {a W b}) union {a}` and `neg Ql = neg Q union {X~ a W b}`.

These rules come from the WeakUntilUnroll axiom, which says that `a W
b == b \/ a /\ ~X~ a W b`. We *could* have defined a single successor
which replaced `a W b` with `b \/ a /\ ~X~ a W b`, but explicitly
given two successors allows us to save some propositional encoding
(and its commensurate unrolling with rules 2 and 3).

> posW :: Ord a => PNPType -> LTL a -> LTL a -> Set (LTL a) -> Set (LTL a) -> [PNP a]
> posW t a b posq' negq = let t' = stepType t in
>   [
>     PNP t' (Set.insert b posq') negq
>   , PNP t' (Set.insert a $ Set.insert (wkX (a `W` b)) $ posq') negq
>   ]

5. For a PNP `Q` with `a W b` in `neg Q`, we define two successors,
`Ql` and `Qr`:

  + Let `pos Ql = pos Q`, and let `neg Ql = (neg Q \ {a W b}) union {a,b}`

  + Let `pos Qr = pos Q union {X~(a W b)}`, and `neg Qr = (neg Q \ {a W b}) union {b}`

This comes from a simple consequence of the WeakUntilUnroll axiom,
namely that `~ (a W b) == (~b /\ ~a) \/ ~b /\ X~(a W b)`, so we
appropriately take each branch. Similar to the previous steps, we use
all of the information we have to avoid duplicating work by stepping
through all of the conjunctions, disjunctions, and negations.

> negW :: Ord a => PNPType -> LTL a -> LTL a -> Set (LTL a) -> Set (LTL a) -> [PNP a]
> negW t a b posq negq' = let t' = stepType t in
>   [
>     PNP t' posq (Set.insert a $ Set.insert b negq')
>   , PNP t' (Set.insert (X $ negate $ W a b) posq) (Set.insert b negq')
>   ]

Once a state has been fully explored, i.e., there are no bare
implications or weak untils in either the positive or negative sets,
`makeSucc` has two cases to consider: either we are at then end of
time, and `X top` is in the positive set, or we are not at the end of
time, and we can take a step forwards.

If we decide that we can take a step forwards, the `step` function
advances both the positive and negative sets of the PNP by (a)
dropping all formulae that don't have an `X` in front of them, and (b)
stripping one layer of `X`s off those that do. That is, `step S`
computes the set `{f | X f in S}`. 

> step :: Ord a => Set (LTL a) -> Set (LTL a)
> step = Set.foldr stripF Set.empty
>   where stripF (X f) nextSet = Set.insert f nextSet
>         stripF _     nextSet = nextSet

Given `step`, we can step both sets of a PNP---marking the resulting PNP as having `Temp`oral type:

> stepPNP :: Ord a => PNP a -> [PNP a]
> stepPNP (PNP _ posq negq) = [PNP Temp (step posq) (step negq)]

On the other hand, if we are at the end of time, we cannot take any
steps. To determine what actually holds at the end of time, the
function `dropTemporal` converts a formula `f` into an atemporal
formula. To do so, we take advantage of the fact that `end /\ X y = F`
for any formula `y`. This means that we will convert `X y` to `F`, and
`a W b` to `a \/ b` before recursing on both `a` and `b`. 
    
> dropTemporal :: LTL a -> LTL a
> dropTemporal F = F
> dropTemporal (X _) = F
> dropTemporal (P a) = P a
> dropTemporal (W a b) = dropTemporal a `or` dropTemporal b
> dropTemporal (Imp a b) = Imp (dropTemporal a) (dropTemporal b)

Given a PNP `q`, we can generate a `terminalPNP` that restricts `q`'s
meaning to the end of time (while making sure that `end` information
is still maintained by the PNP, namely `X top` is in the negative
set).

> terminalPNP :: Ord a => PNP a -> [PNP a]
> terminalPNP q = [PNP Term (Set.map dropTemporal $ pos q)
>                          (Set.insert (X top) $ Set.map dropTemporal $ neg q)]

<h3>Finding terminal paths</h3>

Now that we've built the tableau, we need to determine whether or not
the root node is is contradictory. If it *is*, then then the original
formula with injected finiteness is contradictory, i.e., the original
formula is unsatisfiable in a finite model. Otherwise, the formula is
satisfiable.

How can we tell whether the root node is contradictory? Our function
`closed` only accounts for whether a node is contradictory in the
moment, which many nodes are not. Taking `a /\ ~a` as an example, we
must take several steps before arriving at a closed node. To lift the
definition closedness to trees, we say that a node is closed when:

 - its PNP is closed locally, à la `closed`, or
 - all of its successors are closed.

So, to conclude that a node is satsifiable, we only need to find a
path that makes it to the end of time without encountering closedness,
i.e. we get to a `Term` node. We call such paths "terminal paths" and
the `terminalPath` function searches its input Tableau for these
paths.

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

<h3>Avoiding the tableau: direct search</h3>

It turns out that we don't actually need to build the tableau at
all. We can combine the search with the generation procedure itself!
The critical insight is that Kröger and Merz use three criteria for
lifting closedness, defining the closed set of nodes inductively (p.53):

  - it's closed locally, à la `closed` (C1)
  - a node whose successors are all closed is closed (C2)
  - nodes `q` where `always f` is in `neg q` is closed when every path
    from `q` to a node `p` such that `f` in `neg p` contains a closed
    node (C3).

Condition (C3) amounts to saying that having `always f` in the
negative set means `f` is false infinitely often. Checking C3 requires
us to keep the tableau around (or perform expensive recomputation) in
order to ensure that we treat a negated always properly, avoiding
infinite paths that never get around to falsifying `f`. But we don't
have to worry about infinite paths---so we don't need to check for
them in the tableau. But having eliminated C3 as a condition, we can
test our simpler definition for closedness on the fly.

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

We can improve the performance even more by checking for only the
existence of a terminal path without actually calculating it.

> existsTerminalPath :: Ord a => Set (PNP a) -> PNP a -> Bool
> existsTerminalPath _    p | closed p = False
> existsTerminalPath seen p | p `Set.member` seen = False
> existsTerminalPath _    p | typ p == Term = True
> existsTerminalPath seen p =
>   foldr (\q found -> existsTerminalPath (Set.insert p seen) q || found) False (makeSucc p)

<h3>Checking satisfiability and validity</h3>

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
  
