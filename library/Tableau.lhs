> {-# OPTIONS_GHC -Wall -fno-warn-unused-imports -fno-warn-name-shadowing #-}
> {-# LANGUAGE TemplateHaskell,FlexibleContexts, FlexibleInstances #-}


Here we present a simple decision procedure for Linear Temporal Logic
over finite traces (henceforth LTLf). For the Syntax full syntax,
please consult `./Syntax.hs`. Notice that type of terms is `LTL a`,
because the syntax of LTL and LTLf is exactly the same. Since LTLf is
a variant of LTL, we adopt the prieval name for the syntax.

The semantics of the language are fairly simple. Formulae in the logic
are evaluated over traces, which are arrays of valuation functions
that take variables to truth values. There are three ways that a
formula can be evaluated. It can be evaluated in a single state, the
next state, or some collection of states, now and in the
future.

Say we are in some position `i` in a trace `t` of length `n`. If we
swant to know omething about the current state `i` we can simply write
a standard propositional logical formula. We will use the minimal
presentation that uses variables, implication and the always-false
symbol `F` (sometimes called "bot").  If we want to know about state
`i+1`, then we write down formulae of the form `X f`, where `f`
is another formula. When evaluated n the trace `t`, we say that `X f`
is true in the current state iff `f` is true at state `i+1`, provided
`i+1 < n`.

These two syntactic and semantic forms are sufficient to
express properties about the future, when we know exactly when we want
to evaluate an event. To see if a property `f` holds 3 steps in the
future, check `X X X f`. But we have no way to express statements like
"always in the future a `f` holds" or "sometime in the future `f`
holds". To do this, we introduce the binary infix "weak until"
operator (`W`). When evaluating `f W f'` at position `i` in a trace
`t` of length `n`, we say that `f W f'` is true if and only if there
exists a position `j` in the trace `t` such that `f` holds at all
positions between `i` and `j` and if `j+1 <= n`, then `f'` holds at
position `j+1` of `t`.

Our goal in defining a decision procedure is to take an arbitrary LTLf
formula `f` and determine whether there exists a trace `t` such that
`f` holds in `t` at position 0. If there is such a trace, we say that
`f` is "satsifiable". Otherwise it is unsatisfiable. To do this we
will define a Tableau structure explores all the implications of a
given formula, and try and find a contradiction. If we can find no
contradiction, we conclude that the formula is satisfiable.

For example, given the formula `a /\ ~a`, we want to be able to find
the contradiction, so we will explore all of the implications of the
formula `a /\ ~a`. We define a Positive Negative Pair to be a pair of
sets of formulae, `pos` and `neg`, that keep track of the formulae
that `a /\ ~a` implies must be true and false (respectively). We say
that a PNP is `closed` if the intersection between `pos and `neg` is
nonempty. It might be tempting to say that the PNP `(pos = {a/\~a},
neg = {})` is closed, because it is a conjunction of variable and its
negation. While we can say that as humans, the decision procedure
needs a little bit more structure.

To start, we create the root node `P` of the Tableau labeled with the
PNP where `pos P = {a/\~a}` and `neg P = {}`. Since `a/\~a => a` and
`a /\ ~a => ~a`, create a successor PNP called `P'` with both
implications in it's positive set i.e. `pos P' = {a,~a}` and `neg P'=
{}`. Since `a` is a variable, there is nothing we can do to reduce it
further, but we can reduce `~a`! If `~a` is true it must be that `a`
is false, so we can put `a` in the `neg` set. Now we define another
successor PNP `P''` that `pos P'' = {a}` and `neg P'' = {a}`. Since so
their intersection is nonempty, and so the PNP is closed. Now we can
conclude that `a/\~a` is unsatisfiable.

So, how do we process temporal formulae? Let's see what would happen
with a formula like `a /\ X (~a)`. We would, as above, create a PNP
`P` with `pos P = {a /\ X ~a}` and `neg P = {}`. Then, we would follow
the same steps for conjunction to get to a successor PNP `P'` with
`pos = {a,X~a}` and `neg = {}`. Again, since `a` is a variable, there
isn't anything we can do with it. However, there is something we can
do with the formula `X~a`. If we were talking about the trace
semantics, we would step `X ~a` forwards to the next state in the
trace and evaluate `~a` there. In the Tableau we create a successor
`P''` of `P'` that has none of the non-temporal formulae (in this case
of `P''`), and removes one step of the temporal information. In our
case `pos P'' = {~a}, neg P'' = {}`. Then to complete the evaluation,
the successor of `P''` has only `a` in the negative set. Since this is
not contradictory, we conclude that `a /\ X~a` is "satisfiable".

This process should feel similar to Brzozowski & Antimirov
derivatives.

We need only discuss how formulae like `a W b` are processed by the
tableau. Luckily there is a sound axiom called WeakUntilUnroll that
tells us that `a W b == b \/ a /\ ~X~(a W b)`. Now, we apply this
transformation to get rid of the temporal formulae at the top level of
the AST. We continue by processing the disjunction, conjunction,
negation.

So far, we've discussed a decision procedure for LTL on infinite
traces. There some small tricks that we do that make this method work
for LTL on finite traces. We'll see these in a bit; for now, lets look
at how we implement this Tableau decision procedure for LTLf.

To evoke the methodology by which we produce a decision procedure, we've called the module `Tableau`.

> module Tableau where
> import Prelude hiding (negate, or, and, until)
> 
> -- Dependencies
> import Data.List hiding (or, and)
> import Data.List.Split (endBy)
> 
> import Data.Maybe (mapMaybe, isNothing, isJust, fromMaybe)
> 
> import Data.Map (Map)
> import qualified Data.Map as Map
> -- 
> import Data.Set (Set)
> import qualified Data.Set as Set

>
> -- Importing the LTLf syntax.
> import Syntax

As described above, the nodes of the Tableau are PNPs.Intuitively, the
`pos` set is the set of LTLf formulae that are true, and the `neg` set
is the set of formulae that are false.

The labels represent the different roles that PNPs will play in our
tableau. `Norm` PNPs represent the exploration of the current time
step. `Temp` PNPs represent the first PNP to explore a new time
step. `Term` PNPs represent the exploration of the end of time.

> data PNPType
>   = Norm | Temp | Term
>     deriving (Show, Eq, Ord)

This is the first hint so far about how LTLf differs from LTL. Namely
that we need a way to differentiate behavior at the end of time.  

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
`i` is checked before rule `i+1`):

1. For a PNP `Q`, if `Q` is closed or if `F` is in `pos Q`, take no
step.

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

3. For a PNP `Q` with `a -> b` in `neg Q`, define one successors `Q'`,
such that `pos Q' = pos Q union {a}` and `neg Q = (neg Q \ {a -> b})
union {b}`.

Again, we can use the classical logic tautology `~ a -> b == a /\ ~b`,
and so we put a in the positve set and `b` in the negative set. We
could have just as easily made `pos Q = {a,~b}`, but then we would
eventually have to put `b` in the negative set, and that is extra,
unnecessary work that we can do here in one step.

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

5. For a PNP `Q` with `a W b` in `neg Q`, we define two successors,
`Ql` and `Qr`:

  + Let `pos Ql = pos Q`, and let `neg Ql = (neg Q \ {a W b}) union {a,b}`

  + Let `pos Qr = pos Q union {X~(a W b)}`, and `neg Qr = (neg Q \ {a W b}) union {b}`

This comes from a simple consequence of the WeakUntilUnroll axiom,
namely that `~ (a W b) == (~b /\ ~a) \/ ~b /\ X~(a W b)`, so we
appropriately take each branch. Similar to the previous steps, we use
all of the information we have to avoid duplicating work by stepping
through all of the conjunctions, disjunctions and negations.

Now that we can explore each individual state in time, we can step
forward in time. There are two cases to consider here, either we are
at then end of time, and `X top` is in the positive set, or we are not
at the end of time, and we can take a step forwards.

If we decide that we can take a step forwards, we will apply the
`step` function to both the positive and negative sets of the
PNP. When applied to a set `S`, this function computes the set `{f | X
f in S}`. It drops all formulae that were expanded in the previous
time step and keeps onlu those that must be evaluated in the next time
step.

> step :: Ord a => Set (LTL a) -> Set (LTL a)
> step = Set.foldr (\f nextSet ->
>            case f of
>              (X f) -> Set.insert f nextSet
>              _ -> nextSet
>         ) Set.empty

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
> terminalPNP :: Ord a => PNP a -> PNP a
> terminalPNP q = PNP Term (Set.map dropTemporal $ pos q)
>                          (Set.insert (X top) $ Set.map dropTemporal $ neg q)

Now, we can put all of these pieces together into one `makeSucc` function!

> makeSucc :: Ord a => PNP a -> [PNP a]
> makeSucc q =  
>   if (not $ Set.null $ pos q `Set.intersection` neg q)
>      || F `Set.member` pos q    -- Bot
>   then []
>   else case satisfying isImp (pos q) of -- (->+)
>     -- Just (Imp F _, posq') -> [q {pos = posq'}] -- opt for forms equiv to TOP
>     Just (Imp a b, posq') ->
>       [constr q (Set.insert b posq') (neg q) , -- need to use constr q here?????
>        constr q posq' (Set.insert a $ neg q)]
>     Just _ -> error "Expected Imp in posImp Case"
>     Nothing ->
>       case satisfying isImp (neg q) of -- ( -> -)
>         Just (Imp a b, negq') ->
>           [constr q (Set.insert a $ pos q) (Set.insert b negq')]
>         Just _ -> error "Expected Imp in negImp case"
>         Nothing ->
>           case satisfying isW (pos q) of -- (W+)
>             Just (W a b, posq') ->
>               [constr q (Set.insert b posq') (neg q),
>                constr q (posq' `Set.union` (Set.fromList [a, wkX (a `W` b)])) (neg q)
>               ]
>             Just _ -> error " expected W in posW case"
>             Nothing ->
>               case satisfying isW (neg q) of -- (W-)
>                 Just (W a b, negq') ->
>                   [constr q (pos q) (negq' `Set.union` Set.fromList [a,b]),
>                    constr q
>                      (Set.insert (X (negate (a `W` b))) (pos q))
>                      (Set.insert b negq')]
>                 Just _ -> error "expected W in negW case"
>                 Nothing ->
>                   let posq' = sigma_one q in
>                   if (X top `Set.member` neg q) && null posq'
>                   then [terminalPNP q]                -- (end)
>                   else [PNP Temp posq' (sigma_four q)] -- (o)
>   where
>     constr :: PNP a -> (Set (LTL a) -> Set (LTL a) -> PNP a)
>     constr (PNP Term _ _) = PNP Term
>     constr (PNP _ _ _)    = PNP Norm
>     
>     satisfying :: Ord a => (a -> Bool) -> Set a -> Maybe (a, Set a)
>     satisfying pred s = do
>       let (sat, unsat) = Set.partition pred s
>       (v,sat') <- Set.maxView sat
>       return (v, sat' `Set.union` unsat)


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
>
> path :: Ord a => LTL a -> Maybe [PNP a]
> path f = if existsTerminalPath Set.empty (buildRoot f) then Just [] else Nothing


Now as defined before we can process the result of the `path` function
as `sat`, `unsat` and `valid` which take LTLf formulae and return
whether or not they are satisfiable, unsatisfiable or valid,
respectively.

> sat, unsat, valid :: Ord a => LTL a -> Bool
> sat   = isJust . path
> unsat = not . sat
> valid = isNothing . path . negate

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
  
