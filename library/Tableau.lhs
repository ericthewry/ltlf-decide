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
case `pos P'' = {~a}, neg P'' = {}`. Then to complete the evaluation, the successor of `P''` has only `a` in the negative set. Since this is not contradictory, we conclude that `a /\ X~a` is "satisfiable".

This process should feel similar to Brzozowski & Antimirov
derivatives.

We need only discuss how formulae like `a W b` are processed by the
tableau. Luckily there is a sound axiom called WeakUntilUnroll that
tells us that `a W b == b \/ a /\ ~X~(a W b)` and suddenly we dont
have a temporal formula on the top level and can continue exploring
the current state.

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

TODO : TALK ABOUT CLOSED-NESS AND WHAT IT MEANS

> closed :: Ord a => PNP a -> Bool
> closed p = F `Set.member` pos p
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

The basic idea of `buildRoot` is that it injects a formula `f` into the positive set of an empty PNP. In an LTL decision procedure that's all we would need to do, but in an LTLf decision procedure we need to take another simple step, which is to "inject finiteness". In other words, we insert one of the axioms of LTLf, FINITE, into the positive set. The FINITE axiom says `ever end` which means that eventually time will end. 

> buildRoot :: Ord a => LTL a -> PNP a
> buildRoot f = PNP Norm (Set.fromList [f, ever end]) Set.empty

The functions `ever` and `end` are new, but can be defined in terms of `W`, `F` and `->`. For the full definition, see `./Syntax.hs`.

Now we can move onto defining the `makeSucc` function; it will take a
PNP and return a list of successor PNPs. Since we are searching to
find a contradiction, we want to define the `makeSucc` function such
that for a PNP `P`, if every successor in `makeSucc P` is
unsatisfiable, then `P` is also unsatisfiable. Since closed PNPs are
unsatisfiable, we will eventually need to find a path that ends in a
`Term` PNP with no closed nodes on it. For now, we are just concerned with how to define the `makeSucc` function.

> step :: Ord a => Set (LTL a) -> Set (LTL a)
> step s = Set.map (\(X f) -> f) $ Set.filter isX s
>
> sigma_one :: Ord a => PNP a -> Set (LTL a)  
> sigma_one  p = step $ pos p
>
> sigma_four :: Ord a => PNP a -> Set (LTL a)
> sigma_four p = step $ neg p

TODO Describe why and how we drop-temporal
    
> dropTemporal :: LTL a -> LTL a
> dropTemporal F = F
> dropTemporal (X _) = F
> dropTemporal (P a) = P a
> dropTemporal (W a b) = dropTemporal a `or` dropTemporal b
> dropTemporal (Imp a b) = Imp (dropTemporal a) (dropTemporal b)
>
> terminalPNP :: Ord a => PNP a -> PNP a
> terminalPNP q = PNP Term (Set.map dropTemporal $ pos q) (Set.insert (X top) $ Set.map dropTemporal $ neg q)


TODO : DEFINE THE RULES HERE IN PLAIN ENGLISH

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


TODO : Describe the fixpoint

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

----------------------------------------------------------------------
-- Path finding
----------------------------------------------------------------------


> terminalPath :: Ord a => Tableau a -> Set (PNP a) -> PNP a -> Maybe [PNP a]
> terminalPath _ _    p | closed p            = Nothing
> terminalPath _ seen p | p `Set.member` seen = Nothing
> terminalPath _ _    p | typ p == Term       = Just [p]
> terminalPath t seen p =
>   let succs = successors p t in -- what if I just replace this with makeSucc?
>   let paths = mapMaybe (terminalPath t (Set.insert p seen)) succs in
>   case paths of
>     []       -> Nothing
>     (path:_) -> Just (p:path)

> path :: Ord a => LTL a -> Maybe [PNP a]
> path f = terminalPath (tableau f) Set.empty (buildRoot f)


------------------------------------------------------------------------
-- Satisfiability and validity checking
------------------------------------------------------------------------

> valid :: Ord a => LTL a -> Bool
> valid = isNothing . path . negate

> sat, unsat :: Ord a => LTL a -> Bool
> sat   = isJust . path
> unsat = not . sat

> satString :: Ord a => LTL a -> String
> satString f = if sat f then "sat" else "unsat"

> check :: Ord a => LTL a -> String
> check f =
>   if valid f
>   then "valid"
>   else if sat f
>        then "sat" else "unsat"

> doCheck :: String -> String
> doCheck = check . parse'

> doSatCheck :: String -> String
> doSatCheck s =
>   if sat $ parse' s
>   then "sat"
>   else "unsat"

----------------------------------------------------------------------
-- OTHER STUFF // Maybe unnecessary
----------------------------------------------------------------------

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


> sigma_five :: Ord a => PNP a -> Set (LTL a)
> sigma_five  p= Set.filter
>              (\f -> case f of
>                      (W a b) -> a `Set.member` pos p
>                                 || b `Set.member` neg p
>                      _      -> False)
>              (neg p)

TODO : This doesn't seem necessary here.

> sigma :: Ord a => PNP a -> PNP a
> sigma p = p {
>   pos = sigma_one p `Set.union` sigma_two p `Set.union` sigma_three p,
>   neg = sigma_four p `Set.union` sigma_five p
>   }
 TODO : is this necessary?

> getPrimitives :: PNP a -> PNP a
> getPrimitives p = p { pos = Set.filter isProp (pos p),
>                       neg = Set.filter isProp (neg p)}
  
