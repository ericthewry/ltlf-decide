{-# OPTIONS_GHC -Wall -fno-warn-unused-imports -fno-warn-name-shadowing #-}
{-# LANGUAGE FlexibleInstances #-}

module Pretty where

import Prelude hiding (negate, or, and, until)

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map ((!))
import Data.Maybe

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
--import Data.GraphViz.Commands


import Syntax
import Tableau
import ProofGraph

{- TODO
   label node more clearly
   track transition types more clearly in Tableau.hs (not NECESSARY, but clarity/bug checking)

-}

data NodeLabel
  = NodeLabel {form :: PNPType, nameOf :: String}
  deriving (Show, Eq, Ord) 

data EdgeLabel = Std | OnPath deriving (Show, Eq, Ord)

buildGraph :: Graph gr => PNP NamedProp -> Tableau NamedProp -> [PNP NamedProp] -> gr NodeLabel EdgeLabel
buildGraph root (Tableau t) path = mkGraph nodes edges
  where nodes = map (\(n,num) -> (num, NodeLabel (typ n) (show n)))
                $ Map.toList nodeNumbering
        nodeNumbering = snd $
                        Map.foldrWithKey 
                        (\src dsts (ctr, numbering) ->
                          countNodes (src:dsts) ctr numbering) 
                        (1, Map.singleton root 0)
                        t
        countNodes ns ctr numbering = 
          foldr 
          (\n (ctr, numbering) -> if Map.member n numbering 
                                  then (ctr,   numbering)
                                  else (ctr+1, Map.insert n ctr numbering))
          (ctr,numbering) 
          ns
        edges = Map.foldrWithKey
                (\src dsts edges -> 
                  map (\dst -> (nodeNumbering ! src, 
                                nodeNumbering ! dst,
                                if (src,dst) `elem` epath
                                then OnPath 
                                else Std)) dsts ++ edges)
                []
                t
        epath = nodesToEdges path


nodesToEdges :: [PNP NamedProp] -> [(PNP NamedProp, PNP NamedProp)]
nodesToEdges [] = []
nodesToEdges [_] = []
nodesToEdges (n:n':ns) = (n,n') : nodesToEdges (n':ns)



prettyLTL :: (LTL NamedProp -> Tableau NamedProp) -> LTL NamedProp -> FilePath -> FilePath -> IO ()
prettyLTL tblConstr f graphFile texFile  =
  do ns <- ltlToPDF tblConstr f (buildRoot f) graphFile 
     nodesToTex ns texFile

prettyTableau, prettyGraph :: LTL NamedProp -> FilePath -> FilePath -> IO ()
prettyTableau = prettyLTL tableau
prettyGraph = prettyLTL pgraphs

prettySig :: PNP NamedProp -> FilePath -> FilePath -> IO ()
prettySig p pdf tex =
  do
    ns <- runGraphviz dot Pdf pdf >> return (labNodes g)
    nodesToTex ns tex

  where
    dot = graphToDot nonClusteredParams (g :: Gr NodeLabel EdgeLabel)
    g = buildGraph p t []
    t = sigmaGraph p

ltlToPDF :: (LTL NamedProp -> Tableau NamedProp) -> LTL NamedProp -> PNP NamedProp -> FilePath -> IO [LNode NodeLabel]
ltlToPDF tblConstr f root filename  = runGraphviz dot Pdf filename >> return (labNodes g)
  where dot = graphToDot params (g :: Gr NodeLabel EdgeLabel)
        params = nonClusteredParams { fmtEdge = colorPath, fmtNode = colorNode }

        colorPath (_,_,Std) = []
        colorPath (_,_,OnPath) = [color Red]

        stateColor = LightSteelBlue1 --MediumAquamarine
        colorNode (0, _)          = [fillColor stateColor, style filled]
        colorNode (_, NodeLabel Norm _)  = []
        colorNode (_, NodeLabel Temp _) = [fillColor stateColor, style filled]
        colorNode (_, NodeLabel Term _) = [shape Ellipse, Peripheries 2]

        g = buildGraph root t (fromMaybe [] $ terminalPath t Set.empty root)
        t = tblConstr f
          

nodesToTex :: [LNode NodeLabel] -> FilePath -> IO ()
nodesToTex ns filename = writeFile filename $ makeTable ns
  where makeTable ns = header ++ body ns ++ footer
        header = "\\begin{tabular}[b]{c c} \n    Node & Contents \\\\ \\hline \n"
        footer = "    \\hline \n\\end{tabular}"
        body ns = foldr addLine "" ns
        addLine (num, node) txt = "    $Q_{" ++ show num ++ "}$ & $" ++ nameOf node ++ "$ \\\\ \n" ++ txt


        
