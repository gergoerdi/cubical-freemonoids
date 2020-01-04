{-# LANGUAGE NoMonomorphismRestriction, FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}

import Data.Tree
import Diagrams.Prelude
import Diagrams.Backend.PGF.CmdLine
import Diagrams.TwoD.Layout.Tree
import Control.Monad
import Data.List.Extra (chunksOf)

xs >< ys = Node Nothing [xs, ys]

tree1 = xs >< (ys >< zs)
tree2 = (xs >< ys) >< zs

xs = Node (Just "xs") []
ys = Node (Just "ys") []
zs = Node (Just "zs") []

renderParen node t =
    renderTree toNode
               (~~)
               (symmLayout' (with & slHSep .~ 4 & slVSep .~ 4) t)
    # centerXY # pad 1.1
  where
    toNode Nothing = text ":⋄:" <> (square 2 # fc lightgreen)
    toNode (Just s) = node s <> (circle 1.4 # fc yellow)

main = do
    renderPGF "MonoidSyntax.pgf" (mkWidth 300) $
      zline 2 $
        [ toDiag tree1 === label "xs ⋄ (ys ⋄ zs)"
        , toDiag tree2 === label "(xs ⋄ ys) ⋄ zs"
        ]
  where
    toDiag p = renderParen text p :: Diagram B

    label s = text s <> strutX 12 <> strutY 2

zline :: Int -> [Diagram B] -> Diagram B
zline n =
    foldr (===) mempty .
    map (foldr (|||) mempty) .
    chunksOf n .
    map frame
  where
    frame = atop (square 10 # lcA transparent)
