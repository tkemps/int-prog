{-# LANGUAGE OverloadedStrings, RecordWildCards, NamedFieldPuns #-}
module Numeric.LP where

import           Control.Monad
import           Data.Array.IArray           (Array, (//))
import qualified Data.Array.IArray           as A
import           Data.Maybe
import qualified Data.Text.Lazy              as T
import qualified Data.Text.Lazy.Builder      as TB
import qualified Formatting                  as F
import           Numeric.LinearAlgebra       (I, Matrix, Vector, atIndex, cols,
                                              flatten, ident, minIndex, rows,
                                              subMatrix, subVector, (!), (><),
                                              (?), (|||), (¿))
import qualified Numeric.LinearAlgebra       as LA
import           Numeric.LinearAlgebra.Devel (atM', modifyMatrix, runSTMatrix,
                                              thawMatrix)
import           Text.UnicodeTable

data LP = LP {
    a        :: Matrix Double,
    lhs, rhs :: Vector I}

lp2Table :: Int -> Int -> LP -> Table
lp2Table nPrec nColW LP{..} = mkTable ta cws hs vs
    where rN = rows a
          cN = cols a
          taElem r c | r>0 && c>0 = F.bprint (F.fixed nPrec) $ a `atIndex` (r-1, c-1)
                     | r==0 && c>1 = TB.fromString $ "x"++show (rhs!(c-1))
                     | r==1 && c==0 =  TB.fromString "z"
                     | r>1 && c==0 = TB.fromString $ "x"++show (lhs!(r-1))
                     | otherwise = TB.fromString ""
          ta = A.array ((0,0), (rN, cN)) [((r,c), taElem r c) | r <- [0..rN], c <- [0..cN]]
          cws = A.listArray (0,cN) (replicate (cN+1) nColW)
          hs = konstArray0 (rN+2) NoLine // [(0, SingleLine), (1, DoubleLine), (rN+1, SingleLine)]
          vs = konstArray0 (cN+2) NoLine // [(0, SingleLine), (1, DoubleLine), (cN+1, SingleLine)]

konstArray0 :: Int -> e -> Array Int e
konstArray0 n x = A.listArray (0,n-1) (replicate n x)

instance Show LP where
    show = T.unpack . TB.toLazyText . fromTable . lp2Table 4 15

transfromToEquationalForm :: Matrix Double -> Matrix Double
transfromToEquationalForm a = a ||| (ident (rows a))

choosePivot :: LP -> Maybe (Int, Int)
choosePivot LP {..} =
    let c = subVector 1 (cols a-1) (flatten $ a ? [0])
        b = subVector 1 (cols a-1) (flatten $ a ¿ [0])
        a' = subMatrix (1,1) (rows a-1, cols a-1) a
    in case LA.find (>0) c of
            s:_ ->
                let as = flatten $ a' ¿ [s] -- column s as a vector
                in Just (1 + minIndex (b / as), 1+s)
            _ -> Nothing

-- see <https://en.wikipedia.org/wiki/Simplex_algorithm>
-- Let's solve the following problem:
--      maximize $c^t x$ subject to
--      Ax ≤ b
--      ∀i, xᵢ ≥ 0
--      x,c ∈ ℝⁿ, b ∈ ℝ^p, A ∈ ℝ^pxn

ex1 :: LP
ex1 = LP {a = (3><3)[0,2,-4, 2,-6,1, 8,3,-4],
          lhs = LA.fromList [0,1,4],
          rhs = LA.fromList [0,2,3]
        }

simplexStep :: LP -> Int -> Int -> LP
simplexStep (LP {..}) sr sc =
    let theta = atM' a sr sc -- save the pivot element
        pc = flatten $ a ¿ [sc] -- save the whole pivot column
        a' = runSTMatrix
            (do
                a'm <- thawMatrix a
                -- replace each row -- except the pivot row -- by that linear combination
                -- of itself and the pivot row which makes its pivot column entry zero.
                forM_ [r | r <- [0..(rows a - 1)], r /= sr] $ \r -> do
                    let m = (-1) * (a `atIndex` (r,sc)) / theta
                    forM_ [0..(cols a - 1)] $ \i -> do
                        modifyMatrix a'm r i (\x -> x + m * (a `atIndex` (sr,i)))
                -- divide the pivot row by the negative of the pivot
                forM_ [0..(cols a - 1)] $ \i -> do
                        modifyMatrix a'm sr i (\x -> x/(-theta))
                -- replace the pivot by the negative of its saved reciprocal
                modifyMatrix a'm sr sc (\_ -> 1/theta)
                -- replace the other elements of the pivot column by its saved values divided
                -- by the saved pivot element
                forM_ [r | r <- [0..(rows a - 1)], r /= sr] $ \j -> do
                        modifyMatrix a'm j sc (\_ -> pc!j/theta)
                return a'm)
    in LP a' lhs rhs

main :: IO ()
main = do
    putStrLn (show ex1)
    let (LP {..}) = ex1
    let (sr, sc) = fromJust $ choosePivot ex1
    putStrLn ("Pivot row/column: "++(show sr)++", "++(show sc))
    let theta = atM' a sr sc
    putStrLn ("Pivot element: "++(show theta))

