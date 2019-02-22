{-# LANGUAGE OverloadedStrings, DuplicateRecordFields, RecordWildCards, NamedFieldPuns #-}
{-|
 - Module      : Numeric.GLP
 - Description : Specifiy a General Linear Problem and transform to a Standardized LP
 - Copyright   : (c) Torsten Kemps-Benedix, 2019
 -
 - This module 'Numeric.GLP' specifiies a Generalized Linear Problem (or LP in short) and provides means to tranform this into a Standardized LP (see module 'Numeric.LP') that may be solved with e.g. the simplex solver in module 'Numeric.LP.Simplex'.
-}
module Numeric.GLP
-- (GLP, Numeric.GLP.a, c, m1, m2, m3, dir, mkGLP, standardizeGLP)
where

import qualified Data.List                   as L
import           Control.Monad
import qualified Data.Set                    as S
import           Data.Set                    (member, isSubsetOf)
import           Numeric.LinearAlgebra       (I, Element, Matrix, Vector, ident, diagl,
                                              cols, rows, find, toColumns,
                                              fromColumns, cmap, fromList, toList,
                                              (!), (><),
                                              )
import qualified Numeric.LinearAlgebra       as LA
import           Numeric.LinearAlgebra.Devel (modifyMatrix, runSTMatrix,
                                              thawMatrix, mapVectorWithIndex)

-- | This structure defines a General Linear Problem containing ≤
-- and ≥ inequalities and == equalities. The sum of the numbers of
-- inequalities ('m1' times ≤ and 'm2' times ≥) and equalities ('m3'
-- times ==) must match one less than the number of
-- rows of the matrix 'a'. The first (i.e. the zero-th) row of the matrix
-- contains the coefficients of the objective function.
--
-- We assume that \(a_{00}\) is zero. The matrix \(a\) shall have \(m+1\) rows
-- and \(n+1\) columns.
--
-- The formal specification of the problem we intend to solve is as follows:
--
-- Maximize resp. minimize (according to 'dir') the following linear objective
-- function:
--
-- \[ z_0 = \sum_{i=1}^{n} a_{0,i} x_i \]
--
-- Subject to the following linear constraints:
--
-- \[ z_j = a_{j,0} + \sum_{i=1}^{n} a_{j,i} x_i,\, j=1,\ldots,m\]
-- \[ z_j \leq 0,\, j=1,\ldots,m_1\]
-- \[ z_j \geq 0,\, j=m_1+1,\ldots,m_1+m_2\]
-- \[ z_j = 0,\, j=m_1+m_2+1,\ldots,m=m1+m_2+m_3\]
--
-- The original variables \(x_1, \ldots, x_n\) may be constraint to be non-negative,
-- non-positive or they may be unconstrained according to the n-vector
-- \(c\in\{-1,0,+1\}^n\).
--
-- \[ c_j = -1 \Rightarrow x_j \leq 0\]
-- \[ c_j = 1 \Rightarrow x_j \geq 0\]
-- \[ c_j = 0 \Rightarrow x_j \text{ unrestricted} \]
data GLP = GLP {
    a   :: Matrix Double, -- ^ Tableau of coefficients, see above for a formal
                          -- description of their meaning
    c   :: Vector I,      -- ^ Type of constraint for \(x_j\), \(j=1,\ldots,n\),
                          -- see 'GLP' for further details. The element \(c_i\)
                          -- corresponds to column \(i+1\) of the matrix \(a\).
    m1  :: Int,           -- ^ Number of ≤ inequalities
    m2  :: Int,           -- ^ Number of ≥ inequalities
    m3  :: Int,           -- ^ Number of = equalities
    dir :: Dir            -- ^ Whether the objective function is to be maximized
                          -- or minimzed
    } deriving (Show)

-- | This smart constructor checks all the pre-conditions for 'GLP' stated in the
-- description of 'GLP'.
mkGLP :: Matrix Double -> Vector I -> (Int, Int, Int) -> Dir -> Either String GLP
mkGLP a c (m1,m2,m3) dir =
    let m = rows a - 1
        n = cols a - 1
    in if (m /= m1+m2+m3)
       then Left $ "rows a - 1 == "++show m++" /= m1+m2+m3 == "++show (m1+m2+m3)
       else if (m <= 0)
            then Left "The number of constraints is m <= 0"
            else if (n <= 0)
                 then Left "The number of variables n is <= 0"
                 else if not (S.fromList (LA.toList c) `isSubsetOf` (S.fromList [-1,0,1]))
                      then Left "Vector c has elements other than -1, 0, +1"
                      else if LA.size c /= n
                           then error $ "Vector c has not the proper length "++show n
                           else Right (GLP a c m1 m2 m3 dir)

data Dir = Maximize | Minimize deriving Show

-- | Transform the Generalized Linear Problem to a Standardized Linear Problem
-- by means of the following steps:
--
-- 1. If the objective function is to be minimized multiply it by -1.
-- 2. Turn around the ≥-inequalities by negation of the corresponding rows. After this
-- step there are 'm1'+'m2' inequalities of the <= type.
-- 3. For the 'm1'+'m2' ≤-inequalities introduce as many slack variables on the right
-- hand side and make these equalities instead. After this step there are only
-- equalities left as constraints. We do not represent these slack variables in the
-- matrix 'a' and therefore nothing really changes in this step.
-- 4. For those variables \(x_i\) that have a constraint \(x_i \leq 0\) substitute
-- \(x_i \rightarrow -x_i\). This means multiplying the column \(i\) of the matrix
-- \(a\) by \(-1\).
-- 5. For those variables \(x_i\) that are unconstrained introduce new non-negative
-- variables \(x_i = x_i⁺ - x_i⁻\). We give these the indices \(x_i⁺ = x_i\) and
-- \(x_⁻ = x_{i+1}\). The indices of all other variables \(x_k\), \(k>i\) have to be
-- increased by \(1\). The matrix \(a\) therefore grows by one column.
-- 6. Introduce artificial variables \(z_j\) ( \(j=1,\ldots,m\) ) for each equation.
-- This changes the optimization problem and the solver has to take this into account.
--
-- The function returns a modified and standardized GLP and a matrix \(b\) that maps
-- solution vectors (including the objective functions value) of the modified GLP back
-- to solution vectors of the original GLP.
standardizeGLP :: GLP -> (GLP, Matrix Double)
standardizeGLP glp =
    let (glp1, b1) = resolveMin2Max glp
        (glp2, b2) = resolveGeqConstraints glp1
        (glp3, b3) = resolveNonPositiveVars glp2
        (glp4, b4) = resolveUnconstrainedVars glp3
    in (glp4, b1 <> b2 <> b3 <> b4)

resolveMin2Max :: GLP -> (GLP, Matrix Double)
resolveMin2Max glp@GLP{..} = case dir of
        Maximize -> (glp, ident (1+m1+m2+m3))
        Minimize -> (glp{a = mapRow a 0 negate},
                     diagl (-1:(replicate (m1+m2+m3) 1)))

resolveGeqConstraints :: GLP -> (GLP, Matrix Double)
resolveGeqConstraints glp@GLP{..} =
    let a' = foldl (\a j -> mapRow a j negate) a [m1+1..m1+m2] -- negate rows from m1+1 to m1+m2
    in (glp{a = a', m1 = m1+m2, m2 = 0},
        ident (1+m1+m2+m3))

resolveNonPositiveVars :: GLP -> (GLP, Matrix Double)
resolveNonPositiveVars glp@GLP{..} =
    let varsToBeNegated = find (== -1) c
        varsToBeNegatedS = S.fromList varsToBeNegated
        (a', c') = foldl (\(a,c) i ->
                            (mapCol a (i+1) negate,
                             mapVectorWithIndex (\k x -> if k==i
                                                         then 1
                                                         else c!k)
                                                c))
                         (a, c)
                         (find (== -1) c)
    in (glp{a = a', c = c'},
        diagl $ 1:[if i `member` varsToBeNegatedS
                   then -1
                   else 1 | i <- [0..m1+m2+m3-1]])

resolveUnconstrainedVars :: GLP -> (GLP, Matrix Double)
resolveUnconstrainedVars glp@GLP{..} =
    let m = 1+m1+m2+m3
        zCol = vec1 m 0 1
        (a', c', b) =
            let listOfColsAndCs =
                   fmap (\(c1,ci,i1) ->
                            if ci==0
                            then ([c1, cmap negate c1],
                                  [1, 1],
                                  [vec1 m (i1+1) 1,
                                   vec1 m (i1+1) (-1)]) -- duplicate and adjust
                            else ([c1], [ci],
                                  [vec1 m (i1+1) 1])) -- return unchanged
                        (L.zip3 (toColumns a) (toList c) [0..(cols a)-1])
                columns = L.concat $ fmap (\(x,_,_) -> x) listOfColsAndCs
                cs = L.concat $ fmap (\(_,x,_) -> x) listOfColsAndCs
                bs = L.concat $ fmap (\(_,_,x) -> x) listOfColsAndCs
            in (fromColumns columns, fromList cs, fromColumns $ zCol:bs)
    in (glp{a=a', c=c'}, b)

vec1 :: Int -> Int -> Double -> Vector Double
vec1 n i x = fromList $ L.replicate i 0++x:L.replicate (n-i-1) 0

mapRow :: (Element t) => Matrix t -> Int -> (t -> t) -> Matrix t
mapRow a k f = runSTMatrix $ do
                    a' <- thawMatrix a
                    forM_ [0..cols a-1] (\i -> modifyMatrix a' k i f)
                    return a'

mapCol :: (Element t) => Matrix t -> Int -> (t -> t) -> Matrix t
mapCol a k f = runSTMatrix $ do
                    a' <- thawMatrix a
                    forM_ [0..rows a-1] (\i -> modifyMatrix a' i k f)
                    return a'

prettyPrintAsFormulas :: GLP -> String
prettyPrintAsFormulas glp@GLP{..} =
    let rs = LA.toRows a
        m = cols a - 1
        n = rows a - 1
        objFun = (show dir)++
                    " z_0 = "++linExp 0
        zRows = fmap (\k -> "z_"++show k++" = "++linExp k) [1..n]
        linExp k = L.intercalate " + " (
                    L.filter (/= "") $
                    fmap (\(a,i) ->
                            if a /= 0
                            then show a++" x_"++show i
                            else "") (L.zip (toList $ rs!!k) [0..m]))
        zNonNeg  = "z_i ≥ 0"
        xConstr :: I -> Int -> String
        xConstr ck k = "x_"++show k++if ck == -1
                                     then " ≤ 0"
                                     else if ck == 1
                                          then " ≥ 0"
                                          else " unconstrained"
        xConstrs = fmap (uncurry xConstr) (L.zip (toList c) [1..m])
    in L.intercalate "\n" (
            objFun:
            "Subject to":
            (fmap (\line -> "\t"++line) (zRows++[""]++
                                         [zNonNeg, ""]++
                                         xConstrs)))
            ++"\n"

(Right ex1') = ex1
ex1 = let a = (5><5)
                 [   0,    1,  1,  3, -0.5
                 , 740,   -1,  0, -2,  0
                 ,   0,    0, -2,  0,  7
                 ,   0.5,  0, -1,  1, -2
                 ,   9,   -1, -1, -1, -1]
          c = LA.fromList [-1, 1, 0, -1]
      in mkGLP a c (2, 1, 1) Minimize
