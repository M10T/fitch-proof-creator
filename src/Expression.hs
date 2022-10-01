module Expression
    (Expression, equivalentPropositions)
where

import Data.Set (Set, union, empty, singleton, toList)
import Data.Map (Map, member, (!))
import Data.Maybe (fromJust)
import qualified Data.Map

data Expression = Variable Char | Bottom | Not Expression | And Expression Expression | Or Expression Expression
                deriving (Show, Eq, Ord)

type FitchContext = Map Char Bool

mapFromList :: (Ord a) => [(a,b)] -> Map a b
mapFromList = Data.Map.fromList

getVariables :: Expression -> Set Char

getVariables (Variable c) = singleton c
getVariables (Bottom) = empty
getVariables (Not expr) = getVariables expr
getVariables (And expr1 expr2) = union (getVariables expr1) $ (getVariables expr2)
getVariables (Or expr1 expr2) = union (getVariables expr1) $ (getVariables expr2)

evaluateFitch :: FitchContext -> Expression -> Maybe Bool

evaluateFitch context (Variable c)
    | member c context = Just (context ! c)
    | otherwise = Nothing

evaluateFitch context (And expr1 expr2) = (fmap (&&) (evaluateFitch context expr1)) <*> (evaluateFitch context expr2)
evaluateFitch context (Or expr1 expr2) = (fmap (||) (evaluateFitch context expr1)) <*> (evaluateFitch context expr2)
evaluateFitch context (Not expr) = fmap not (evaluateFitch context expr)
evaluateFitch _ Bottom = Nothing

allBooleans :: Int -> [[Bool]]

allBooleans 1 =  [[True], [False]]
allBooleans n = [x++y | x <- (allBooleans $ n-1), y <- (allBooleans 1)]

allContexts :: [Expression] -> [FitchContext]

allContexts exprs = map (mapFromList . zip allVars) (allBooleans (length allVars))
   where allVars = toList $ (foldr union) empty (map getVariables exprs)

equivalentPropositions :: Expression -> Expression -> Bool

equivalentPropositions expr1 expr2 = all id (map maybeEquals (map evaluateFitch contexts))
    where contexts = allContexts [expr1, expr2]
          maybeEquals = (\f -> fromJust (f expr1) == fromJust (f expr2))