module ExpressionEvaluator (
    equivalentPropositions, 
    contradictoryPropositions,
    impliedProposition,
    evaluateFitch
)
where

import Data.Set (Set, union, empty, singleton, toList)
import Data.Map (Map, member, (!))
import Data.Maybe (fromJust)
import qualified Data.Map
import Control.Applicative (liftA2)
import Expression (Expression (..), Operator (..))

type FitchContext = Map Char Bool

mapFromList :: (Ord a) => [(a,b)] -> Map a b
mapFromList = Data.Map.fromList

operatorEvaluationMap :: Map Operator (Bool -> Bool -> Bool)
operatorEvaluationMap = mapFromList [(And, (&&)),(Or, (||)),(Implies, (\x y->not x||y)),(Iff, (==))]

getVariables :: Expression -> Set Char

getVariables (Variable c) = singleton c
getVariables (Bottom) = empty
getVariables (Not expr) = getVariables expr
getVariables (Expr _ expr1 expr2) = union (getVariables expr1) $ (getVariables expr2)

evaluateFitch :: FitchContext -> Expression -> Maybe Bool

evaluateFitch context (Variable c)
    | member c context = Just (context ! c)
    | otherwise = Nothing

evaluateFitch context (Not expr) = fmap not (evaluateFitch context expr)
evaluateFitch context (Expr op expr1 expr2) = liftA2 f (evaluateFitch context expr1) (evaluateFitch context expr2)
    where f = operatorEvaluationMap!op
evaluateFitch _ Bottom = Just False

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

contradictoryPropositions :: [Expression] -> Bool

contradictoryPropositions [expr] = all (not . fromJust . ($ expr)) (map evaluateFitch contexts)
    where contexts = allContexts [expr]

contradictoryPropositions (expr:exprs) = contradictoryPropositions [foldr (Expr And) expr exprs]
contradictoryPropositions [] = False

impliedProposition :: [Expression] -> Expression -> Bool

impliedProposition [] result = isTautology result
impliedProposition exprs Bottom = contradictoryPropositions exprs
impliedProposition (premise:premises) result = all (fromJust . ($ result)) $ filter (fromJust . ($ totalPremise)) $ mappedContexts
    where contexts = allContexts $ result:premise:premises
          totalPremise = foldr (Expr And) premise premises
          mappedContexts = map evaluateFitch contexts

isTautology :: Expression -> Bool

isTautology expr = all ( fromJust . ($ expr)) (map evaluateFitch contexts)
    where contexts = allContexts [expr]