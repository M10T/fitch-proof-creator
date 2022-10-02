module FitchTransform 
    (transformExpressions)
where

import Expression (Expression)
import ExpressionEvaluator (equivalentPropositions, contradictoryPropositions)

transformExpressions :: [Expression] -> Expression -> Maybe [Expression]

transformExpressions exprs expr2
    | all (equivalentPropositions expr2) exprs = Nothing
    | otherwise = Nothing