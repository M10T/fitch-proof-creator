module FitchTransform 
    ()
where

import Expression (Expression (..), Operator (..))
import ExpressionEvaluator (equivalentPropositions, contradictoryPropositions, impliedProposition)

data FitchProof = Proof FitchProof [ProofSection] | TopProof [ProofSection]
data ProofSection = Given Expression | Implication Expression | SubProof FitchProof

proofGiven :: [Expression] -> FitchProof
proofGiven givens = TopProof $ map Given givens 

getGivens :: FitchProof -> [Expression]
getGivens (TopProof []) = []
getGivens (TopProof (section:sections)) = case section of 
    Given expr -> expr:(getGivens $ TopProof sections)
    _ -> getGivens $ TopProof sections
getGivens (Proof parent sections) = (getGivens parent)++(getGivens $ TopProof sections)

addImplication :: FitchProof -> Expression -> FitchProof
addImplication (Proof parent sections) expr = Proof parent (sections++[Implication expr])
addImplication (TopProof sections) expr = TopProof $ sections++[Implication expr]

matchingSection :: (ProofSection -> Bool) -> FitchProof -> Bool

--matchingExpression p (TopProof sections) = any (mapAnyToSection p) sections
--matchingExpression p (Proof parent sections) = (any (mapAnyToSection p) sections) 
--                                                    || (matchingExpression p parent)

proofImplies :: FitchProof -> Expression -> Bool
proofImplies proof result = impliedProposition (getGivens proof) result

transformProof :: FitchProof -> Expression -> FitchProof
transformProof currentProof result
    | matchingExpression (==result) currentProof = currentProof
    | otherwise = case result of
        (Variable c) -> 
        (Expr And expr1 expr2) | matchingExpression (==expr1) currentProof 
                    && matchingExpression (==expr2) currentProof -> addImplication currentProof result
        (Expr And expr1 expr2) -> addImplication (transformProof (transformProof currentProof expr1) expr2) result