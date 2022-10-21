module FitchTransform 
    (
        transformProof,
        safeTransformProof
    )
where

import Expression (Expression (..), Operator (..))
import ExpressionEvaluator (equivalentPropositions, contradictoryPropositions, impliedProposition)
import Data.Maybe (fromJust)
import Data.List (nub)

data FitchProof = Proof FitchProof [ProofSection] | TopProof [ProofSection]

data ProofSection = Given Expression | Implication Expression | SubProof FitchProof | DirectStep Expression Expression
    deriving (Show)

instance Show FitchProof where
    show (Proof _ sections) = "Proof "++(show sections)
    show (TopProof sections) = "Proof "++(show sections)

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

addSubproof :: FitchProof -> FitchProof -> FitchProof
addSubproof (Proof parent sections) newSection = Proof parent (sections++[SubProof newSection])
addSubproof (TopProof sections) newSection = TopProof $ sections++[SubProof newSection]

addStep :: FitchProof -> Expression -> Expression -> FitchProof
addStep (Proof parent sections) e1 e2 = Proof parent (sections++[DirectStep e1 e2])
addStep (TopProof sections) e1 e2 = TopProof $ sections++[DirectStep e1 e2]

matchingExpression :: (Expression -> Bool) -> FitchProof -> Bool
matchingExpression _ (TopProof []) = False
matchingExpression p (TopProof (x:xs)) = case x of
    Given e | p e -> True
    Implication e | p e -> True
    _ -> matchingExpression p (TopProof xs)
matchingExpression p (Proof parent sections) = (matchingExpression p (TopProof sections)) 
                                                    || (matchingExpression p parent)

matchingSubproof :: (FitchProof -> Bool) -> FitchProof -> Bool
matchingSubproof p (TopProof []) = False
matchingSubproof p (TopProof (x:xs)) = case x of
    SubProof proof -> p proof || matchingSubproof p (TopProof xs)
    _ -> matchingSubproof p (TopProof xs)
matchingSubproof p (Proof _ xs) = matchingSubproof p (TopProof xs)

firstExpression :: (Expression -> Bool) -> FitchProof -> Maybe Expression
firstExpression _ (TopProof []) = Nothing
firstExpression p (TopProof (x:xs)) = case x of
    Given e | p e -> Just e
    Implication e | p e -> Just e
    _ -> firstExpression p (TopProof xs)
firstExpression p (Proof parent sections) = case (firstExpression p (TopProof sections)) of
    Just e -> Just e
    Nothing -> (firstExpression p parent)

direct :: Expression -> Expression -> Bool
direct e1 e2 | e1 == e2 = True
direct e1 (Expr And e2 e3) | (e1 == e2) || (e1 == e3) = True
direct (Expr Or e1 e2) e3 | (e1 == e3) || (e2 == e3) = True
direct e1 (Not (Not e2)) | e1 == e2 = True
direct Bottom (Expr And e1 e2) | (e1 == Not e2) || (e2 == Not e1) = True
direct _ _ = False

indirectProvable :: Expression -> Expression -> Bool
indirectProvable e1 e2 | direct e1 e2 = True
indirectProvable (Expr And e1 e2) e3 = indirectProvable e1 e3 && indirectProvable e2 e3
indirectProvable e1 (Expr And e2 e3) = indirectProvable e1 e2 || indirectProvable e1 e3
indirectProvable e1 (Expr Or e2 e3) = indirectProvable e1 e2 && indirectProvable e1 e3 
indirectProvable (Expr Or e1 e2) e3 = indirectProvable e1 e3 || indirectProvable e2 e3
indirectProvable e1 (Not (Not e2)) = indirectProvable e1 e2
indirectProvable _ _ = False

proveIndirect :: FitchProof -> Expression -> Expression -> FitchProof
proveIndirect proof result premise | result == premise = proof
proveIndirect proof (Expr And e1 e2) e3 = addImplication initialProof (Expr And e1 e2)
    where initialProof = proveIndirect (proveIndirect proof e1 e3) e2 e3 
proveIndirect proof result (Expr And e1 e2)
    | indirectProvable result e1 = proveIndirect (addImplication proof e1) result e1
    | indirectProvable result e2 = proveIndirect (addImplication proof e2) result e2
proveIndirect proof result (Expr Or e1 e2) = addImplication initialProof result
    where p1 = proveIndirect (Proof proof [Given e1]) result e1
          p2 = proveIndirect (Proof proof [Given e2]) result e2
          initialProof = addSubproof (addSubproof proof p1) p2
proveIndirect proof (Expr Or e1 e2) e3
    | indirectProvable e1 e3 = addImplication (proveIndirect proof e1 e3) (Expr Or e1 e2)
    | indirectProvable e2 e3 = addImplication (proveIndirect proof e2 e3) (Expr Or e1 e2)
proveIndirect proof e1 (Not (Not e2)) = proveIndirect initialProof e1 e2
    where initialProof = addImplication proof e2 

proofImplies :: FitchProof -> Expression -> Bool
proofImplies proof result = impliedProposition (getGivens proof) result

invertNot :: Expression -> Expression
invertNot (Not e) = e
invertNot e = Not e

directContradiction :: Expression -> Expression -> Bool
directContradiction Bottom _ = True
directContradiction (Not e1) e2 | e1 == e2 = True
directContradiction e1 e2 | indirectProvable (invertNot e1) e2 = True
directContradiction e1 e2 | directContradiction e2 e1 = True
directContradiction _ _ = False

indirectContradiction :: FitchProof -> Expression -> Bool
indirectContradiction proof (Expr And e1 e2) | directContradiction e1 e2 = True
indirectContradiction proof expr | matchingExpression (directContradiction expr) proof = True
indirectContradiction proof (Expr Or e1 e2)
    | indirectContradiction proof e1 && indirectContradiction proof e2 = True
indirectContradiction proof (Not (Expr Or e1 e2))
    | indirectContradiction proof (Expr And (invertNot e1) (invertNot e2)) = True

proveIndirectContradiction :: FitchProof -> Expression -> FitchProof
proveIndirectContradiction proof (Expr And e1 e2)
    | directContradiction e1 e2 = addImplication
        (addImplication (proveIndirect proof (invertNot e1) e2) (Expr And e1 (invertNot e1)))
        Bottom

proveIndirectContradiction proof expr 
    | matchingExpression (directContradiction expr) proof = 
        case (fromJust $ firstExpression directContradiction expr) proof of
            Bottom -> addImplication proof Bottom
            e2 -> addImplication 
                (addImplication (proveIndirect proof (invertNot expr) e2) (Expr And expr (invertNot expr)))
                Bottom

proveIndirectContradiction proof (Expr Or e1 e2)
    | matchingExpression (indirectContradiction e1) proof
        && matchingExpression (indirectContradiction e2) proof
        = addImplication (addSubproof (addSubproof proof sub1) sub2) Bottom
        where sub1 = transformProof (Proof proof [Given e1]) Bottom
              sub2 = transformProof (Proof proof [Given e2]) Bottom

proveIndirectContradiction proof (Not (Expr Or e1 e2))
    | indirectContradiction proof equivAnd = proveIndirectContradiction transformed equivAnd
    where equivAnd = Expr And (invertNot e1) (invertNot e2)
          transformed = transformProof proof equivAnd

transformProof :: FitchProof -> Expression -> FitchProof

transformProof currentProof result
    | null $ firstExpression (\_->True) currentProof = transformProof complete result
        where inv = invertNot result
              sub = transformProof (Proof currentProof [Given inv]) Bottom 
              complete = addImplication (addSubproof currentProof sub) (Not inv)

transformProof currentProof result
    | matchingExpression (==result) currentProof = currentProof
    | matchingExpression (direct result) currentProof = addImplication currentProof result 
    | matchingExpression (indirectProvable result) currentProof 
        = proveIndirect currentProof result (fromJust $ firstExpression (indirectProvable result) currentProof)

transformProof currentProof Bottom
    | not (null usableGivens) = 
        addImplication (addImplication (transformProof currentProof (invertNot x)) (Expr And x (invertNot x))) Bottom
    where allGivens = getGivens currentProof
          provableFrom g = matchingExpression (indirectProvable (invertNot g)) currentProof
          usableGivens = filter provableFrom allGivens
          x = head usableGivens

transformProof currentProof Bottom
    | matchingExpression possible currentProof =
        addImplication (addSubproof (addSubproof currentProof sub1) sub2) Bottom
    where possible (Expr Or e1 e2) = 
            matchingExpression (indirectProvable (invertNot e1)) currentProof
                && matchingExpression (indirectProvable (invertNot e2)) currentProof
          possible _ = False
          (Expr Or f1 f2) = fromJust $ firstExpression possible currentProof
          sub1 = transformProof (Proof currentProof [Given f1]) Bottom
          sub2 = transformProof (Proof currentProof [Given f2]) Bottom
    
transformProof currentProof result = case result of
    (Expr And expr1 expr2) -> addImplication (transformProof (transformProof currentProof expr1) expr2) result
    (Not expr) -> 
        addImplication (addSubproof currentProof $ transformProof (Proof currentProof [Given expr]) Bottom) (Not expr)
    _ -> transformProof (addImplication (
            addSubproof currentProof (transformProof (Proof currentProof [Given invertNot result]) Bottom)
        ) (Not $ invertNot result)) result

safeTransformProof :: FitchProof -> Expression -> Maybe FitchProof
safeTransformProof currentProof result
    | not $ impliedProposition (getGivens currentProof) result = Nothing

safeTransformProof currentProof result = Just $ transformProof currentProof result