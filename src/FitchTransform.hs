module FitchTransform 
    (
        proofGiven,
        transformProof,
        safeTransformProof,
        FitchProof (..),
        ProofSection (..),
        matchingExpression,
        matchingSubproof,
        matchingScoped,
        matchingScopedExpression,
        appendSection
    )
where

import Expression (Expression (..), Operator (..))
import ExpressionEvaluator (equivalentPropositions, contradictoryPropositions, impliedProposition)
import Data.Maybe (fromJust)
import Data.List (nub)

data FitchProof = Proof FitchProof [ProofSection] | TopProof [ProofSection]
    deriving Eq

data ProofSection = Given Expression | Implication Expression | SubProof FitchProof
    deriving (Show, Eq)

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

getSections :: FitchProof -> [ProofSection]
getSections (TopProof sections) = sections
getSections (Proof parent sections) = sections

addImplication :: FitchProof -> Expression -> FitchProof
addImplication (Proof parent sections) expr = Proof parent (sections++[Implication expr])
addImplication (TopProof sections) expr = TopProof $ sections++[Implication expr]

addSubproof :: FitchProof -> FitchProof -> FitchProof
addSubproof (Proof parent sections) newSection = Proof parent (sections++[SubProof newSection])
addSubproof (TopProof sections) newSection = TopProof $ sections++[SubProof newSection]

matchingExpression :: (Expression -> Bool) -> FitchProof -> Bool
matchingExpression _ (TopProof []) = False
matchingExpression p (TopProof (x:xs)) = case x of
    Given e | p e -> True
    Implication e | p e -> True
    _ -> matchingExpression p (TopProof xs)
matchingExpression p (Proof parent sections) = (matchingExpression p (TopProof sections)) 
                                                    || (matchingExpression p parent)

matchingScopedExpression :: (Expression -> Bool) -> FitchProof -> Bool
matchingScopedExpression p (TopProof xs) = matchingExpression p (TopProof xs)
matchingScopedExpression p (Proof parent sections) = (matchingExpression p (TopProof sections))

matchingSubproof :: (FitchProof -> Bool) -> FitchProof -> Bool
matchingSubproof p (TopProof []) = False
matchingSubproof p (TopProof (x:xs)) = case x of
    SubProof proof -> p proof || matchingSubproof p (TopProof xs)
    _ -> matchingSubproof p (TopProof xs)
matchingSubproof p (Proof _ xs) = matchingSubproof p (TopProof xs)

matchingScoped :: (ProofSection -> Bool) -> FitchProof -> Bool
matchingScoped p (TopProof sections) = any p sections
matchingScoped p (Proof _ sections) = any p sections

firstExpression :: (Expression -> Bool) -> FitchProof -> Maybe Expression
firstExpression _ (TopProof []) = Nothing
firstExpression p (TopProof (x:xs)) = case x of
    Given e | p e -> Just e
    Implication e | p e -> Just e
    _ -> firstExpression p (TopProof xs)
firstExpression p (Proof parent sections) = case (firstExpression p (TopProof sections)) of
    Just e -> Just e
    Nothing -> (firstExpression p parent)

removeLast :: FitchProof -> FitchProof
removeLast (TopProof []) = TopProof []
removeLast (Proof parent []) = Proof parent []
removeLast (TopProof xs) = TopProof $ init xs
removeLast (Proof parent xs) = Proof parent $ init xs

appendSection :: FitchProof -> ProofSection -> FitchProof
appendSection (TopProof xs) s = TopProof (xs++[s])
appendSection (Proof p xs) s = Proof p (xs++[s])

directIntroduction :: Expression -> ProofSection -> Bool
directIntroduction e1 (Given e2) = direct e1 e2
directIntroduction e1 (Implication e2) = direct e1 e2
directIntroduction (Not e1) (SubProof (Proof _ xs)) 
    = (head xs == (Given $ Not e1)) && (last xs == Implication Bottom)
directIntroduction (Expr Implies e1 e2) (SubProof (Proof _ xs))
    = (head xs == (Given $ e1)) && (last xs == Implication e2)
directIntroduction _ _ = False

direct :: Expression -> Expression -> Bool
direct e1 e2 | e1 == e2 = True
direct e1 (Expr And e2 e3) | (e1 == e2) || (e1 == e3) = True
direct (Expr Or e1 e2) e3 | (e1 == e3) || (e2 == e3) = True
direct e1 (Not (Not e2)) | e1 == e2 = True
direct Bottom (Expr And e1 e2) | (e1 == Not e2) || (e2 == Not e1) = True
direct _ _ = False

indirectProvable :: FitchProof -> Expression -> Expression -> Bool
indirectProvable proof e1 e2 | direct e1 e2 = True
indirectProvable proof (Expr And e1 e2) e3 | indirectProvable proof e1 e3 && indirectProvable proof e2 e3 = True
indirectProvable proof e1 (Expr And e2 e3) | indirectProvable proof e1 e2 || indirectProvable proof e1 e3 = True
indirectProvable proof e1 (Expr Or e2 e3) | indirectProvable proof e1 e2 && indirectProvable proof e1 e3 = True
indirectProvable proof (Expr Or e1 e2) e3 | indirectProvable proof e1 e3 || indirectProvable proof e2 e3 = True
indirectProvable proof (Not (Expr Or e1 e2)) e3
    | e3 /= equivAnd && indirectProvable proof equivAnd e3 = True
    where equivAnd = (Expr And (invertNot e1) (invertNot e2)) 
indirectProvable proof e3 (Not (Expr And e1 e2))
    | e3 /= equivAnd && indirectProvable newProof e3 equivAnd = True
    where equivAnd = (Expr Or (invertNot e1) (invertNot e2)) 
          newProof = addImplication proof equivAnd
indirectProvable proof e1 (Not (Not e2)) = indirectProvable proof e1 e2
indirectProvable proof e1 (Expr Implies e2 e3)
    |  indirectProvable proof e1 e3 && indirectProvable proof e2 (invertNot e1) = True 
    |  indirectProvable proof e1 e3 && matchingExpression (indirectProvable proof e2) proof= True
indirectProvable _ _ _ = False

proveIndirect :: FitchProof -> Expression -> Expression -> FitchProof
proveIndirect proof result premise | result == premise = proof
proveIndirect proof (Expr And e1 e2) e3 = addImplication initialProof (Expr And e1 e2)
    where initialProof = proveIndirect (proveIndirect proof e1 e3) e2 e3 
proveIndirect proof result (Expr And e1 e2)
    | indirectProvable proof result e1 = proveIndirect (addImplication proof e1) result e1
    | indirectProvable proof result e2 = proveIndirect (addImplication proof e2) result e2
proveIndirect proof result (Expr Or e1 e2) = addImplication initialProof result
    where p1 = proveIndirect (Proof proof [Given e1]) result e1
          p2 = proveIndirect (Proof proof [Given e2]) result e2
          initialProof = addSubproof (addSubproof proof p1) p2
proveIndirect proof (Expr Or e1 e2) e3
    | indirectProvable proof e1 e3 = addImplication (proveIndirect proof e1 e3) (Expr Or e1 e2)
    | indirectProvable proof e2 e3 = addImplication (proveIndirect proof e2 e3) (Expr Or e1 e2)
proveIndirect proof (Not (Expr Or e1 e2)) e3
    | e3 /= equivAnd && indirectProvable proof equivAnd e3 
        = transformProof (proveIndirect proof equivAnd e3) (Not (Expr Or e1 e2))
    where equivAnd = (Expr And (invertNot e1) (invertNot e2)) 
proveIndirect proof e3 (Not (Expr And e1 e2)) 
    | e3 /= equivAnd && indirectProvable newProof e3 equivAnd = proveIndirect transformed e3 equivAnd
    where equivAnd = (Expr Or (invertNot e1) (invertNot e2))
          newProof = addImplication proof equivAnd
          transformed = transformProof proof equivAnd
proveIndirect proof e1 (Not (Not e2)) = proveIndirect initialProof e1 e2
    where initialProof = addImplication proof e2 
proveIndirect proof e1 (Expr Implies e2 e3)
    | indirectProvable proof e1 e3 && indirectProvable proof e2 (invertNot e1)
        = transformProof (addImplication (addSubproof proof sub) (Not $ invertNot e1)) e1
    where sub0 = Proof proof [Given $ invertNot e1]
          sub1 = proveIndirect sub0 e2 (invertNot e1)
          sub2 = proveIndirect (addImplication sub1 e3) e1 e3
          sub = addImplication (addImplication sub2 goal) Bottom
          goal = Expr And e1 (invertNot e1)
proveIndirect proof e1 (Expr Implies e2 e3)
    | matchingExpression (indirectProvable proof e2) proof && indirectProvable proof e1 e3
        = transformProof (addImplication (transformProof proof e2) e3) e1

proofImplies :: FitchProof -> Expression -> Bool
proofImplies proof result = impliedProposition (getGivens proof) result

invertNot :: Expression -> Expression
invertNot (Not e) = e
invertNot e = Not e

directContradiction :: FitchProof -> Expression -> Expression -> Bool
directContradiction _ Bottom _ = True
directContradiction _ _ Bottom = True
directContradiction _ (Not e1) e2 | e1 == e2 = True
directContradiction _ e1 (Not e2) | e1 == e2 = True
directContradiction proof e1 e2 | indirectProvable proof (invertNot e1) e2 = True
directContradiction proof e1 e2 | indirectProvable proof (invertNot e2) e1 = True
directContradiction _ _ _ = False

indirectContradiction :: FitchProof -> Expression -> Bool
indirectContradiction proof (Expr And e1 e2) | directContradiction proof e1 e2 = True
indirectContradiction proof expr | matchingExpression (directContradiction proof expr) proof = True
indirectContradiction proof (Expr Or e1 e2)
    | indirectContradiction proof e1 && indirectContradiction proof e2 = True
indirectContradiction proof (Not (Expr Or e1 e2))
    | indirectContradiction (addImplication proof equivAnd) equivAnd = True
    where equivAnd = (Expr And (invertNot e1) (invertNot e2)) 
indirectContradiction proof (Expr And e1 e2)
    | indirectContradiction proof e1 || indirectContradiction proof e2 = True
indirectContradiction proof (Not (Expr And e1 e2))
    | indirectContradiction (addImplication proof equivAnd) equivAnd = True
    where equivAnd = (Expr Or (invertNot e1) (invertNot e2)) 
indirectContradiction proof (Expr Implies e1 e2)
    | matchingExpression (indirectProvable proof e1) proof && indirectContradiction proof e2 = True
    | indirectContradiction proof (invertNot e1) && indirectContradiction proof e2 = True
indirectContradiction _ _ = False

proveIndirectContradiction :: FitchProof -> Expression -> FitchProof
proveIndirectContradiction proof (Expr And e1 e2)
    | directContradiction proof e1 e2 && (indirectProvable proof (invertNot e1) e2)
        = addImplication
            (transformProof (proveIndirect proof (invertNot e1) e2) (Expr And e1 (invertNot e1)))
            Bottom
    | directContradiction proof e1 e2 && (indirectProvable proof (invertNot e2) e1)
        = addImplication
            (transformProof (proveIndirect proof (invertNot e2) e1) (Expr And e2 (invertNot e2)))
            Bottom

proveIndirectContradiction proof expr 
    | matchingExpression (directContradiction proof expr) proof = 
        case (fromJust (firstExpression (directContradiction proof expr) proof)) of
            Bottom -> addImplication proof Bottom
            e2 | indirectProvable proof (invertNot expr) e2 -> addImplication 
                (addImplication (proveIndirect proof (invertNot expr) e2) (Expr And expr (invertNot expr)))
                Bottom
            e2 | indirectProvable proof (invertNot e2) expr 
                -> proveIndirectContradiction proof e2

proveIndirectContradiction proof (Expr Or e1 e2)
    | indirectContradiction proof e1 && indirectContradiction proof e2
        = addImplication (addSubproof (addSubproof proof sub1) sub2) Bottom
        where sub1 = transformProof (Proof proof [Given e1]) Bottom
              sub2 = transformProof (Proof proof [Given e2]) Bottom

proveIndirectContradiction proof (Not (Expr Or e1 e2))
    | indirectContradiction (addImplication proof equivAnd) equivAnd = proveIndirectContradiction transformed equivAnd
    where equivAnd = Expr And (invertNot e1) (invertNot e2)
          transformed = removeLast $ transformProof proof equivAnd

proveIndirectContradiction proof (Expr And e1 e2)
    | indirectContradiction proof e1 = proveIndirectContradiction (transformProof proof e1) e1
    | indirectContradiction proof e2 = proveIndirectContradiction (transformProof proof e2) e2

proveIndirectContradiction proof (Not (Expr And e1 e2))
    | indirectContradiction (addImplication proof equivAnd) equivAnd = proveIndirectContradiction transformed equivAnd
    where equivAnd = Expr Or (invertNot e1) (invertNot e2)
          transformed = transformProof proof equivAnd

proveIndirectContradiction proof (Expr Implies e1 e2)
    | matchingExpression (indirectProvable proof e1) proof && indirectContradiction proof e2
        = proveIndirectContradiction (addImplication (transformProof proof e1) e2) e2
    | indirectContradiction proof (invertNot e1) && indirectContradiction proof e2
        = proveIndirectContradiction (addImplication (transformProof proof e1) e2) e2

provable :: FitchProof -> Expression -> Bool
provable proof expr = (matchingExpression (indirectProvable proof expr) proof) 
    || (indirectContradiction proof (invertNot expr))

transformProof :: FitchProof -> Expression -> FitchProof

--transformProof currentProof result
--    | null $ firstExpression (\_->True) currentProof = transformProof complete result
--        where inv = invertNot result
--              sub = transformProof (Proof currentProof [Given inv]) Bottom 
--             complete = addImplication (addSubproof currentProof sub) (Not inv)

transformProof currentProof result
    | matchingScoped (==Implication result) currentProof = currentProof
    | matchingExpression (direct result) currentProof = addImplication currentProof result 
    | matchingExpression (indirectProvable currentProof result) currentProof 
        = proveIndirect currentProof result 
            (fromJust $ firstExpression (indirectProvable currentProof result) currentProof)

transformProof currentProof Bottom
    | matchingExpression (indirectContradiction currentProof) currentProof
        = proveIndirectContradiction currentProof usable
        where usable = fromJust $ firstExpression (indirectContradiction currentProof) currentProof 
    
transformProof currentProof result = case result of
    (Expr And expr1 expr2) -> addImplication (transformProof (transformProof currentProof expr1) expr2) result
    (Expr Implies e1 e2) -> addImplication 
        (addSubproof currentProof (transformProof (Proof currentProof [Given e1]) e2))
        result
    (Expr Or e1 e2) | provable currentProof e1 -> addImplication (transformProof currentProof e1) result
                    | provable currentProof e2 -> addImplication (transformProof currentProof e2) result
    (Not expr) -> 
        addImplication (addSubproof currentProof $ transformProof (Proof currentProof [Given expr]) Bottom) result
    _ | result /= Bottom -> transformProof (addImplication (
            addSubproof currentProof (transformProof (Proof currentProof [Given $ invertNot result]) Bottom)
        ) (Not $ invertNot result)) result

safeTransformProof :: FitchProof -> Expression -> Maybe FitchProof
safeTransformProof currentProof result
    | not $ impliedProposition (getGivens currentProof) result = Nothing

safeTransformProof currentProof result = Just $ transformProof currentProof result