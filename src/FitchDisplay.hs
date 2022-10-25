module FitchDisplay
    (
        displayProof,
        proofToLines,
        optimize
    )
where

import Expression (Expression (..), Operator (..))
import FitchTransform
import qualified Data.Set (fromList)

data FitchDisplay = GivenDisplay Expression | ImplicationDisplay{premise::FitchDisplay,result::Expression} 
    | SubProofDisplay FitchProof

subEq :: ProofSection -> ProofSection -> Bool
subEq (SubProof (Proof _ p1)) (SubProof (Proof _ p2)) 
    = (getGivens $ TopProof p1) == (getGivens $ TopProof p2) && ((last p1) == (last p2))
subEq _ _ = False

allSections :: FitchProof -> [ProofSection]
allSections (TopProof xs) = xs
allSections (Proof _ xs) = xs

optimize :: FitchProof -> FitchProof
optimize = removeRedundant . removeDuplicates

removeDuplicates :: FitchProof -> FitchProof
removeDuplicates (TopProof p) = removeDuplicatesHelper (TopProof []) (TopProof p)
removeDuplicates (Proof o p) = removeDuplicatesHelper (Proof o []) (TopProof p)

removeDuplicatesHelper :: FitchProof -> FitchProof -> FitchProof
removeDuplicatesHelper acc (TopProof []) = acc
removeDuplicatesHelper acc (Proof p xs) = Proof p fixed 
    where (TopProof fixed) = removeDuplicatesHelper acc (TopProof xs)
removeDuplicatesHelper acc outer = case x of
    SubProof p1 | matchingScoped (subEq $ SubProof (optimize p1)) acc -> removeDuplicatesHelper acc (TopProof xs)
    SubProof p1 -> removeDuplicatesHelper (appendSection acc (SubProof $ optimize p1)) (TopProof xs)
    Given e -> removeDuplicatesHelper (appendSection acc (Given e)) (TopProof xs)
    Implication e | matchingScoped (==Implication e) acc -> removeDuplicatesHelper acc (TopProof xs)
    Implication e | matchingExpression (==e) acc && (not $ null xs) -> removeDuplicatesHelper acc (TopProof xs)
    Implication e-> removeDuplicatesHelper (appendSection acc (Implication e)) (TopProof xs)
    where (TopProof (x:xs)) = outer
          as = case acc of
            (TopProof ys)->ys
            (Proof p ys)->ys

removeRedundant :: FitchProof -> FitchProof
removeRedundant (TopProof p) = removeRedundantHelper (TopProof []) (TopProof p)
removeRedundant (Proof o p) = removeRedundantHelper (Proof o []) (TopProof p)

removeRedundantHelper :: FitchProof -> FitchProof -> FitchProof
removeRedundantHelper acc (TopProof []) = acc
removeRedundantHelper acc (Proof p xs) = Proof p fixed
    where (TopProof fixed) = removeRedundantHelper acc (TopProof xs)
removeRedundantHelper acc outer = case x of 
    SubProof sp | f sp && lastExpr sp == lastExpr outer 
        -> optimize (foldl appendSection acc (allSections $ optimize (notGivens sp)))
    expr -> removeRedundantHelper (appendSection acc expr) (TopProof xs)
    where (TopProof (x:xs)) = outer
          as = case acc of
            (TopProof ys) -> ys
            (Proof p ys)->ys
          f proof = all (\x->matchingExpression (==x) acc) (getGivens proof)
          lastExpr (TopProof ps) = y
            where (Implication y) = last ps
          lastExpr (Proof _ ps) = y
            where (Implication y) = last ps
          isGiven (Given _) = True
          isGiven _ = False
          notGivens (TopProof xs) = TopProof (filter (not . isGiven) xs)
          notGivens (Proof p xs) = Proof p (filter (not . isGiven) xs)
          

sectionToDisplay :: ProofSection -> FitchDisplay
sectionToDisplay (Given expr) = GivenDisplay expr 

displayProofSection :: ProofSection -> IO ()
displayProofSection (Given expr) = putStrLn $ "Given: "++(show expr)
displayProofSection (Implication expr) = print expr
displayProofSection (SubProof proof) = putStrLn "\nSubproof:" >> displayProof proof >> putStrLn "End Subproof\n"

displayProof :: FitchProof -> IO ()
displayProof (TopProof []) = putStrLn "Empty Proof"
displayProof (TopProof exprs) = mapM_ displayProofSection exprs
displayProof (Proof parent exprs) = displayProof (TopProof exprs)

sectionToLines :: ProofSection -> [String]
sectionToLines (Given expr) = ["Given: "++(show expr)]
sectionToLines (Implication expr) = [show expr]
sectionToLines (SubProof proof) = ["","Subproof:"] ++ proofToLines proof ++ ["End Subproof",""]

proofToLines :: FitchProof -> [String]
proofToLines (TopProof []) = ["Empty Proof"]
proofToLines (TopProof exprs) = foldr (++) [] (map sectionToLines exprs)
proofToLines (Proof _ exprs) = proofToLines (TopProof exprs)