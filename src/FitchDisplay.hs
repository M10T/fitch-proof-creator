module FitchDisplay
    (
        displayProof,
        proofToLines,
        removeDuplicates
    )
where

import Expression (Expression (..), Operator (..))
import FitchTransform

data FitchDisplay = GivenDisplay Expression | ImplicationDisplay{premise::FitchDisplay,result::Expression} 
    | SubProofDisplay FitchProof

subEq :: ProofSection -> ProofSection -> Bool
subEq (SubProof (Proof _ p1)) (SubProof (Proof _ p2)) = p1 == p2
subEq _ _ = False

removeDuplicates :: FitchProof -> FitchProof
removeDuplicates p = removeDuplicatesHelper (TopProof []) p

removeDuplicatesHelper :: FitchProof -> FitchProof -> FitchProof
removeDuplicatesHelper acc (TopProof []) = acc
removeDuplicatesHelper acc (Proof p xs) = Proof p fixed 
    where (TopProof fixed) = removeDuplicatesHelper acc (TopProof xs)
removeDuplicatesHelper acc outer = case x of
    SubProof p1 | matchingScoped (subEq $ SubProof (removeDuplicates p1)) acc -> removeDuplicatesHelper acc (TopProof xs)
    SubProof p1 -> removeDuplicatesHelper (TopProof $ as++[SubProof $ removeDuplicates p1]) (TopProof xs)
    Given e -> removeDuplicatesHelper (TopProof $ as++[Given e]) (TopProof xs)
    Implication e | matchingScoped (==Implication e) acc -> removeDuplicatesHelper acc (TopProof xs)
    Implication e | matchingScoped (==Given e) acc && (not $ null xs) -> removeDuplicatesHelper acc (TopProof xs)
    Implication e-> removeDuplicatesHelper (TopProof $ as++[Implication e]) (TopProof xs)
    where (TopProof (x:xs)) = outer
          (TopProof as) = acc

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