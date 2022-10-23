module FitchDisplay
    (
        displayProof
    )
where

import Expression (Expression (..), Operator (..))
import FitchTransform

data FitchDisplay = GivenDisplay Expression | ImplicationDisplay{premise::FitchDisplay,result::Expression} 
    | SubProofDisplay FitchProof

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