module ExpressionParser
    (
        LogicToken (..),
        tokensToExpression
    )
where

import Expression (Expression (..), Operator)

data LogicToken = GroupingToken [LogicToken] | VariableToken Char | NotToken
                    | OperatorToken Operator
                    | ResolvedToken (Maybe Expression)
                    deriving (Show)

tokenToExpression :: LogicToken -> Maybe Expression

tokenToExpression (GroupingToken tokens) = tokensToExpression tokens
tokenToExpression (VariableToken c) = Just (Variable c)
tokenToExpression (ResolvedToken expr) = expr
tokenToExpression _ = Nothing

reduceGroupTokens :: [LogicToken] -> [LogicToken]

reduceGroupTokens [] = []
reduceGroupTokens (x:xs) = case x of 
    GroupingToken tokens -> (ResolvedToken $ tokensToExpression tokens):(reduceGroupTokens xs)
    _ -> x:(reduceGroupTokens xs)

reduceNotTokens :: [LogicToken] -> [LogicToken]

reduceNotTokens (x1:x2:xs) = case x1 of
    NotToken -> (ResolvedToken (fmap Not $ tokenToExpression x2)) : (reduceNotTokens xs)
    _ -> x1:(reduceNotTokens (x2:xs))
reduceNotTokens xs = xs

reduceOperatorTokens :: Operator -> [LogicToken] -> [LogicToken]
reduceOperatorTokens op (x1:x2:x3:xs) = case x2 of
    OperatorToken op1 | op1 == op -> (ResolvedToken $ (fmap (Expr op) $ (tokenToExpression x1)) <*> tokenToExpression x3)
        : (reduceOperatorTokens op xs)
    _ -> x1:x2:(reduceOperatorTokens op (x3:xs))

reduceOperatorTokens _ xs = xs

tokensToExpression :: [LogicToken] -> Maybe Expression

tokensToExpression [token] = tokenToExpression token
tokensToExpression tokens = case endReduced of
    [e] -> tokenToExpression e
    _ -> Nothing
    where initReduced = reduceNotTokens . reduceGroupTokens $ tokens
          ops = [(minBound :: Operator) ..]
          endReduced = foldr (.) id (map reduceOperatorTokens ops) $ initReduced