module Expression
    (
        Expression (..),
        Operator (..)
    )
where

import Data.Map (Map, member, (!))
import Control.Applicative (liftA2)
import Control.Monad (join)
import Data.Maybe (fromJust)
import qualified Data.Map

data Operator = And | Or | Implies | Iff deriving (Enum, Show, Eq, Ord, Bounded)

data Expression = Variable Char | Bottom | Not Expression 
                    | Expr Operator Expression Expression
                deriving (Show, Eq, Ord)

data LogicToken = GroupingToken [LogicToken] | VariableToken Char | NotToken
                    | OperatorToken Operator
                    | ResolvedToken (Maybe Expression)
                    deriving (Show)

mapFromList :: (Ord a) => [(a,b)] -> Map a b
mapFromList = Data.Map.fromList

operatorCharMap :: Map Char Operator
operatorCharMap = mapFromList [('∧',And),('∨',Or),('→',Implies),('↔',Iff)]


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

balancedParens :: String -> Int -> String

balancedParens [] _ = []
balancedParens [x] n 
    | n == 0 = []
    | otherwise = [x]
balancedParens (x:xs) n
    | n == 0 = []
    | x == '(' = x:(balancedParens xs (n+1))
    | x == ')' = x:(balancedParens xs (n-1))
    | otherwise = x:(balancedParens xs n)

stringToTokens :: String -> Maybe [LogicToken]

stringToTokens [] = Just []
stringToTokens (x:xs)
    | elem x ['A'..'Z'] = fmap ((:) (VariableToken x)) (stringToTokens xs)
    | member x operatorCharMap = fmap ((:) (OperatorToken $ operatorCharMap!x)) (stringToTokens xs)
    | x == '~' = fmap (NotToken:) (stringToTokens xs)
    | x == '(' = liftA2 ((:) . GroupingToken) (stringToTokens $ init groupSection) (stringToTokens remainder)
    | otherwise = Nothing
        where groupSection = balancedParens xs 1
              remainder = drop (length groupSection) xs

instance Read (Expression) where
    readsPrec _ s = [(fromJust $ join $ (fmap tokensToExpression) $ stringToTokens $ s, "")]