module ExpressionTokenizer
    (stringToTokens)
where

import ExpressionParser (LogicToken (..))
import Expression (operatorCharMap)
import Data.Map (member, (!))
import Control.Applicative (liftA2)

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