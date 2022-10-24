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
import Data.Char (isSpace)

data Operator = And | Or | Implies | Iff deriving (Enum, Show, Eq, Ord, Bounded)

data Expression = Variable Char | Bottom | Not Expression 
                    | Expr Operator Expression Expression
                deriving (Eq, Ord)

data LogicToken = GroupingToken [LogicToken] | VariableToken Char | NotToken
                    | OperatorToken Operator
                    | ResolvedToken (Maybe Expression)
                    deriving (Show)

instance Show Expression where
    show (Variable c) = [c]
    show (Not (Variable c)) = "~"++[c]
    show (Not e1) = "~("++(show e1)++")"
    show Bottom = "⊥"
    show (Expr op e1 e2) = case (e1,e2) of
        ((Expr _ _ _),(Expr _ _ _))->"("++(show e1)++")"++[opC]++"("++(show e2)++")"
        ((Expr _ _ _),_)->"("++(show e1)++")"++[opC]++(show e2)
        (_,(Expr _ _ _))->(show e1)++[opC]++"("++(show e2)++")"
        _ -> (show e1) ++ [opC] ++ (show e2)
        where (opC,_)=head $ filter (\(_,o)->o==op) (Data.Map.toList operatorCharMap)

mapFromList :: (Ord a) => [(a,b)] -> Map a b
mapFromList = Data.Map.fromList

operatorCharMap :: Map Char Operator
operatorCharMap = mapFromList [('&',And),('v',Or),('→',Implies),('↔',Iff)]


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
    | x=='!' = stringToTokens ('⊥':xs)
stringToTokens (x:y:xs)
    | [x,y]=="=>" = stringToTokens ('→':xs)
stringToTokens (x:xs)
    | isSpace x = stringToTokens xs
    | x == '⊥' = fmap ((:) (ResolvedToken $ Just Bottom)) (stringToTokens xs)
    | elem x ['A'..'Z'] = fmap ((:) (VariableToken x)) (stringToTokens xs)
    | member x operatorCharMap = fmap ((:) (OperatorToken $ operatorCharMap!x)) (stringToTokens xs)
    | x == '~' = fmap (NotToken:) (stringToTokens xs)
    | x == '(' = liftA2 ((:) . GroupingToken) (stringToTokens $ init groupSection) (stringToTokens remainder)
    | otherwise = Nothing
        where groupSection = balancedParens xs 1
              remainder = drop (length groupSection) xs

instance Read (Expression) where
    readsPrec _ s = [(fromJust $ join $ (fmap tokensToExpression) $ stringToTokens $ s, "")]