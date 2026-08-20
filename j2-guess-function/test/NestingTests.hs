-- Conditions that contain conditions.
{-# OPTIONS_GHC -O0 #-}

module NestingTests
    ( nestingTests
    ) where

import           Control.Exception (evaluate)
import qualified System.Timeout as Timeout
import           Test.Tasty (TestTree, localOption, testGroup)
import           Test.Tasty.HUnit (Assertion, assertFailure, testCase)
import           Test.Tasty.Runners (NumThreads(..))

import           ExprREq (alphaEtaEquivalent)
import           Lib (guess)
import           Lib.ExprR (ExprR(..))
import           PerformanceTests (capFor, forceExprR)

nestingTests :: Int -> TestTree
nestingTests hardcore =
    localOption (NumThreads 1) $
        testGroup
            "nested conditions"
            [ testGroup
                "group a"
                [ testCase "nest01" $
                    quotesWithin (scaledCap 0.28)
                        ("guess (nest01 " ++ show depth01 ++ ")")
                        (expectedNest01 depth01)
                        (guess $ nest01 depth01)
                ]
            , testGroup
                "group b"
                [ testCase "nest02 600" $
                    quotesWithin (capFor 0.11)
                        "guess (nest02 600)"
                        (expectedNest02 600)
                        (guess $ nest02 600)
                , testCase "nest03" $
                    quotesWithin (capFor 0.08)
                        (labelled "nest03" depth03)
                        (expectedNest03 depth03)
                        (guess $ nest03 depth03)
                , testCase "nest04" $
                    quotesWithin (capFor 0.05)
                        (labelled "nest04" depth04)
                        (expectedNest04 depth04)
                        (guess $ nest04 depth04)
                , testCase "nest05" $
                    quotesWithin (capFor 0.08)
                        (labelled "nest05" depth05)
                        (expectedNest05 depth05)
                        (guess $ nest05 depth05)
                ]
            , testGroup
                "group c"
                [ testCase "nest07" $
                    quotes
                        "guess nest07"
                        (lams ["predicate", "value", "pad"] $
                            IteR
                                (AppR (VarR "predicate") (VarR "value"))
                                (VarR "value")
                                (VarR "pad"))
                        (guess nest07)
                , testCase "nest08" $
                    quotes
                        "guess nest08"
                        (lams ["predicate", "value", "pad"] $
                            IteR
                                (AppR (VarR "predicate") (VarR "value"))
                                (VarR "value")
                                (VarR "pad"))
                        (guess nest08)
                , testCase "nest09" $
                    quotes
                        "guess nest09"
                        (lams ["step", "predicate", "value", "pad"] $
                            IteR (AppR (VarR "predicate") stepped) stepped stepped)
                        (guess nest09)
                , testCase "nest10" $
                    quotes
                        "guess nest10"
                        (lams ["step", "combine", "value"] $
                            IteR
                                (AppR (AppR (VarR "combine") stepped) stepped)
                                stepped
                                (VarR "value"))
                        (guess nest10)
                , testCase "nest11" $
                    quotesWithin (capFor 0.13)
                        (labelled "nest11" depth11)
                        (expectedNest11 depth11)
                        (guess $ nest11 depth11)
                , testCase "nest06" $
                    quotesWithin (capFor 0.04)
                        (labelled "nest06" depth06)
                        (expectedNest04 depth06)
                        (guess $ nest06 depth06)
                ]
            , testGroup
                "group d"
                [ testCase "nest12" $
                    quotesWithin (scaledCap 0.28)
                        ("guess (nest12 " ++ show depth12 ++ ")")
                        (expectedNest12 depth12)
                        (guess $ nest12 depth12)
                , testCase "nest13" $
                    quotesWithin (scaledCap 0.30)
                        ("guess (nest13 " ++ show depth13 ++ ")")
                        (expectedNest13 depth13)
                        (guess $ nest13 depth13)
                ]
            ]
  where
    scaledCap :: Double -> Int
    scaledCap = capFor

    labelled :: String -> Int -> String
    labelled name depth = "guess (" ++ name ++ " " ++ show depth ++ ")"

    depth01
        | hardcore >= 2 = 3250000
        | hardcore >= 1 = 40000
        | otherwise = 1100
    depth12
        | hardcore >= 2 = 3420000
        | hardcore >= 1 = 50000
        | otherwise = 1100
    depth13
        | hardcore >= 2 = 3460000
        | hardcore >= 1 = 40000
        | otherwise = 1100
    depth03
        | hardcore >= 2 = 19
        | otherwise = 12
    depth11
        | hardcore >= 2 = 14
        | otherwise = 9
    depth04
        | hardcore >= 2 = 152000
        | hardcore >= 1 = 2600
        | otherwise = 800
    depth05
        | hardcore >= 2 = 52000
        | hardcore >= 1 = 2600
        | otherwise = 800
    depth06
        | hardcore >= 2 = 146000
        | hardcore >= 1 = 2400
        | otherwise = 700
    stepped = AppR (VarR "step") (VarR "value")

-- The shapes.  Each takes its object-language pieces as arguments, so quoting one produces a term
-- whose free structure is fixed by the shape and nothing else.

nest01 :: Int -> (a -> Bool) -> a -> a -> a
nest01 n predicate pad value = go n
  where
    go 0 = value
    go k = if predicate (go $ k - 1) then value else pad

nest02 :: Int -> (a -> Bool) -> (a -> a) -> a -> a -> a
nest02 n predicate step pad value = go n value
  where
    go 0 _ = value
    go k x = if predicate x then go (k - 1) (step x) else pad

nest03 :: Int -> (a -> Bool) -> (a -> a) -> a -> a -> a
nest03 n predicate step _pad value = go n value
  where
    go 0 x = x
    go k x = if predicate x then go (k - 1) (step x) else go (k - 1) (step (step x))

nest04 :: Int -> (a -> Bool) -> a -> a -> a
nest04 n predicate pad value = go n
  where
    go 0 = value
    go k =
        if predicate pad
            then go $ k - 1
            else pad

nest05 :: Int -> (a -> Bool) -> a -> a -> a
nest05 n predicate pad value = go n
  where
    go 0 = value
    go k =
        if predicate (if even k then pad else value)
            then go $ k - 1
            else pad

nest06 :: Int -> (a -> Bool) -> a -> a -> a
nest06 n predicate pad value = go n
  where
    go 0 = value
    go k =
        let y = predicate pad
         in if y
                then
                    if y
                        then go $ k - 1
                        else pad
                else pad

nest07 :: (a -> Bool) -> a -> a -> a
nest07 predicate value pad =
    let y = predicate value
     in if y then (if y then value else pad) else pad

nest08 :: (a -> Bool) -> a -> a -> a
nest08 predicate value pad =
    let y = predicate value
     in if y then value else (if y then value else pad)

nest09 :: (a -> a) -> (a -> Bool) -> a -> a -> a
nest09 step predicate value pad =
    let v = step value
        y = predicate v
     in if y then (if y then v else pad) else (if y then pad else v)

nest10 :: (a -> a) -> (a -> a -> Bool) -> a -> a
nest10 step combine value =
    let y = step value
     in if combine y y then y else value

nest11 :: Int -> (a -> Bool) -> (a -> a -> a) -> a -> a -> a
nest11 n predicate combine pad value = go n
  where
    go 0 = value
    go k =
        let y = go $ k - 1
         in if predicate y then combine y y else pad

nest12 :: Int -> (Bool -> Bool) -> Bool -> Bool
nest12 n predicate value = go n
  where
    go 0 = value
    go k = if predicate (go $ k - 1) then True else False

nest13 :: Int -> (Bool -> Bool) -> Bool -> Bool
nest13 n predicate value = go n
  where
    go 0 = value
    go k = if predicate (go $ k - 1) then False else True

-- The answers.

expectedNest01 :: Int -> ExprR
expectedNest01 n = lams ["predicate", "pad", "value"] $ go n
  where
    go 0 = VarR "value"
    go k = IteR (AppR (VarR "predicate") (go $ k - 1)) (VarR "value") (VarR "pad")

expectedNest02 :: Int -> ExprR
expectedNest02 n = lams ["predicate", "step", "pad", "value"] $ go n (VarR "value")
  where
    go 0 _ = VarR "value"
    go k x =
        IteR
            (AppR (VarR "predicate") x)
            (go (k - 1) (AppR (VarR "step") x))
            (VarR "pad")

expectedNest04 :: Int -> ExprR
expectedNest04 n = lams ["predicate", "pad", "value"] $ go n
  where
    go 0 = VarR "value"
    go k = IteR (AppR (VarR "predicate") (VarR "pad")) (go $ k - 1) (VarR "pad")

expectedNest05 :: Int -> ExprR
expectedNest05 n = lams ["predicate", "pad", "value"] $ go n
  where
    go 0 = VarR "value"
    go k =
        IteR
            (AppR (VarR "predicate") (VarR $ if even k then "pad" else "value"))
            (go $ k - 1)
            (VarR "pad")

expectedNest03 :: Int -> ExprR
expectedNest03 n = lams ["predicate", "step", "pad", "value"] $ go n (VarR "value")
  where
    step = AppR (VarR "step")
    go 0 x = x
    go k x =
        IteR
            (AppR (VarR "predicate") x)
            (go (k - 1) (step x))
            (go (k - 1) (step (step x)))

expectedNest11 :: Int -> ExprR
expectedNest11 n = lams ["predicate", "combine", "pad", "value"] $ go n
  where
    go 0 = VarR "value"
    go k =
        let y = go $ k - 1
         in IteR (AppR (VarR "predicate") y) (AppR (AppR (VarR "combine") y) y) (VarR "pad")

expectedNest12 :: Int -> ExprR
expectedNest12 n = lams ["predicate", "value"] $ go n
  where
    go 0 = VarR "value"
    go k = AppR (VarR "predicate") (go $ k - 1)

expectedNest13 :: Int -> ExprR
expectedNest13 n = lams ["predicate", "value"] $ go n
  where
    go 0 = VarR "value"
    go k = IteR (AppR (VarR "predicate") (go $ k - 1)) (ValR False) (ValR True)

lams :: [String] -> ExprR -> ExprR
lams names body = foldr LamR body names

quotesWithin :: Int -> String -> ExprR -> ExprR -> Assertion
quotesWithin timeoutMicros label expected actual = do
    completed <- Timeout.timeout timeoutMicros . evaluate $ forceExprR actual
    case completed of
        Nothing ->
            assertFailure $
                label
                    ++ " did not finish within "
                    ++ show timeoutMicros
                    ++ " microseconds"
        Just () ->
            if alphaEtaEquivalent actual expected
                then pure ()
                else assertFailure $ label ++ " quoted to " ++ show actual

quotes :: String -> ExprR -> ExprR -> Assertion
quotes = quotesWithin $ capFor 0.01
