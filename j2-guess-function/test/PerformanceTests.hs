{-# OPTIONS_GHC -O0 #-}

-- The widest function type below has more arguments than GHC's default reduction depth allows a
-- structural traversal of the type to take.  The limit is about how far GHC is willing to go, not
-- about whether the traversal terminates, so it is lifted rather than raised to a guess.
{-# OPTIONS_GHC -freduction-depth=0 #-}

{-# LANGUAGE GADTs #-}

module PerformanceTests
    ( performanceTests
    , capFor
    , forceExprR
    ) where

import           Control.Concurrent
    ( forkFinally
    , killThread
    , newEmptyMVar
    , putMVar
    , takeMVar
    )
import           Control.Exception (evaluate)
import           Control.Monad (forM)
import           Lib (guess)
import           ExprREq (alphaEtaEquivalent)
import           Lib.ExprR (ExprR(..))
import           System.Timeout (timeout)
import           Test.Tasty (TestTree, localOption, testGroup)
import           Test.Tasty.HUnit
    ( Assertion
    , assertBool
    , assertFailure
    , testCase
    , (@?=)
    )
import           Test.Tasty.Runners (NumThreads(..))

performanceTests :: Int -> TestTree
performanceTests hardcore =
    localOption (NumThreads 1) $
        testGroup
            "performance regressions"
            [ testCase
                "shape01 500000"
                $ assertMatchesWithin
                    (capFor 0.39)
                    "guess (shape01 500000)"
                    (matches01 500000)
                    (guess $ shape01 500000)
            , testCase
                "shape02 parallel"
                $ assertParallelWithin (capFor 0.12) 8 40000
            , testCase
                "shape08 26 1000"
                $ assertMatchesWithin (capFor 0.15)
                    "guess (shape08 26 1000)"
                    (matches08 26 1000)
                    (guess $ shape08 26 1000)
            , testCase
                "shape09 80 1000"
                $ assertMatchesWithin (capFor 0.34)
                    "guess (shape09 80 1000)"
                    (matches09 80 1000)
                    (guess $ shape09 80 1000)
            , testCase
                "shape10 50 600"
                $ assertMatchesWithin (capFor 0.32)
                    "guess (shape10 50 600)"
                    (matches10 50 600)
                    (guess $ shape10 50 600)
            , testCase
                "shape11 100000"
                $ assertMatchesWithin (capFor 0.42)
                    "guess (shape11 100000)"
                    (matches11 100000)
                    (guess $ shape11 100000)
            , testCase
                "shape12 100000"
                $ assertShape12Within (capFor 0.23) 100000
                    (guess $ shape12 100000)
            , testCase
                "shape02 300000"
                $ assertQuotesWithin (capFor 0.50)
                    "guess (shape02 300000)"
                    (expected02 300000)
                    (guess $ shape02 300000)
            , testCase
                "shape03"
                $ assertQuotesWithin (capFor 1.05)
                    "guess shape03"
                    (expected03)
                    (guess shape03)
            , testCase
                "shape04 50 175000"
                $ assertQuotesWithin (capFor 0.73)
                    "guess shape04"
                    (expected04 50)
                    (guess $ shape04 50 175000)
            , testCase
                "shape05 600"
                $ assertQuotesWithin (capFor 0.31)
                    "guess (shape05 600)"
                    (expected05 False 600)
                    (guess $ shape05 600)
            , testCase
                "shape06 130000"
                $ assertQuotesWithin (capFor 0.40)
                    "guess (shape06 130000)"
                    (expected06 130000)
                    (guess $ shape06 130000)
            , testCase
                "shape13 500"
                $ assertQuotesWithin (capFor 0.34)
                    "guess (shape13 500)"
                    (expected05 False 500)
                    (guess $ shape13 500)
            , testCase
                "shape07 130000"
                $ assertQuotesWithin (capFor 0.37)
                    "guess (shape07 130000)"
                    (expected07 130000)
                    (guess $ shape07 130000)
            , testCase
                "shape16"
                $ assertQuotesWithin (capFor 0.37)
                    (labelled "shape16" depth16)
                    (expected16 depth16)
                    (guess $ shape16 depth16)
            , testCase
                "shape17"
                $ assertQuotesWithin (capFor 0.13)
                    (labelled "shape17" depth17)
                    (expected17 depth17)
                    (guess $ shape17 depth17)
            , testCase
                "shape18"
                $ assertQuotesWithin (capFor 0.33)
                    (labelled "shape18" depth18)
                    (expected18 depth18)
                    (guess $ shape18 depth18)
            , testCase
                "shape01 250000"
                $ assertQuotesWithin (capFor 0.14)
                    "guess (shape01 250000)"
                    (expected01 250000)
                    (guess $ shape01 250000)
            , testCase "closed forms" $ do
                sizeExprR (expected16 1000) @?= 7 * 1000 + 4
                sizeExprR (expected17 1000) @?= 8 * 1000 + 5
                sizeExprR (expected18 1000) @?= 13 * 1000 + 5
                sizeExprR expected03 @?= 5 * 500 + 4
                sizeExprR (expected04 50) @?= 9 * 50 + 4
                sizeExprR (expected02 300000) @?= 2 * 300000 + 7
                sizeExprR (expected06 130000) @?= 4 * 130000 + 8
                sizeExprR (expected07 130000) @?= 4 * 130000 + 8
                sizeExprR (expected05 False 500) @?= 162 * 500 + 7
                sizeExprR (expected05 True 550) @?= 162 * 550 + 10
            , testCase
                "shape14 550"
                $ assertQuotesWithin (capFor 0.50)
                    "guess (shape14 550)"
                    (expected05 True 550)
                    (guess $ shape14 550)
            , testCase
                "shape15 250"
                $ assertQuotesWithin (capFor 0.46)
                    "guess (shape15 250)"
                    (expected05Arity 320 True 250)
                    (guess $ shape15 250)
            , testGroup
                "grouped shapes"
                [ testCase
                    "shape19"
                    $ assertQuotesWithin (groupCap 0.17)
                        (labelled "shape19" depth19)
                        (expected19 depth19)
                        (guess $ shape19 depth19)
                , testCase
                    "shape20"
                    $ assertQuotesWithin (groupCap 0.20)
                        (labelled "shape20" depth20)
                        (expected20 depth20)
                        (guess $ shape20 depth20)
                , testCase
                    "shape21"
                    $ assertQuotesWithin (groupCap 0.23)
                        (labelled "shape21" depth21)
                        (expected21 depth21)
                        (guess $ shape21 depth21)
                , testCase
                    "shape22"
                    $ assertQuotesWithin (groupCap 0.20)
                        (labelled "shape22" depth22)
                        (expected22 depth22)
                        (guess $ shape22 depth22)
                , testCase
                    "shape23"
                    $ assertQuotesWithin (groupCap 0.20)
                        (labelled "shape23" depth23)
                        (expected23 depth23)
                        (guess $ shape23 depth23)
                , testCase
                    "shape24"
                    $ assertQuotesWithin (groupCap 0.29)
                        (labelled "shape24" depth24)
                        (expected24 depth24)
                        (guess $ shape24 depth24)
                , testCase
                    "shape25"
                    $ assertQuotesWithin (groupCap 0.30)
                        (labelled "shape25" depth25)
                        (expected25 depth25)
                        (guess $ shape25 depth25)
                , testCase "closed forms (grouped)" $ do
                    sizeExprR (expected19 1000) @?= 9 * 1000 + 5
                    sizeExprR (expected20 1000) @?= 7 * 1000 + 5
                    sizeExprR (expected21 1000) @?= 7 * 1000 + 5
                    sizeExprR (expected22 1000) @?= 29 * 1000 + 5
                    sizeExprR (expected23 1000) @?= 21 * 1000 + 5
                    sizeExprR (expected24 1000) @?= 7 * 1000 + 5
                    sizeExprR (expected25 1000) @?= 11 * 1000 + 5
                ]
            , testCase
                "shape26"
                $ assertMatchesWithin (capFor 1.05)
                    ("guess (shape26 "
                        ++ show depth26
                        ++ " "
                        ++ show size26
                        ++ ")")
                    (matches26 depth26 size26)
                    (guess $ shape26 depth26 size26)
            ]
  where
    labelled :: String -> Int -> String
    labelled name depth = "guess (" ++ name ++ " " ++ show depth ++ ")"

    groupCap :: Double -> Int
    groupCap = capFor

    scaledDepth :: Int -> Int -> Int
    scaledDepth hardcoreDepth widerDepth
        | hardcore >= 2 = widerDepth
        | hardcore >= 1 = hardcoreDepth
        | otherwise = 900

    depth26 = 2000
    size26 = 1700000

    -- Raised only at the widest setting, where seven nodes a level is what the budget is buying.
    depth16
        | hardcore >= 2 = 4450000
        | otherwise = 1000

    depth17
        | hardcore >= 2 = 48000
        | hardcore >= 1 = 2000
        | otherwise = 700

    depth18
        | hardcore >= 2 = 110000
        | hardcore >= 1 = 800
        | otherwise = 300

    depth19 = scaledDepth 30000 1890000
    depth20 = scaledDepth 30000 2470000
    depth21 = scaledDepth 30000 2680000
    depth22 = scaledDepth 24000 1610000
    depth23 = scaledDepth 26000 1890000
    depth24 = scaledDepth 27000 3250000
    depth25 = scaledDepth 24000 3380000

capFor :: Integral a => Double -> a
capFor referenceSeconds =
    max 2000000 . round $ referenceSeconds * 17 * 1000000

forceExprR :: ExprR -> ()
forceExprR expr =
    case expr of
        ValR _ ->
            ()
        VarR name ->
            forceName name
        AppR fun arg ->
            forceExprR fun `seq` forceExprR arg
        LamR name body ->
            forceName name `seq` forceExprR body
        IteR cond yes no ->
            forceExprR cond `seq` forceExprR yes `seq` forceExprR no

forceName :: String -> ()
forceName =
    foldr seq ()

quotedWithin :: Int -> String -> ExprR -> (ExprR -> Assertion) -> Assertion
quotedWithin timeoutMicros label actual check = do
    quoted <- timeout timeoutMicros $ evaluate $ forceExprR actual
    case quoted of
        Nothing ->
            assertFailure $
                label
                    ++ " did not finish within "
                    ++ show timeoutMicros
                    ++ " microseconds"
        Just () ->
            check actual

assertQuotesWithin :: Int -> String -> ExprR -> ExprR -> Assertion
assertQuotesWithin timeoutMicros label expected actual =
    quotedWithin timeoutMicros label actual $ \quoted ->
        assertBool
            (label ++ " did not quote to the expected AST")
            (alphaEtaEquivalent quoted expected)

assertMatchesWithin
    :: Int
    -> String
    -> (ExprR -> Bool)
    -> ExprR
    -> Assertion
assertMatchesWithin timeoutMicros label matches actual =
    quotedWithin timeoutMicros label actual $ \quoted ->
        assertBool (label ++ " did not quote to the expected AST") (matches quoted)

assertParallelWithin :: Int -> Int -> Int -> Assertion
assertParallelWithin timeoutMicros workerCount nominalDepth = do
    workers <- forM (take workerCount [0 ..]) $ \phase -> do
        result <- newEmptyMVar
        thread <- forkFinally
            (do
                expr <- evaluate $ guess $
                    shape02 (nominalDepth + phase * 37)
                pure $
                    case expr of
                        LamR _ _ -> True
                        _ -> False
            )
            (putMVar result)
        pure (thread, result)
    completed <- timeout timeoutMicros $
        mapM (takeMVar . snd) workers
    case completed of
        Nothing -> do
            mapM_ (killThread . fst) workers
            assertFailure $
                "parallel guesses did not finish within "
                    ++ show timeoutMicros
                    ++ " microseconds"
        Just outcomes ->
            case sequence outcomes of
                Left failure ->
                    assertFailure $
                        "parallel guess failed: " ++ show failure
                Right roots ->
                    assertBool
                        "parallel guesses returned malformed roots"
                        (and roots)

assertShape12Within :: Int -> Int -> ExprR -> Assertion
assertShape12Within timeoutMicros linkDepth actual =
    quotedWithin
        timeoutMicros
        ("guess (shape12 " ++ show linkDepth ++ ")")
        actual
        $ \quoted ->
            assertBool
                "guess shape12 did not quote to the expected AST"
                (matches12 linkDepth quoted)

sizeExprR :: ExprR -> Int
sizeExprR expr =
    case expr of
        ValR _ ->
            1
        VarR _ ->
            1
        AppR fun arg ->
            1 + sizeExprR fun + sizeExprR arg
        LamR _ body ->
            1 + sizeExprR body
        IteR condition yes no ->
            1
                + sizeExprR condition
                + sizeExprR yes
                + sizeExprR no

shape01 :: Int -> (a -> a) -> a -> a
shape01 0 _ value = value
shape01 n fun value =
    fun $ shape01 (n - 1) fun value

shape02 :: Int -> (a -> a) -> Bool -> a -> a
shape02 n fun condition value =
    shape01 n fun $
        if condition
            then value
            else value

slowIdentity :: Int -> a -> a
slowIdentity 0 value = value
slowIdentity n value =
    slowIdentity (n - 1) value

shape03 :: (a -> Bool) -> a -> b -> b
shape03 predicate input final = go (500 :: Int)
  where
    go 0 = final
    go n =
        if predicate $ slowIdentity 600000 input
            then go $ n - 1
            else final

burn :: Int -> Bool -> Bool
burn 0 value = value
burn depth value =
    burn (depth - 1) $ not value
{-# NOINLINE burn #-}

shape04
    :: Int
    -> Int
    -> (Bool -> Bool -> Bool)
    -> (a -> Bool)
    -> a
    -> Bool
shape04 length' burnDepth combine predicate value =
    go length'
  where
    go 0 = False
    go n =
        combine
            (burn burnDepth True)
            ( if predicate value
                then go $ n - 1
                else False
            )

type Arguments8 a result =
    a -> a -> a -> a -> a -> a -> a -> a -> result

type Arguments80 a result =
    Arguments8 a
        (Arguments8 a
            (Arguments8 a
                (Arguments8 a
                    (Arguments8 a
                        (Arguments8 a
                            (Arguments8 a
                                (Arguments8 a
                                    (Arguments8 a
                                        (Arguments8 a result)
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )

type WideBoolFunction a =
    Arguments80 a (Bool -> Bool)

apply80 :: Arguments80 a result -> a -> result
apply80 fun value =
    fun
        value value value value value value value value
        value value value value value value value value
        value value value value value value value value
        value value value value value value value value
        value value value value value value value value
        value value value value value value value value
        value value value value value value value value
        value value value value value value value value
        value value value value value value value value
        value value value value value value value value

shape05
    :: Int
    -> WideBoolFunction a
    -> a
    -> (a -> Bool)
    -> a
    -> Bool
shape05 width combine repeated predicate value =
    go width
  where
    go 0 =
        predicate value
    go remaining =
        apply80 combine repeated $
            go $ remaining - 1

spinePadded :: Int -> (a -> a -> a) -> a -> a -> a
spinePadded 0 _ _ value = value
spinePadded n fun pad value =
    fun (spinePadded (n - 1) fun pad value) pad

shape06 :: Int -> (a -> a -> a) -> a -> Bool -> a -> a
shape06 n fun pad condition value =
    spinePadded n fun pad $
        if condition
            then value
            else value

shape07 :: Int -> (a -> a -> a) -> a -> Bool -> a -> a
shape07 n fun pad condition value = go n
  where
    go 0 =
        if condition
            then value
            else value
    go k
        | even k = fun (go (k - 1)) pad
        | otherwise = fun pad (go (k - 1))

shape08
    :: Int
    -> Int
    -> (a -> a -> a)
    -> Arguments8 a a
    -> (a -> Bool)
    -> a
    -> a
    -> a
shape08 leafCount linkDepth join fun predicate pad value =
    balancedApply join
        [ link phase (scheduledDepth linkDepth phase)
        | phase <- take leafCount [0 ..]
        ]
  where
    link _ 0 =
        if predicate pad
            then value
            else value
    link phase n =
        applyAt8 ((n + phase) `mod` 8) fun (link phase (n - 1)) pad

applyAt8 :: Int -> Arguments8 a a -> a -> a -> a
applyAt8 position fun nested pad =
    case position of
        0 -> fun nested pad pad pad pad pad pad pad
        1 -> fun pad nested pad pad pad pad pad pad
        2 -> fun pad pad nested pad pad pad pad pad
        3 -> fun pad pad pad nested pad pad pad pad
        4 -> fun pad pad pad pad nested pad pad pad
        5 -> fun pad pad pad pad pad nested pad pad
        6 -> fun pad pad pad pad pad pad nested pad
        _ -> fun pad pad pad pad pad pad pad nested

shape09
    :: Int
    -> Int
    -> (a -> a -> a)
    -> (a -> a -> a)
    -> (a -> a -> Bool)
    -> a
    -> a
    -> a
shape09 leafCount linkDepth join wrap decide pad value =
    balancedApply join
        [ link phase (scheduledDepth linkDepth phase)
        | phase <- take leafCount [0 ..]
        ]
  where
    link phase 0 = shape16 (innerDepth phase) decide pad value
    link phase n
        | even (n + phase) = wrap (link phase (n - 1)) pad
        | otherwise = wrap pad (link phase (n - 1))

scheduledDepth :: Int -> Int -> Int
scheduledDepth nominal phase =
    nominal + (phase * 37 `mod` 101) - 50

innerDepth :: Int -> Int
innerDepth phase = 3 + (phase * 5 `mod` 4)

shape10
    :: Int
    -> Int
    -> (a -> a)
    -> (a -> a -> a)
    -> (a -> a -> Bool)
    -> a
    -> a
    -> a
shape10 branchDepth linkDepth step turn decide pad value =
    branch branchDepth
  where
    branch 0 = value
    branch edge
        | even edge =
            if decide nested pad then value else pad
        | otherwise =
            if decide pad nested then pad else value
      where
        nested = link edge linkDepth $ branch (edge - 1)

    link _ 0 body = body
    link edge remaining body
        | remaining `mod` 11 == 0 && even (remaining + edge) =
            turn recursive pad
        | remaining `mod` 11 == 0 =
            turn pad recursive
        | otherwise = step recursive
      where
        recursive = link edge (remaining - 1) body

shape11
    :: Int
    -> (a -> a)
    -> (a -> a -> Bool)
    -> a
    -> a
    -> a
shape11 linkDepth wrap decide pad value = branch (3 :: Int)
  where
    branch 0 = value
    branch n =
        if decide (link linkDepth $ branch (n - 1)) pad
            then value
            else pad

    link 0 body = body
    link n body = wrap $ link (n - 1) body

shape12
    :: Int
    -> (a -> a)
    -> (a -> a -> a)
    -> (a -> a -> Bool)
    -> a
    -> a
    -> a
shape12 nominalDepth step turn decide pad value =
    branch (3 :: Int)
  where
    branch 0 = value
    branch edge
        | even edge =
            if decide nested pad then value else pad
        | otherwise =
            if decide pad nested then pad else value
      where
        depth = depth12 nominalDepth edge
        nested =
            link edge depth (initialTurn edge depth) (even edge) $
                branch $ edge - 1

    link _ 0 _ _ body = body
    link edge remaining untilTurn turnLeft body
        | untilTurn == 0 =
            if turnLeft
                then turn recursive pad
                else turn pad recursive
        | otherwise = step recursive
      where
        (nextTurn, nextSide)
            | untilTurn == 0 = (4092, not turnLeft)
            | otherwise = (untilTurn - 1, turnLeft)
        recursive =
            link edge (remaining - 1) nextTurn nextSide body

depth12 :: Int -> Int -> Int
depth12 nominal edge =
    if edge == 3
        then nominal + edge * 53 `mod` 127
        else 0

initialTurn :: Int -> Int -> Int
initialTurn edge depth =
    (depth + edge * 997) `mod` 4093

balancedApply :: (a -> a -> a) -> [a] -> a
balancedApply _ [] = error "balancedApply: empty input"
balancedApply _ [value] = value
balancedApply join values = balancedApply join $ pair values
  where
    pair (left : right : rest) = join left right : pair rest
    pair remaining = remaining

{-# NOINLINE wrapBool #-}
wrapBool :: a -> a
wrapBool value = value

apply80Distinct :: Arguments80 a result -> (a -> a) -> a -> result
apply80Distinct fun wrap value =
    fun
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)
        (wrap value) (wrap value) (wrap value) (wrap value)

shape13
    :: Int
    -> WideBoolFunction a
    -> a
    -> (a -> Bool)
    -> a
    -> Bool
shape13 width combine repeated predicate value =
    go width
  where
    go 0 =
        predicate value
    go remaining =
        apply80Distinct combine wrapBool repeated $
            go $ remaining - 1

type Arguments320 a result =
    Arguments80 a
        (Arguments80 a
            (Arguments80 a
                (Arguments80 a result)
            )
        )

apply320 :: Arguments320 a result -> a -> result
apply320 fun value =
    apply80 (apply80 (apply80 (apply80 fun value) value) value) value

shape15
    :: Int
    -> Arguments320 Bool (Bool -> Bool)
    -> Bool
    -> (Bool -> Bool)
    -> Bool
    -> Bool
shape15 width combine repeated predicate value =
    go width
  where
    go 0 =
        predicate value
    go remaining =
        apply320 combine repeated $
            if repeated
                then go $ remaining - 1
                else False

shape14
    :: Int
    -> WideBoolFunction Bool
    -> Bool
    -> (Bool -> Bool)
    -> Bool
    -> Bool
shape14 width combine repeated predicate value =
    go width
  where
    go 0 =
        predicate value
    go remaining =
        apply80 combine repeated $
            if repeated
                then go $ remaining - 1
                else False

shape16 :: Int -> (a -> a -> Bool) -> a -> a -> a
shape16 n fun pad value = go n
  where
    go 0 = value
    go k = if fun (go (k - 1)) pad then value else pad

shape17 :: Int -> (a -> Bool) -> (a -> a) -> a -> a -> a
shape17 n predicate wrap pad value = go n
  where
    go 0 = value
    go k
        | even k =
            if predicate pad
                then go $ k - 1
                else wrap pad
        | otherwise =
            if predicate (go $ k - 1)
                then wrap value
                else wrap pad

shape18
    :: Int
    -> (a -> Bool)
    -> (a -> a -> a -> a -> a)
    -> a
    -> a
    -> a
shape18 n predicate combine pad value = go n
  where
    go 0 = value
    go k =
        if predicate pad
            then combine pad (go $ k - 1) pad pad
            else pad

shape19 :: Int -> (a -> Bool) -> (a -> a) -> a -> a -> a
shape19 n predicate wrap pad value = go n
  where
    go 0 = value
    go k =
        if predicate (go $ k - 1)
            then wrap value
            else wrap pad

shape20 :: Int -> (a -> Bool) -> (a -> a) -> a -> a -> a
shape20 n predicate wrap pad value = go n
  where
    go 0 = value
    go k =
        if predicate (go $ k - 1)
            then wrap value
            else pad

shape21 :: Int -> (a -> Bool) -> (a -> a) -> a -> a -> a
shape21 n predicate wrap pad value = go n
  where
    go 0 = value
    go k =
        if predicate (go $ k - 1)
            then value
            else wrap pad

innerSpine :: Int -> (a -> a) -> a -> a
innerSpine 0 _ value = value
innerSpine depth wrap value =
    wrap $ innerSpine (depth - 1) wrap value

shape22 :: Int -> (a -> Bool) -> (a -> a) -> a -> a -> a
shape22 n predicate wrap pad value = go n
  where
    go 0 = value
    go k =
        if predicate (go $ k - 1)
            then innerSpine 6 wrap value
            else innerSpine 6 wrap pad

shape23
    :: Int
    -> (a -> Bool)
    -> (a -> a -> a -> a -> a)
    -> a
    -> a
    -> a
shape23 n predicate combine pad value = go n
  where
    go 0 = value
    go k =
        if predicate (go $ k - 1)
            then combine value pad value pad
            else combine pad value pad value

shape24 :: Int -> (a -> Bool) -> (a -> a) -> a -> a -> a
shape24 n predicate wrap pad value = go n
  where
    go 0 = value
    go k
        | even k =
            if predicate (go $ k - 1)
                then wrap value
                else pad
        | otherwise =
            if predicate (go $ k - 1)
                then value
                else wrap pad

shape25 :: Int -> (a -> a -> Bool) -> (a -> a) -> a -> a -> a
shape25 n predicate wrap pad value = go n
  where
    go 0 = value
    go k =
        if predicate (go $ k - 1) pad
            then wrap value
            else wrap pad

shape26 :: Int -> Int -> (a -> Bool) -> (a -> a) -> a -> a -> a
shape26 n bodySize predicate wrap pad value = go n
  where
    body = innerSpine bodySize wrap value
    go 0 = body
    go i =
        if predicate pad
            then go (i - 1)
            else pad

expected01 :: Int -> ExprR
expected01 n =
    lams ["fun", "value"] $ chain n
  where
    chain 0 = VarR "value"
    chain k = AppR (VarR "fun") $ chain (k - 1)

expected16 :: Int -> ExprR
expected16 n =
    lams ["fun", "pad", "value"] $ chain n
  where
    chain 0 = VarR "value"
    chain k =
        IteR
            (AppR (AppR (VarR "fun") (chain (k - 1))) (VarR "pad"))
            (VarR "value")
            (VarR "pad")

expected17 :: Int -> ExprR
expected17 n =
    lams ["predicate", "wrap", "pad", "value"] $ chain n
  where
    wrapped name = AppR (VarR "wrap") (VarR name)
    chain 0 = VarR "value"
    chain k
        | even k =
            IteR
                (AppR (VarR "predicate") (VarR "pad"))
                (chain (k - 1))
                (wrapped "pad")
        | otherwise =
            IteR
                (AppR (VarR "predicate") (chain (k - 1)))
                (wrapped "value")
                (wrapped "pad")

expected18 :: Int -> ExprR
expected18 n =
    lams ["predicate", "combine", "pad", "value"] $ chain n
  where
    chain 0 = VarR "value"
    chain k =
        IteR
            (AppR (VarR "predicate") (VarR "pad"))
            (AppR
                (AppR
                    (AppR (AppR (VarR "combine") (VarR "pad")) (chain (k - 1)))
                    (VarR "pad"))
                (VarR "pad"))
            (VarR "pad")

expected03 :: ExprR
expected03 =
    lams ["predicate", "input", "final"] $ chain (500 :: Int)
  where
    chain 0 = VarR "final"
    chain k =
        IteR (AppR (VarR "predicate") (VarR "input")) (chain (k - 1)) (VarR "final")

expected04 :: Int -> ExprR
expected04 n =
    lams ["combine", "predicate", "value"] $ chain n
  where
    chain 0 = ValR False
    chain k =
        AppR (AppR (VarR "combine") (ValR True)) $
            IteR (AppR (VarR "predicate") (VarR "value")) (chain (k - 1)) (ValR False)

expected02 :: Int -> ExprR
expected02 n =
    lams ["fun", "condition", "value"] $ chain n
  where
    chain 0 = IteR (VarR "condition") (VarR "value") (VarR "value")
    chain k = AppR (VarR "fun") $ chain (k - 1)

expected06 :: Int -> ExprR
expected06 n =
    lams ["fun", "pad", "condition", "value"] $ chain n
  where
    chain 0 = IteR (VarR "condition") (VarR "value") (VarR "value")
    chain k = AppR (AppR (VarR "fun") (chain (k - 1))) (VarR "pad")

expected07 :: Int -> ExprR
expected07 n =
    lams ["fun", "pad", "condition", "value"] $ chain n
  where
    chain 0 = IteR (VarR "condition") (VarR "value") (VarR "value")
    chain k
        | even k = AppR (AppR (VarR "fun") (chain (k - 1))) (VarR "pad")
        | otherwise = AppR (AppR (VarR "fun") (VarR "pad")) (chain (k - 1))

expected19 :: Int -> ExprR
expected19 n =
    lams ["predicate", "wrap", "pad", "value"] $ chain n
  where
    wrapped name = AppR (VarR "wrap") (VarR name)
    chain 0 = VarR "value"
    chain k =
        IteR
            (AppR (VarR "predicate") (chain (k - 1)))
            (wrapped "value")
            (wrapped "pad")

expected20 :: Int -> ExprR
expected20 n =
    lams ["predicate", "wrap", "pad", "value"] $ chain n
  where
    chain 0 = VarR "value"
    chain k =
        IteR
            (AppR (VarR "predicate") (chain (k - 1)))
            (AppR (VarR "wrap") (VarR "value"))
            (VarR "pad")

expected21 :: Int -> ExprR
expected21 n =
    lams ["predicate", "wrap", "pad", "value"] $ chain n
  where
    chain 0 = VarR "value"
    chain k =
        IteR
            (AppR (VarR "predicate") (chain (k - 1)))
            (VarR "value")
            (AppR (VarR "wrap") (VarR "pad"))

expected22 :: Int -> ExprR
expected22 n =
    lams ["predicate", "wrap", "pad", "value"] $ chain n
  where
    spine 0 name = VarR name
    spine depth name = AppR (VarR "wrap") (spine (depth - 1 :: Int) name)
    chain 0 = VarR "value"
    chain k =
        IteR
            (AppR (VarR "predicate") (chain (k - 1)))
            (spine 6 "value")
            (spine 6 "pad")

expected23 :: Int -> ExprR
expected23 n =
    lams ["predicate", "combine", "pad", "value"] $ chain n
  where
    applied = foldl (\fun name -> AppR fun (VarR name)) (VarR "combine")
    chain 0 = VarR "value"
    chain k =
        IteR
            (AppR (VarR "predicate") (chain (k - 1)))
            (applied ["value", "pad", "value", "pad"])
            (applied ["pad", "value", "pad", "value"])

expected24 :: Int -> ExprR
expected24 n =
    lams ["predicate", "wrap", "pad", "value"] $ chain n
  where
    chain 0 = VarR "value"
    chain k
        | even k =
            IteR
                (AppR (VarR "predicate") (chain (k - 1)))
                (AppR (VarR "wrap") (VarR "value"))
                (VarR "pad")
        | otherwise =
            IteR
                (AppR (VarR "predicate") (chain (k - 1)))
                (VarR "value")
                (AppR (VarR "wrap") (VarR "pad"))

expected25 :: Int -> ExprR
expected25 n =
    lams ["predicate", "wrap", "pad", "value"] $ chain n
  where
    wrapped name = AppR (VarR "wrap") (VarR name)
    chain 0 = VarR "value"
    chain k =
        IteR
            (AppR (AppR (VarR "predicate") (chain (k - 1))) (VarR "pad"))
            (wrapped "value")
            (wrapped "pad")

-- Checked by walking the answer rather than by building the shape it ought to be and comparing:
-- the fixture is sized so that the body is what the budget is about, and an equality test against
-- a term of the same size would put as much of that budget into the check as into the quotation.
matches26 :: Int -> Int -> ExprR -> Bool
matches26 n bodySize expr =
    case expr of
        LamR predicate (LamR wrap (LamR pad (LamR value body))) ->
            distinctNames [predicate, wrap, pad, value]
                && chain n predicate wrap pad value body
        _ ->
            False
  where
    chain 0 _ wrap _ value body =
        spine bodySize wrap value body
    chain remaining predicate wrap pad value body =
        case body of
            IteR (AppR (VarR fun) (VarR argument)) yes (VarR no) ->
                fun == predicate
                    && argument == pad
                    && no == pad
                    && chain (remaining - 1) predicate wrap pad value yes
            _ ->
                False

    spine 0 _ value body =
        body == VarR value
    spine remaining wrap value body =
        case body of
            AppR (VarR fun) nested ->
                fun == wrap && spine (remaining - 1) wrap value nested
            _ ->
                False

data BalancedPlan
    = PlanLeaf !Int
    | PlanJoin !BalancedPlan !BalancedPlan

balancedPlan :: Int -> BalancedPlan
balancedPlan leafCount = build $
    PlanLeaf <$> take leafCount [0 ..]
  where
    build [] = error "balancedPlan: empty input"
    build [link] = link
    build plans = build $ pair plans

    pair (left : right : rest) = PlanJoin left right : pair rest
    pair remaining = remaining

distinctNames :: [String] -> Bool
distinctNames [] = True
distinctNames (name : names) =
    name `notElem` names && distinctNames names

splitApplications :: Int -> ExprR -> Maybe (ExprR, [ExprR])
splitApplications count = go count []
  where
    go 0 arguments fun = Just (fun, arguments)
    go remaining arguments (AppR fun argument) =
        go (remaining - 1) (argument : arguments) fun
    go _ _ _ = Nothing

matches01 :: Int -> ExprR -> Bool
matches01 depth expr =
    case expr of
        LamR funName (LamR valueName body) ->
            funName /= valueName && chain funName valueName depth body
        _ -> False
  where
    chain _ valueName 0 current = current == VarR valueName
    chain funName valueName remaining current =
        case current of
            AppR (VarR name) nested ->
                name == funName
                    && chain funName valueName (remaining - 1) nested
            _ -> False

matches08 :: Int -> Int -> ExprR -> Bool
matches08 leafCount nominalDepth expr =
    case expr of
        LamR joinName
            (LamR funName
                (LamR predicateName
                    (LamR padName (LamR valueName body)))) ->
                distinctNames
                    [joinName, funName, predicateName, padName, valueName]
                    && matchesPlan
                        joinName funName predicateName padName valueName
                        (balancedPlan leafCount) body
        _ -> False
  where
    matchesPlan joinName funName predicateName padName valueName plan current =
        case plan of
            PlanLeaf phase ->
                link funName predicateName padName valueName phase
                    (scheduledDepth nominalDepth phase) current
            PlanJoin leftPlan rightPlan ->
                case current of
                    AppR (AppR (VarR name) left) right ->
                        name == joinName
                            && matchesPlan joinName funName predicateName
                                padName valueName leftPlan left
                            && matchesPlan joinName funName predicateName
                                padName valueName rightPlan right
                    _ -> False

    link funName predicateName padName valueName phase remaining current
        | remaining == 0 =
            case current of
                IteR
                    (AppR (VarR predicate) (VarR pad))
                    (VarR yes)
                    (VarR no) ->
                        predicate == predicateName
                            && pad == padName
                            && yes == valueName
                            && no == valueName
                _ -> False
        | otherwise =
            case splitApplications 8 current of
                Just (VarR name, arguments) ->
                    name == funName && matchArguments 0 arguments
                _ -> False
      where
        position = (remaining + phase) `mod` 8

        matchArguments _ [] = True
        matchArguments index (argument : arguments)
            | index == position =
                link funName predicateName padName valueName phase
                    (remaining - 1) argument
                    && matchArguments (index + 1) arguments
            | otherwise =
                argument == VarR padName
                    && matchArguments (index + 1) arguments

matches09 :: Int -> Int -> ExprR -> Bool
matches09 leafCount nominalDepth expr =
    case expr of
        LamR joinName
            (LamR wrapName
                (LamR decideName
                    (LamR padName (LamR valueName body)))) ->
                distinctNames
                    [joinName, wrapName, decideName, padName, valueName]
                    && matchesPlan
                        joinName wrapName decideName padName valueName
                        (balancedPlan leafCount) body
        _ -> False
  where
    matchesPlan joinName wrapName decideName padName valueName plan current =
        case plan of
            PlanLeaf phase ->
                link wrapName decideName padName valueName phase
                    (scheduledDepth nominalDepth phase) current
            PlanJoin leftPlan rightPlan ->
                case current of
                    AppR (AppR (VarR name) left) right ->
                        name == joinName
                            && matchesPlan joinName wrapName decideName
                                padName valueName leftPlan left
                            && matchesPlan joinName wrapName decideName
                                padName valueName rightPlan right
                    _ -> False

    link wrapName decideName padName valueName phase remaining current
        | remaining == 0 =
            branchCore decideName padName valueName
                (innerDepth phase) current
        | even (remaining + phase) =
            case current of
                AppR (AppR (VarR name) nested) (VarR pad) ->
                    name == wrapName
                        && pad == padName
                        && link wrapName decideName padName valueName phase
                            (remaining - 1) nested
                _ -> False
        | otherwise =
            case current of
                AppR (AppR (VarR name) (VarR pad)) nested ->
                    name == wrapName
                        && pad == padName
                        && link wrapName decideName padName valueName phase
                            (remaining - 1) nested
                _ -> False

    branchCore _ _ valueName 0 current = current == VarR valueName
    branchCore decideName padName valueName remaining current =
        case current of
            IteR
                (AppR (AppR (VarR decide) nested) (VarR conditionPad))
                (VarR yes)
                (VarR no) ->
                    decide == decideName
                        && conditionPad == padName
                        && yes == valueName
                        && no == padName
                        && branchCore decideName padName valueName
                            (remaining - 1) nested
            _ -> False

matches10 :: Int -> Int -> ExprR -> Bool
matches10 branchDepth linkDepth expr =
    case expr of
        LamR stepName
            (LamR turnName
                (LamR decideName
                    (LamR padName (LamR valueName body)))) ->
                distinctNames
                    [stepName, turnName, decideName, padName, valueName]
                    && branch stepName turnName decideName padName valueName
                        branchDepth body
        _ -> False
  where
    branch _ _ _ _ valueName 0 current = current == VarR valueName
    branch stepName turnName decideName padName valueName edge current =
        case current of
            IteR condition yes no ->
                correctLeaves padName valueName edge yes no
                    && case innerArgument decideName padName edge condition of
                        Just nested ->
                            link stepName turnName decideName padName valueName
                                edge linkDepth nested
                        Nothing -> False
            _ -> False

    link stepName turnName decideName padName valueName
            edge remaining current
        | remaining == 0 =
            branch stepName turnName decideName padName valueName
                (edge - 1) current
        | remaining `mod` 11 == 0 =
            case current of
                AppR (AppR (VarR name) nested) (VarR pad)
                    | even (remaining + edge)
                    , name == turnName
                    , pad == padName -> descend nested
                AppR (AppR (VarR name) (VarR pad)) nested
                    | odd (remaining + edge)
                    , name == turnName
                    , pad == padName -> descend nested
                _ -> False
        | otherwise =
            case current of
                AppR (VarR name) nested
                    | name == stepName -> descend nested
                _ -> False
      where
        descend =
            link stepName turnName decideName padName valueName
                edge (remaining - 1)

    correctLeaves padName valueName edge yes no
        | even edge =
            yes == VarR valueName && no == VarR padName
        | otherwise =
            yes == VarR padName && no == VarR valueName

    innerArgument decideName padName edge condition
        | even edge =
            case condition of
                AppR (AppR (VarR name) nested) (VarR pad)
                    | name == decideName
                    , pad == padName -> Just nested
                _ -> Nothing
        | otherwise =
            case condition of
                AppR (AppR (VarR name) (VarR pad)) nested
                    | name == decideName
                    , pad == padName -> Just nested
                _ -> Nothing

matches11 :: Int -> ExprR -> Bool
matches11 linkDepth expr =
    case expr of
        LamR wrapName
            (LamR decideName
                (LamR padName (LamR valueName body))) ->
                distinctNames [wrapName, decideName, padName, valueName]
                    && branch wrapName decideName padName valueName
                        (3 :: Int) body
        _ -> False
  where
    branch _ _ _ valueName 0 current = current == VarR valueName
    branch wrapName decideName padName valueName edge current =
        case current of
            IteR
                (AppR (AppR (VarR decide) nested) (VarR conditionPad))
                (VarR yes)
                (VarR no) ->
                    decide == decideName
                        && conditionPad == padName
                        && yes == valueName
                        && no == padName
                        && link wrapName decideName padName valueName
                            edge linkDepth nested
            _ -> False

    link wrapName decideName padName valueName edge remaining current
        | remaining == 0 =
            branch wrapName decideName padName valueName (edge - 1) current
        | otherwise =
            case current of
                AppR (VarR name) nested ->
                    name == wrapName
                        && link wrapName decideName padName valueName
                            edge (remaining - 1) nested
                _ -> False

-- Check the exact result without constructing and alpha-normalizing a second
-- 600000-node tree.  The oracle validates every sparse turn, argument side,
-- condition, branch leaf, binder, and ordinary unary edge in one pass.
matches12 :: Int -> ExprR -> Bool
matches12 nominalDepth expr =
    case expr of
        LamR stepName
            (LamR turnName
                (LamR decideName
                    (LamR padName (LamR valueName body)))) ->
                allDistinct
                    [stepName, turnName, decideName, padName, valueName]
                    && branch stepName turnName decideName padName valueName
                        3 body
        _ -> False
  where
    allDistinct [] = True
    allDistinct (name : names) =
        name `notElem` names && allDistinct names

    branch stepName turnName decideName padName valueName edge current
        | edge == 0 = current == VarR valueName
        | otherwise =
            case current of
                IteR condition yes no ->
                    correctLeaves yes no
                        && case innerArgument condition of
                            Just nested ->
                                link stepName turnName decideName
                                    padName valueName edge
                                    depth
                                    (initialTurn edge depth)
                                    (even edge)
                                    nested
                            Nothing -> False
                _ -> False
      where
        depth = depth12 nominalDepth edge

        correctLeaves yes no
            | even edge =
                yes == VarR valueName && no == VarR padName
            | otherwise =
                yes == VarR padName && no == VarR valueName

        innerArgument condition
            | even edge =
                case condition of
                    AppR (AppR (VarR name) nested) (VarR pad)
                        | name == decideName && pad == padName -> Just nested
                    _ -> Nothing
            | otherwise =
                case condition of
                    AppR (AppR (VarR name) (VarR pad)) nested
                        | name == decideName && pad == padName -> Just nested
                    _ -> Nothing

    link stepName turnName decideName padName valueName
            edge remaining untilTurn turnLeft current
        | remaining == 0 =
            branch stepName turnName decideName padName valueName
                (edge - 1) current
        | untilTurn == 0 =
            case current of
                AppR (AppR (VarR name) recursive) (VarR pad)
                    | turnLeft
                    , name == turnName
                    , pad == padName ->
                        descend 4092 (not turnLeft) recursive
                AppR (AppR (VarR name) (VarR pad)) recursive
                    | not turnLeft
                    , name == turnName
                    , pad == padName ->
                        descend 4092 (not turnLeft) recursive
                _ -> False
        | otherwise =
            case current of
                AppR (VarR name) recursive
                    | name == stepName ->
                        descend (untilTurn - 1) turnLeft recursive
                _ -> False
      where
        descend nextTurn nextSide =
            link stepName turnName decideName padName valueName
                edge (remaining - 1) nextTurn nextSide

expected05 :: Bool -> Int -> ExprR
expected05 =
    expected05Arity 80

expected05Arity :: Int -> Bool -> Int -> ExprR
expected05Arity arity forced width =
    lams ["combine", "repeated", "predicate", "value"] $ level width True
  where
    level 0 _ = AppR (VarR "predicate") (VarR "value")
    level k fresh =
        AppR (foldl AppR (VarR "combine") (replicate arity argument)) nested
      where
        argument
            | fresh = VarR "repeated"
            | otherwise = ValR True
        nested
            | forced && fresh = IteR (VarR "repeated") (level (k - 1) False) (ValR False)
            | otherwise = level (k - 1) (not forced && fresh)

lams :: [String] -> ExprR -> ExprR
lams names body = foldr LamR body names
