module StressTests
    ( stressTests
    ) where

import           Control.Concurrent
    ( forkIO
    , newEmptyMVar
    , putMVar
    , takeMVar
    )
import           Control.Exception
    ( SomeException
    , evaluate
    , mask_
    , throwIO
    , try
    )
import           Data.List (isInfixOf, nub)
import           System.IO.Unsafe (unsafePerformIO)
import qualified System.Timeout as Timeout
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.HUnit (assertBool, assertFailure, testCase)

import           Lib (guess)
import           ExprREq (alphaEtaEquivalent)
import           Lib.ExprR (ExprR(..), parseExprR)

stressTests :: TestTree
stressTests =
    testGroup
        "stress and robustness"
        [ testCase "forkIO inside a term can force its reflected Bool argument" $
            check
                (capFor 0.01)
                "forcing a reflected Bool argument on another thread"
                reflectedArgumentResult
        , testCase "reflected Bool result can be forced on another thread" $
            check
                (capFor 0.01)
                "forcing a reflected Bool result on another thread"
                reflectedResultResult
        , testCase "reflected application can be quoted on another thread" $
            check
                (capFor 0.01)
                "quoting a reflected application on another thread"
                reflectedApplicationResult
        , testCase "reflected application arguments are quoted interruptibly" $
            check
                (capFor 0.50)
                "quoting a reflected application argument uninterruptibly"
                maskedApplicationResult
        , testCase "discarded application does not force its argument" $
            check
                (capFor 0.01)
                "quoting a discarded application with a diverging argument"
                discardedDivergenceResult
        , testCase "quoting several terms at once agrees with quoting them in turn" $ do
            outcome <- Timeout.timeout (capFor 0.16) concurrentQuotesResult
            case outcome of
                Nothing ->
                    assertFailure "quoting several terms at once timed out"
                Just False ->
                    assertFailure "quoting several terms at once disagreed with quoting in turn"
                Just True ->
                    pure ()
        , testCase "one quotation forced from several threads agrees with itself" $ do
            outcome <- Timeout.timeout (capFor 0.13) sharedQuoteResult
            case outcome of
                Nothing ->
                    assertFailure "forcing one quotation from several threads timed out"
                Just False ->
                    assertFailure "forcing one quotation from several threads disagreed"
                Just True ->
                    pure ()
        , testCase "an unusable condition is not silently swallowed" $ do
            outcome <-
                try . evaluate . length . show $
                    guess $ \fun value ->
                        if fun (error "boom" `asTypeOf` value)
                            then value
                            else value
            case outcome of
                Left err
                    | "boom" `isInfixOf` show (err :: SomeException) -> pure ()
                    | otherwise ->
                        assertFailure $ "quoting failed for the wrong reason: " ++ show err
                Right _ ->
                    assertFailure
                        "quoting an if whose condition cannot be materialized succeeded anyway"
        , testCase "an argument taking many arguments gets distinct binders" $
            quotesAs
                (guess $ \fun ->
                    fun $ \a b c d e ->
                        if a
                            then b
                            else if c then d else e)
                "\\fun -> fun (\\a b c d e -> if a then b else if c then d else e)"
        , testCase "arguments nested three arrows deep get distinct binders" $
            quotesAs
                (guess $ \fun -> fun $ \g -> g $ \h -> h True)
                "\\fun -> fun (\\g -> g (\\h -> h True))"
        , testCase "a term with no binders at all" $
            quotesAs (guess True) "True"
        , testCase "a term whose condition is already known" $
            quotesAs (guess $ if True then False else True) "False"
        , testCase "a term that is nothing but its argument" $
            quotesAs (guess $ \fun -> (fun :: Bool -> Bool)) "\\fun x -> fun x"
        , testCase "a thunk shared between two unknown functions, forced by neither" $
            quotesAs
                (guess $ \f g h x -> let y = f x in g y (h y))
                "\\f g h x -> g (f x) (h (f x))"
        , testCase "a binder survives an earlier sibling that binds too" $
            quotesClosedAs
                (guess $ \f g p -> f (\a -> a) (\c -> g c (if p c then True else False)))
                "\\f g p -> f (\\a -> a) (\\c -> g c (p c))"
        , testCase "an earlier sibling that binds does not divert a later binder" $
            quotesClosedAs
                (guess $ \f g p ->
                    f (\a -> a) (\c d -> g (g c d) (if p c then True else False)))
                "\\f g p -> f (\\a -> a) (\\c d -> g (g c d) (p c))"
        , testCase "an argument quoted before a condition keeps its own binder" $
            quotesClosedAs
                (guess $ \f h p -> f h (\c -> if p c then h c else h c))
                "\\f h p -> f h (\\c -> if p c then h c else h c)"
        , testCase "quoting the same term twice agrees with itself" $
            check
                (capFor 0.01)
                "quoting one term twice"
                (alphaEtaEquivalent (quoteWith 1 sampleTerm) (quoteWith 2 sampleTerm))
        , testCase "a distinct argument at every level" $
            quotesWithinAs (capFor 0.04) (guess $ distinctPerLevel 40) $ renderDistinct 40
        , testCase "a condition repeated at every level" $
            check
                (capFor 0.12)
                "the repeated-condition stress case"
                stressResult
        ]

stressBigConditionDepth :: Int
stressBigConditionDepth = 14

stressBranchDepth :: Int
stressBranchDepth = 12

capFor :: Double -> Int
capFor referenceSeconds =
    max 2000000 . round $ referenceSeconds * 17 * 1000000

check :: Int -> String -> Bool -> IO ()
check timeoutMicros label result = do
    completed <- Timeout.timeout timeoutMicros $ evaluate result
    case completed of
        Nothing ->
            assertFailure $ label ++ " timed out"
        Just False ->
            assertFailure $ label ++ " produced the wrong AST"
        Just True ->
            pure ()

{-# NOINLINE quoteWith #-}
quoteWith :: Int -> ((Bool -> Bool) -> Bool -> Bool) -> ExprR
quoteWith _ = guess

sampleTerm :: (Bool -> Bool) -> Bool -> Bool
sampleTerm f x = if f x then f True else x

quotesClosedAs :: ExprR -> String -> IO ()
quotesClosedAs actual expectedSource = do
    case nub $ freeNames [] actual of
        [] ->
            pure ()
        free ->
            assertFailure $
                "quoted to a term with nothing binding "
                    ++ unwords free
                    ++ ": "
                    ++ show actual
    quotesAs actual expectedSource

freeNames :: [String] -> ExprR -> [String]
freeNames bound expr =
    case expr of
        ValR _ ->
            []
        VarR name
            | name `elem` bound -> []
            | otherwise -> [name]
        AppR fun argument ->
            freeNames bound fun ++ freeNames bound argument
        LamR name body ->
            freeNames (name : bound) body
        IteR cond yes no ->
            freeNames bound cond ++ freeNames bound yes ++ freeNames bound no

-- Like 'quotesAs', with a budget.  The cases which spell their expectation out in full are about
-- the shape of the answer and take no measurable time to reach; the ones whose expectation is
-- generated are about how the cost of reaching it grows, and those get a cap here rather than
-- being left to the whole-suite timeout, which would report them as the suite dying instead of as
-- this case being slow.
quotesWithinAs :: Int -> ExprR -> String -> IO ()
quotesWithinAs timeoutMicros actual expectedSource =
    case parseExprR expectedSource of
        Left err -> assertFailure $ "could not parse the expectation: " ++ err
        Right expected -> do
            completed <-
                Timeout.timeout timeoutMicros . evaluate $
                    alphaEtaEquivalent actual expected
            case completed of
                Nothing ->
                    assertFailure $
                        "quoting did not finish within "
                            ++ show timeoutMicros
                            ++ " microseconds"
                Just False ->
                    assertFailure $
                        "quoted to " ++ show actual ++ " rather than " ++ show expected
                Just True ->
                    pure ()

quotesAs :: ExprR -> String -> IO ()
quotesAs actual expectedSource =
    case parseExprR expectedSource of
        Left err -> assertFailure $ "could not parse the expectation: " ++ err
        Right expected ->
            assertBool
                ("quoted to " ++ show actual ++ " rather than " ++ show expected)
                (alphaEtaEquivalent actual expected)

distinctPerLevel :: Int -> (Bool -> Bool -> Bool) -> (Bool -> Bool) -> Bool -> Bool
distinctPerLevel n fun g value = go n value
  where
    go 0 acc = acc
    go k acc = fun (go (k - 1) (g acc)) acc

renderDistinct :: Int -> String
renderDistinct n =
    "\\fun g value -> " ++ chain n (0 :: Int)
  where
    chain 0 d = wrapped d
    chain k d = "(fun " ++ chain (k - 1) (d + 1) ++ " " ++ wrapped d ++ ")"
    wrapped 0 = "value"
    wrapped d = "(g " ++ wrapped (d - 1) ++ ")"

chainTerm :: Int -> (Bool -> Bool) -> Bool -> Bool
chainTerm n fun value = go n
  where
    go 0 = value
    go k = fun $ go (k - 1)

-- Compares the ASTs themselves: rendering them would measure the pretty printer instead.
quoteChain :: Int -> IO ExprR
quoteChain = evaluate . guess . chainTerm

inParallel :: [IO ExprR] -> IO [Maybe ExprR]
inParallel actions =
    mapM start actions >>= mapM takeMVar
  where
    start action = do
        slot <- newEmptyMVar
        _ <- forkIO $ do
            outcome <- try action
            putMVar slot $ either (\err -> (err :: SomeException) `seq` Nothing) Just outcome
        pure slot

concurrentQuotesResult :: IO Bool
concurrentQuotesResult = do
    let sizes = [200, 210, 220, 230, 240, 250]
    sequential <- mapM quoteChain sizes
    parallel <- inParallel $ map quoteChain sizes
    pure $ parallel == map Just sequential

sharedQuoteResult :: IO Bool
sharedQuoteResult = do
    let shared = guess $ chainTerm 600
        force' = evaluate shared
    parallel <- inParallel $ replicate 6 force'
    expected <- force'
    pure $ parallel == replicate 6 (Just expected)

reflectedArgumentResult :: Bool
reflectedArgumentResult =
    isIdentity $ guess $ \value ->
        if forceOnWorker value then True else False

reflectedResultResult :: Bool
reflectedResultResult =
    isAppliedIdentity $ guess $ \predicate value ->
        if forceOnWorker $ predicate value then True else False

reflectedApplicationResult :: Bool
reflectedApplicationResult =
    isApplication $ guess $ \fun value ->
        forceOnWorker $ fun value

maskedApplicationResult :: Bool
maskedApplicationResult =
    isAppliedIdentity $ guess $ \predicate value ->
        if forceMasked $ predicate $ interruptibly value
            then True
            else False

{-# NOINLINE forceMasked #-}
forceMasked :: a -> a
forceMasked value =
    unsafePerformIO $ mask_ $ evaluate value

-- Rather than asking what the masking state says, this insists on the consequence of it: an
-- asynchronous exception really is thrown at the thread materializing the argument, and really
-- has to arrive.  An interrupt which can be delivered at all is delivered to an allocating loop
-- promptly; one thrown at a thread behind the forcing mask is not delivered while the loop runs,
-- however long it runs for.  So the loop outlasts its interrupt sixty times over, and only a
-- quotation which cannot be interrupted at all ever sees the end of it.
{-# NOINLINE interruptibly #-}
interruptibly :: a -> a
interruptibly value =
    unsafePerformIO $ do
        interrupted <- Timeout.timeout interruptibleMicros $ spinFor spinSteps
        case interrupted of
            Nothing ->
                pure value
            Just _ ->
                throwIO $
                    userError "a reflected application argument was quoted uninterruptibly"

interruptibleMicros :: Int
interruptibleMicros = 500000

-- About half a minute of counting.  Long enough that no scheduling delay can make an interrupt
-- lose the race, short enough that an engine which cannot be interrupted still reports rather
-- than wedging the run.  Counting in IO, it also cannot be shared between quotations the way a
-- suspended pure loop could be.
spinSteps :: Integer
spinSteps = 4000000000

{-# NOINLINE spinFor #-}
spinFor :: Integer -> IO Integer
spinFor limit = go 0
  where
    go n
        | n >= limit = pure n
        | otherwise = go $! n + 1

-- Inspects its accumulator as well as growing it, so that the increment cannot be dropped as dead
-- code and the loop keeps allocating.  That matters: a loop that allocates can be interrupted, so
-- an implementation that insists on this argument is reported as a failure instead of wedging the
-- whole run, and unlike a blocked MVar there is no exception for it to recover from.
{-# NOINLINE spinBool #-}
spinBool :: Integer -> a
spinBool n
    | n < 0 = spinBool 0
    | otherwise = spinBool $ n + 1

discardedDivergenceResult :: Bool
discardedDivergenceResult =
    isSecondProjection $ guess $ \fun value ->
        let applied = fun (spinBool 0 `asTypeOf` value)
         in applied `seq` (value `asTypeOf` applied)

isIdentity :: ExprR -> Bool
isIdentity (LamR name (VarR actualName)) =
    name == actualName
isIdentity _ = False

isAppliedIdentity :: ExprR -> Bool
isAppliedIdentity
        (LamR predicateName
            (LamR valueName
                (AppR (VarR actualPredicateName) (VarR actualValueName)))) =
    predicateName == actualPredicateName
        && valueName == actualValueName
isAppliedIdentity _ = False

isApplication :: ExprR -> Bool
isApplication
        (LamR funName
            (LamR valueName
                (AppR (VarR actualFunName) (VarR actualValueName)))) =
    funName == actualFunName
        && valueName == actualValueName
isApplication _ = False

isSecondProjection :: ExprR -> Bool
isSecondProjection (LamR _ (LamR valueName (VarR actualValueName))) =
    valueName == actualValueName
isSecondProjection _ = False

{-# NOINLINE forceOnWorker #-}
forceOnWorker :: a -> a
forceOnWorker value = unsafePerformIO $ do
    resultV <- newEmptyMVar
    _ <- forkIO $ tryEvaluate value >>= putMVar resultV
    result <- takeMVar resultV
    either throwIO pure result

tryEvaluate :: a -> IO (Either SomeException a)
tryEvaluate = try . evaluate

stressResult :: Bool
stressResult =
    isRepeatedExpected $
        guess $
            repeatedCase
                stressBigConditionDepth
                stressBranchDepth

fullBinary :: Int -> (a -> a -> a) -> a -> a
fullBinary 0 _ value = value
fullBinary depth combine value =
    let subtree = fullBinary (depth - 1) combine value
     in combine subtree subtree

decisionTree
    :: Int
    -> (a -> Bool)
    -> (a -> a)
    -> (a -> a)
    -> a
    -> a
decisionTree 0 _ _ _ value = value
decisionTree depth predicate left right value =
    if predicate value
        then decisionTree
            (depth - 1)
            predicate
            left
            right
            (left value)
        else decisionTree
            (depth - 1)
            predicate
            left
            right
            (right value)

repeatedCase
    :: Int
    -> Int
    -> (a -> Bool)
    -> (a -> a -> a)
    -> (a -> Bool)
    -> (a -> a)
    -> (a -> a)
    -> a
    -> a
repeatedCase
        binaryDepth
        treeDepth
        expensivePredicate
        combine
        cheapPredicate
        left
        right
        value =
    let expensive = fullBinary binaryDepth combine value
        tripled = combine expensive $ combine expensive expensive
     in if expensivePredicate tripled
            then decisionTree treeDepth cheapPredicate left right value
            else value

isRepeatedExpected :: ExprR -> Bool
isRepeatedExpected expr =
    case expr of
        LamR expensivePredicateName
            (LamR combineName
                (LamR cheapPredicateName
                    (LamR leftName
                        (LamR rightName
                            (LamR valueName body))))) ->
            case body of
                IteR condition yes (VarR noName) ->
                    noName == valueName
                        && isExpensiveCondition
                            stressBigConditionDepth
                            expensivePredicateName
                            combineName
                            valueName
                            condition
                        && isDecisionTree
                            stressBranchDepth
                            cheapPredicateName
                            leftName
                            rightName
                            valueName
                            []
                            yes
                _ -> False
        _ -> False

isExpensiveCondition :: Int -> String -> String -> String -> ExprR -> Bool
isExpensiveCondition depth predicateName combineName valueName expr =
    case expr of
        AppR (VarR actualPredicateName) argument ->
            actualPredicateName == predicateName
                && isTripled depth combineName valueName argument
        _ -> False

isTripled :: Int -> String -> String -> ExprR -> Bool
isTripled depth combineName valueName expr =
    case expr of
        AppR
            (AppR (VarR firstCombineName) first)
            (AppR
                (AppR (VarR secondCombineName) second)
                third) ->
            firstCombineName == combineName
                && secondCombineName == combineName
                && isFullBinary depth combineName valueName first
                && isFullBinary depth combineName valueName second
                && isFullBinary depth combineName valueName third
        _ -> False

isFullBinary :: Int -> String -> String -> ExprR -> Bool
isFullBinary 0 _ valueName expr = isNamedVariable valueName expr
isFullBinary depth combineName valueName expr =
    case expr of
        AppR (AppR (VarR actualCombineName) left) right ->
            actualCombineName == combineName
                && isFullBinary
                    (depth - 1)
                    combineName
                    valueName
                    left
                && isFullBinary
                    (depth - 1)
                    combineName
                    valueName
                    right
        _ -> False

isDecisionTree
    :: Int
    -> String
    -> String
    -> String
    -> String
    -> [String]
    -> ExprR
    -> Bool
isDecisionTree 0 _ _ _ valueName path expr =
    isApplicationPath valueName path expr
isDecisionTree
        depth
        predicateName
        leftName
        rightName
        valueName
        path
        expr =
    case expr of
        IteR
            (AppR (VarR actualPredicateName) argument)
            yes
            no ->
            actualPredicateName == predicateName
                && isApplicationPath valueName path argument
                && isDecisionTree
                    (depth - 1)
                    predicateName
                    leftName
                    rightName
                    valueName
                    (leftName : path)
                    yes
                && isDecisionTree
                    (depth - 1)
                    predicateName
                    leftName
                    rightName
                    valueName
                    (rightName : path)
                    no
        _ -> False

isApplicationPath :: String -> [String] -> ExprR -> Bool
isApplicationPath valueName [] expr = isNamedVariable valueName expr
isApplicationPath valueName (name : names) expr =
    case expr of
        AppR (VarR actualName) argument ->
            actualName == name
                && isApplicationPath valueName names argument
        _ -> False

isNamedVariable :: String -> ExprR -> Bool
isNamedVariable expectedName expr =
    case expr of
        VarR actualName -> actualName == expectedName
        _ -> False
