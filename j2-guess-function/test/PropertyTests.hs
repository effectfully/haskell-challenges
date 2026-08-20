{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module PropertyTests
    ( propertyTests
    ) where

import ExprREq
import Lib (guess)
import Lib.ExprR
import PerformanceTests (capFor)

import Control.Concurrent
    ( MVar
    , ThreadId
    , forkFinally
    , killThread
    , newEmptyMVar
    , putMVar
    , readMVar
    , tryPutMVar
    )
import Control.Exception (SomeException, bracket, evaluate)
import Control.Monad (void)
import Data.Coerce (coerce)
import Data.IORef
import qualified Data.Map.Strict as Map
import Data.Type.Equality ((:~:) (Refl))
import GHC.Stack (HasCallStack, emptyCallStack, freezeCallStack)
import System.IO.Unsafe (unsafePerformIO)
import System.Timeout (timeout)
import Test.Tasty
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Test.Tasty.Providers (IsTest (run, testOptions))
import Test.Tasty.Providers.ConsoleFormat (noResultDetails)
import Test.Tasty.Runners
    ( FailureReason (TestTimedOut)
    , Outcome (Failure)
    , Result
        ( Result
        , resultDescription
        , resultDetailsPrinter
        , resultOutcome
        , resultShortDescription
        , resultTime
        )
    , TestTree (..)
    )
import qualified Test.Tasty.QuickCheck as QC
import qualified Test.QuickCheck.Property as QCP
import qualified Test.QuickCheck.State as QCS

withoutCallStack :: (HasCallStack => a) -> a
withoutCallStack x =
    let ?callStack = freezeCallStack emptyCallStack
     in x

recordPropertyProgress :: IORef Int -> QCS.State -> QCP.Result -> IO ()
recordPropertyProgress passedCount state result =
    case QCP.ok result of
        Just True ->
            writeIORef passedCount $
                QCS.numSuccessTests state + 1
        _ ->
            pure ()

data ReportPropertyProgress t = ReportPropertyProgress (IORef Int) Timeout t

instance IsTest t => IsTest (ReportPropertyProgress t) where
    testOptions =
        coerce (testOptions @t)

    run opts (ReportPropertyProgress passedCount testTimeout test) updateProgress = do
        writeIORef passedCount 0
        case testTimeout of
            NoTimeout ->
                run opts test updateProgress
            Timeout micros _ -> do
                result <- timeout (fromInteger micros) $ run opts test updateProgress
                case result of
                    Just testResult ->
                        pure testResult
                    Nothing ->
                        propertyTimeoutResult passedCount micros

propertyTimeoutResult :: IORef Int -> Integer -> IO Result
propertyTimeoutResult passedCount micros = do
    passed <- readIORef passedCount
    pure $
        Result
            { resultOutcome = Failure $ TestTimedOut micros
            , resultDescription =
                "QuickCheck generated cases passed before timeout: "
                    ++ show passed
            , resultShortDescription = "TIMEOUT"
            , resultTime = fromIntegral micros / 1000000
            , resultDetailsPrinter = noResultDetails
            }

reportPropertyProgress :: IORef Int -> Timeout -> TestTree -> TestTree
reportPropertyProgress passedCount testTimeout testTree =
    case testTree of
        SingleTest name test ->
            SingleTest name $ ReportPropertyProgress passedCount testTimeout test
        TestGroup name tests ->
            TestGroup name $ map (reportPropertyProgress passedCount testTimeout) tests
        PlusTestOptions options test ->
            PlusTestOptions options $ reportPropertyProgress passedCount testTimeout test
        WithResource resource useResource ->
            WithResource resource $ reportPropertyProgress passedCount testTimeout . useResource
        AskOptions withOptions ->
            AskOptions $ reportPropertyProgress passedCount testTimeout . withOptions
        After dependency patternExpr test ->
            After dependency patternExpr $ reportPropertyProgress passedCount testTimeout test

type Pred = Bool -> Bool
type Bin = Bool -> Bool -> Bool
type Tri = Bool -> Bool -> Bool -> Bool
type Quad = Bool -> Bool -> Bool -> Bool -> Bool
type Pent = Bool -> Bool -> Bool -> Bool -> Bool -> Bool
type WideEater2 = Pent -> Pent -> Bool -> Bool
type WideEater5 = Pent -> Pent -> Pent -> Pent -> Pent -> Bool -> Bool

data Ty a where
    TBool :: Ty Bool
    TFun :: Ty a -> Ty b -> Ty (a -> b)

data TestType a = TestType
    { testTypeRepr :: Ty a
    , testTypeGuess :: a -> ExprR
    }

withGeneratedRootType :: (forall a. TestType a -> QC.Gen r) -> QC.Gen r
withGeneratedRootType k =
    QC.frequency
        [ (1, k rootBinBinPredBool)
        , (1, k rootTriTriPredBool)
        , (2, k rootBinBinTriTriPredBool)
        , (2, k rootTriTriQuadQuadPredBool)
        , (3, k rootBinBinTriTriQuadQuadPredBool)
        , (1, k rootTriTriQuadQuadPentPentPredBool)
        , (6, k rootEaterEaterBinPredBool)
        , (6, k rootEaterEaterEaterTriBool)
        ]

rootEaterEaterBinPredBool :: TestType (WideEater5 -> WideEater2 -> WideEater2 -> Pred -> Bool -> Bool -> Bool -> Bool)
rootEaterEaterBinPredBool =
    TestType
        ( TFun wideEater5Ty $
            TFun wideEater2Ty $
                TFun wideEater2Ty $
                    TFun predTy $
                        TFun TBool $
                            TFun TBool $
                                TFun TBool TBool
        )
        $ withoutCallStack . guess

rootEaterEaterEaterTriBool :: TestType (WideEater5 -> WideEater5 -> WideEater2 -> Pred -> Bool -> Bool -> Bool -> Bool)
rootEaterEaterEaterTriBool =
    TestType
        ( TFun wideEater5Ty $
            TFun wideEater5Ty $
                TFun wideEater2Ty $
                    TFun predTy $
                        TFun TBool $
                            TFun TBool $
                                TFun TBool TBool
        )
        $ withoutCallStack . guess

rootBinBinPredBool :: TestType (Bin -> Bin -> Pred -> Bool -> Bool -> Bool -> Bool)
rootBinBinPredBool =
    TestType
        ( TFun binTy $
            TFun binTy $
                TFun predTy $
                    TFun TBool $
                        TFun TBool $
                            TFun TBool TBool
        )
        $ withoutCallStack . guess

rootTriTriPredBool :: TestType (Tri -> Tri -> Pred -> Bool -> Bool -> Bool -> Bool -> Bool)
rootTriTriPredBool =
    TestType
        ( TFun triTy $
            TFun triTy $
                TFun predTy $
                    TFun TBool $
                        TFun TBool $
                            TFun TBool $
                                TFun TBool TBool
        )
        $ withoutCallStack . guess

rootBinBinTriTriPredBool :: TestType (Bin -> Bin -> Tri -> Tri -> Pred -> Bool -> Bool -> Bool -> Bool -> Bool)
rootBinBinTriTriPredBool =
    TestType
        ( TFun binTy $
            TFun binTy $
                TFun triTy $
                    TFun triTy $
                        TFun predTy $
                            TFun TBool $
                                TFun TBool $
                                    TFun TBool $
                                        TFun TBool TBool
        )
        $ withoutCallStack . guess

rootTriTriQuadQuadPredBool :: TestType (Tri -> Tri -> Quad -> Quad -> Pred -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool)
rootTriTriQuadQuadPredBool =
    TestType
        ( TFun triTy $
            TFun triTy $
                TFun quadTy $
                    TFun quadTy $
                        TFun predTy $
                            TFun TBool $
                                TFun TBool $
                                    TFun TBool $
                                        TFun TBool $
                                            TFun TBool TBool
        )
        $ withoutCallStack . guess

rootBinBinTriTriQuadQuadPredBool :: TestType (Bin -> Bin -> Tri -> Tri -> Quad -> Quad -> Pred -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool)
rootBinBinTriTriQuadQuadPredBool =
    TestType
        ( TFun binTy $
            TFun binTy $
                TFun triTy $
                    TFun triTy $
                        TFun quadTy $
                            TFun quadTy $
                                TFun predTy $
                                        TFun TBool $
                                            TFun TBool $
                                                TFun TBool $
                                                    TFun TBool $
                                                        TFun TBool TBool
        )
        $ withoutCallStack . guess

rootTriTriQuadQuadPentPentPredBool :: TestType (Tri -> Tri -> Quad -> Quad -> Pent -> Pent -> Pred -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool)
rootTriTriQuadQuadPentPentPredBool =
    TestType
        ( TFun triTy $
            TFun triTy $
                TFun quadTy $
                    TFun quadTy $
                        TFun pentTy $
                            TFun pentTy $
                                TFun predTy $
                                    TFun TBool $
                                        TFun TBool $
                                            TFun TBool $
                                                TFun TBool $
                                                    TFun TBool $
                                                        TFun TBool TBool
        )
        $ withoutCallStack . guess

predTy :: Ty Pred
predTy =
    TFun TBool TBool

binTy :: Ty Bin
binTy =
    TFun TBool $ TFun TBool TBool

triTy :: Ty Tri
triTy =
    TFun TBool $ TFun TBool $ TFun TBool TBool

quadTy :: Ty Quad
quadTy =
    TFun TBool $ TFun TBool $ TFun TBool $ TFun TBool TBool

pentTy :: Ty Pent
pentTy =
    TFun TBool $ TFun TBool $ TFun TBool $ TFun TBool $ TFun TBool TBool

wideEater2Ty :: Ty WideEater2
wideEater2Ty =
    TFun pentTy $ TFun pentTy $ TFun TBool TBool

wideEater5Ty :: Ty WideEater5
wideEater5Ty =
    TFun pentTy $ TFun pentTy $ TFun pentTy $ TFun pentTy $ TFun pentTy $ TFun TBool TBool

showTy :: Ty a -> String
showTy =
    showTyPrec 0

showTyPrec :: Int -> Ty a -> String
showTyPrec prec ty =
    case ty of
        TBool ->
            "Bool"
        TFun arg res ->
            parensIf (prec > 0) $
                showTyPrec 1 arg ++ " -> " ++ showTyPrec 0 res

parensIf :: Bool -> String -> String
parensIf True text =
    "(" ++ text ++ ")"
parensIf False text =
    text

runAppPlan :: [Bool] -> (a -> a) -> (a -> a) -> a -> a
runAppPlan plan first second =
    go plan
  where
    go [] value =
        value
    go (useFirst : rest) value =
        (if useFirst then first else second) $ go rest value

appPlanExprR :: [Bool] -> ExprR
appPlanExprR plan =
    LamR "first" $
        LamR "second" $
            LamR "value" $
                foldr
                    ( \useFirst body ->
                        AppR
                            (VarR $ if useFirst then "first" else "second")
                            body
                    )
                    (VarR "value")
                    plan

nextAppSeed :: Int -> Int
nextAppSeed seed =
    seed * 1664525 + 1013904223

seededAppPlan :: Int -> Int -> [Bool]
seededAppPlan depth seed =
    take depth $ map appSeedChoice $ iterate nextAppSeed seed

appSeedChoice :: Int -> Bool
appSeedChoice seed =
    seed `mod` 7 < 3

runBalancedAppPlan :: Int -> Int -> (a -> a -> a) -> (a -> a) -> (a -> a) -> a -> a
runBalancedAppPlan depth seed combine first second value =
    go depth seed
  where
    go 0 leafSeed =
        (if appSeedChoice leafSeed then first else second) value
    go level nodeSeed =
        combine
            (go (level - 1) $ nextAppSeed nodeSeed)
            (go (level - 1) $ nextAppSeed $ nextAppSeed nodeSeed)

balancedAppPlanExprR :: Int -> Int -> ExprR
balancedAppPlanExprR depth seed =
    LamR "combine" $
        LamR "first" $
            LamR "second" $
                LamR "value" $
                    go depth seed
  where
    go 0 leafSeed =
        AppR
            (VarR $ if appSeedChoice leafSeed then "first" else "second")
            (VarR "value")
    go level nodeSeed =
        AppR
            ( AppR
                (VarR "combine")
                (go (level - 1) $ nextAppSeed nodeSeed)
            )
            (go (level - 1) $ nextAppSeed $ nextAppSeed nodeSeed)

data ApplicationStressCase
    = ApplicationStressCase Int Int
    deriving (Show)

genApplicationStressCase :: QC.Gen ApplicationStressCase
genApplicationStressCase =
    QC.sized $ \size ->
        ApplicationStressCase
            (applicationStressDepthForSize size)
            <$> QC.arbitrary

applicationStressCaseExprs :: ApplicationStressCase -> (ExprR, ExprR)
applicationStressCaseExprs (ApplicationStressCase depth seed) =
    let plan = seededAppPlan depth seed
     in ( appPlanExprR plan
        , withoutCallStack $ guess $ runAppPlan plan
        )

applicationStressCaseApps :: ApplicationStressCase -> Int
applicationStressCaseApps (ApplicationStressCase depth _) =
    depth

data BoolPlan
    = BoolConst Bool
    | BoolInput Int
    | BoolIf BoolPlan BoolPlan BoolPlan

evalBoolPlan :: [Bool] -> BoolPlan -> Bool
evalBoolPlan inputs plan =
    case plan of
        BoolConst value ->
            value
        BoolInput index ->
            indexBoolPlanInput inputs index
        BoolIf cond yes no ->
            if evalBoolPlan inputs cond
                then evalBoolPlan inputs yes
                else evalBoolPlan inputs no

exprROfBoolPlan :: [String] -> BoolPlan -> ExprR
exprROfBoolPlan names plan =
    case plan of
        BoolConst value ->
            ValR value
        BoolInput index ->
            VarR $ indexBoolPlanInput names index
        BoolIf cond yes no ->
            IteR
                (exprROfBoolPlan names cond)
                (exprROfBoolPlan names yes)
                (exprROfBoolPlan names no)

indexBoolPlanInput :: [a] -> Int -> a
indexBoolPlanInput values index
    | index < 0 =
        error $ "negative BoolPlan input index: " ++ show index
    | otherwise =
        case drop index values of
            value : _ ->
                value
            [] ->
                error $ "BoolPlan input index out of range: " ++ show index

runBoolPlan30 ::
    BoolPlan ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool ->
    Bool
runBoolPlan30 plan
    b00 b01 b02 b03 b04 b05 b06 b07 b08 b09
    b10 b11 b12 b13 b14 b15 b16 b17 b18 b19
    b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 =
        evalBoolPlan
            [ b00, b01, b02, b03, b04, b05, b06, b07, b08, b09
            , b10, b11, b12, b13, b14, b15, b16, b17, b18, b19
            , b20, b21, b22, b23, b24, b25, b26, b27, b28, b29
            ]
            plan

data BranchStressCase
    = BranchStressChain Int Int Int Bool
    | BranchStressTree Int Int Int
    deriving (Show)

genBranchStressCase :: QC.Gen BranchStressCase
genBranchStressCase =
    QC.frequency
        [ ( 3
          , BranchStressChain
                <$> QC.chooseInt (26, 30)
                <*> QC.chooseInt (0, 29)
                <*> QC.elements [1, 7, 11, 13, 17, 19, 23, 29]
                <*> QC.arbitrary
          )
        , ( 1
          , BranchStressTree
                <$> QC.chooseInt (8, 10)
                <*> QC.chooseInt (0, 28)
                <*> QC.chooseInt (1, 28)
          )
        ]

branchStressCasePlan :: BranchStressCase -> BoolPlan
branchStressCasePlan stressCase =
    case stressCase of
        BranchStressChain width start stride reversePolarity ->
            let indices =
                    take width $
                        iterate (\index -> (index + stride) `mod` 30) start
             in if reversePolarity
                    then foldr addReverse (BoolConst False) indices
                    else foldr addForward (BoolConst True) indices
        BranchStressTree depth start stride ->
            fullTree $
                take depth $
                    iterate (\index -> (index + stride) `mod` 29) start
  where
    addForward index rest =
        BoolIf (BoolInput index) (BoolConst False) rest

    addReverse index rest =
        BoolIf (BoolInput index) rest (BoolConst True)

    fullTree [] =
        BoolInput 29
    fullTree (index : rest) =
        BoolIf
            (BoolInput index)
            (fullTree rest)
            (fullTree rest)

branchStressCaseItes :: BranchStressCase -> Int
branchStressCaseItes stressCase =
    case stressCase of
        BranchStressChain width _ _ _ ->
            width
        BranchStressTree depth _ _ ->
            2 ^ depth - 1

branchStressCaseDepth :: BranchStressCase -> Int
branchStressCaseDepth stressCase =
    case stressCase of
        BranchStressChain width _ _ _ ->
            width
        BranchStressTree depth _ _ ->
            depth

eqTy :: Ty a -> Ty b -> Maybe (a :~: b)
eqTy left right =
    case (left, right) of
        (TBool, TBool) ->
            Just Refl
        (TFun argL resL, TFun argR resR) -> do
            Refl <- eqTy argL argR
            Refl <- eqTy resL resR
            Just Refl
        _ ->
            Nothing

data Var a where
    Var :: String -> Ty a -> Var a

data SomeVar where
    SomeVar :: Var a -> SomeVar

varName :: Var a -> String
varName (Var name _) =
    name

varType :: Var a -> Ty a
varType (Var _ ty) =
    ty

data TExpr a where
    EVal :: Bool -> TExpr Bool
    EVar :: Var a -> TExpr a
    EApp :: TExpr (a -> b) -> TExpr a -> TExpr b
    ELam :: Var a -> TExpr b -> TExpr (a -> b)
    EIte :: TExpr Bool -> TExpr a -> TExpr a -> TExpr a

exprROf :: TExpr a -> ExprR
exprROf expr =
    case expr of
        EVal b ->
            ValR b
        EVar var ->
            VarR $ varName var
        EApp f x ->
            AppR (exprROf f) (exprROf x)
        ELam var body ->
            LamR (varName var) $ exprROf body
        EIte cond yes no ->
            IteR (exprROf cond) (exprROf yes) (exprROf no)

data Binding where
    Binding :: Var a -> a -> Binding

newtype EvalEnv = EvalEnv [Binding]

lookupVar :: Var a -> EvalEnv -> a
lookupVar needle (EvalEnv bindings) =
    go bindings
  where
    go [] =
        error $ "unbound variable in property evaluator: " ++ varName needle
    go (Binding var value : rest)
        | varName var == varName needle =
            case eqTy (varType var) (varType needle) of
                Just Refl ->
                    value
                Nothing ->
                    error $ "type mismatch for variable: " ++ varName needle
        | otherwise =
            go rest

extendEnv :: Var a -> a -> EvalEnv -> EvalEnv
extendEnv var value (EvalEnv bindings) =
    EvalEnv $ Binding var value : bindings

emptyEvalEnv :: EvalEnv
emptyEvalEnv =
    EvalEnv []

evalExpr :: EvalEnv -> TExpr a -> a
evalExpr env expr =
    evalExprCps env expr id

evalExprCps :: EvalEnv -> TExpr a -> (a -> r) -> r
evalExprCps env expr k =
    case expr of
        EVal b ->
            k b
        EVar var ->
            k $ lookupVar var env
        EApp f x ->
            evalExprCps env f $ \f' ->
                k $ f' $ evalExpr env x
        ELam var body ->
            k $ \value -> evalExprCps (extendEnv var value env) body id
        EIte cond yes no ->
            evalExprCps env cond $ \cond' ->
                if cond'
                    then evalExprCps env yes k
                    else evalExprCps env no k

data Scope = Scope
    { scopeVars :: [SomeVar]
    , scopeNext :: Int
    }

emptyScope :: Scope
emptyScope =
    Scope
        { scopeVars = []
        , scopeNext = 0
        }

freshVar :: Ty a -> Scope -> (Var a, Scope)
freshVar ty scope =
    let name = "x" ++ show (scopeNext scope)
        var = Var name ty
     in ( var
        , scope
            { scopeVars = SomeVar var : scopeVars scope
            , scopeNext = scopeNext scope + 1
            }
        )

varsOfType :: Ty a -> Scope -> [Var a]
varsOfType ty scope =
    foldr collect [] $ scopeVars scope
  where
    collect (SomeVar var) acc =
        case eqTy (varType var) ty of
            Just Refl ->
                var : acc
            Nothing ->
                acc

data Args f b where
    ArgsDone :: Args b b
    ArgsCons :: Ty a -> Args r b -> Args (a -> r) b

data SomeArgs f b where
    SomeArgs :: Args f b -> Int -> SomeArgs f b

data SomeVarApp b where
    SomeVarApp :: Var f -> Args f b -> Int -> SomeVarApp b

data SomeFunIteApp b where
    SomeFunIteApp :: Var f -> Var f -> Args f b -> Int -> SomeFunIteApp b

boolArgSlots :: Args f b -> [Int]
boolArgSlots =
    go 0
  where
    go :: Int -> Args f b -> [Int]
    go _ ArgsDone =
        []
    go index (ArgsCons ty rest) =
        case eqTy ty TBool of
            Just Refl ->
                index : go (index + 1) rest
            Nothing ->
                go (index + 1) rest

argPlansTo :: Ty f -> Ty b -> Int -> [SomeArgs f b]
argPlansTo from target maxArgs =
    direct ++ stepped
  where
    direct =
        case eqTy from target of
            Just Refl ->
                [SomeArgs ArgsDone 0]
            Nothing ->
                []

    stepped =
        case (maxArgs, from) of
            (n, TFun arg res)
                | n > 0 ->
                    [ SomeArgs (ArgsCons arg args) (count + 1)
                    | SomeArgs args count <- argPlansTo res target (n - 1)
                    ]
            _ ->
                []

varAppsTo :: Scope -> Ty b -> Int -> Int -> [SomeVarApp b]
varAppsTo scope target minArgs maxArgs =
    foldr collect [] $ scopeVars scope
  where
    collect (SomeVar var) acc =
        [ SomeVarApp var args count
        | SomeArgs args count <- argPlansTo (varType var) target maxArgs
        , count >= minArgs
        ]
            ++ acc

funIteAppsTo :: forall b. Scope -> Ty b -> Int -> Int -> [SomeFunIteApp b]
funIteAppsTo scope target minArgs maxArgs =
    foldr collectLeft [] $ scopeVars scope
  where
    collectLeft (SomeVar varL) acc =
        foldr (collectRight varL) acc $ scopeVars scope

    collectRight :: forall f. Var f -> SomeVar -> [SomeFunIteApp b] -> [SomeFunIteApp b]
    collectRight varL (SomeVar varR) acc
        | varName varL == varName varR =
            acc
        | otherwise =
            case eqTy (varType varL) (varType varR) of
                Just Refl ->
                    [ SomeFunIteApp varL varR args count
                    | SomeArgs args count <- argPlansTo (varType varL) target maxArgs
                    , count >= minArgs
                    ]
                        ++ acc
                Nothing ->
                    acc

applyVariable :: Scope -> GenBudget -> Var f -> Args f b -> QC.Gen (TExpr b)
applyVariable scope budget var args =
    go (EVar var) args
  where
    go :: TExpr g -> Args g b -> QC.Gen (TExpr b)
    go fun ArgsDone =
        pure fun
    go fun (ArgsCons argTy rest) = do
        arg <- genSmallArg scope budget argTy
        go (EApp fun arg) rest

genSmallArg :: Scope -> GenBudget -> Ty a -> QC.Gen (TExpr a)
genSmallArg scope budget ty =
    case ty of
        TFun arg res ->
            QC.frequency
                [ (8, genConstFun scope ty)
                , (1, genFunLeaf scope arg res)
                ]
        TBool ->
            small
  where
    small =
        genExpr
            scope
            GenBudget
                { budgetApps = max 0 $ budgetApps budget `div` 8
                , budgetBranches = 0
                }
            ty

genConstFun :: Scope -> Ty a -> QC.Gen (TExpr a)
genConstFun scope ty =
    case ty of
        TBool ->
            EVal <$> QC.arbitrary
        TFun arg res ->
            let (var, scope') = freshVar arg scope
             in ELam var <$> genConstFun scope' res

type Size = Int
type Width = Int
type Depth = Int
type LevelPolicy = Depth -> Width -> Size -> [Size]

data GenBudget = GenBudget
    { budgetApps :: Int
    , budgetBranches :: Int
    }

minGeneratedApps :: Int
minGeneratedApps =
    64

maxGeneratedBranchDepth :: Int
maxGeneratedBranchDepth =
    2

minGeneratedItes :: Int
minGeneratedItes =
    4

maxGeneratedItes :: Int
maxGeneratedItes =
    6

mixedPropertyTestCount :: Int
mixedPropertyTestCount =
    25

mixedPropertyTimeoutMicros :: Integer
mixedPropertyTimeoutMicros =
    capFor 1.26

mixedPropertyMinSize :: Int
mixedPropertyMinSize =
    40

mixedPropertyMaxSize :: Int
mixedPropertyMaxSize =
    80

genBudget :: Size -> GenBudget
genBudget size =
    GenBudget
        { budgetApps = minGeneratedApps + 4 * max 0 size
        , budgetBranches = maxGeneratedBranchDepth
        }

splitEvenly :: Size -> Width -> [Size]
splitEvenly size width
    | width <= 0 =
        []
    | size <= 0 =
        replicate width 0
    | otherwise =
        replicate leftover (base + 1) ++ replicate (width - leftover) base
  where
    base =
        size `div` width

    leftover =
        size `mod` width

bigEnds :: LevelPolicy
bigEnds _depth width size0
    | width <= 0 =
        []
    | width == 1 =
        [size]
    | width == 2 =
        splitEvenly size 2
    | otherwise =
        left : middles ++ [right]
  where
    size =
        max 0 size0

    middleWidth =
        width - 2

    middleBudget =
        min middleWidth size

    endBudget =
        size - middleBudget

    left =
        (endBudget + 1) `div` 2

    right =
        endBudget `div` 2

    middles =
        splitEvenly middleBudget middleWidth

splitBudget3 :: Int -> QC.Gen (Int, Int, Int)
splitBudget3 budget = do
    sizes <-
        QC.elements
            [ take 3 $ splitEvenly budget 3 ++ repeat 0
            , take 3 $ bigEnds 0 3 budget ++ repeat 0
            ]
    case sizes of
        x : y : z : _ ->
            pure (x, y, z)
        _ ->
            error "splitBudget3: impossible width"

data SomeProgram where
    SomeProgram :: TestType a -> TExpr a -> SomeProgram

genSomeProgram :: QC.Gen SomeProgram
genSomeProgram = do
    size <- QC.chooseInt (mixedPropertyMinSize, mixedPropertyMaxSize)
    withGeneratedRootType $ \testType -> do
        expr <- genRootExpr emptyScope (genBudget size) $ testTypeRepr testType
        pure $ SomeProgram testType expr

genRootExpr :: Scope -> GenBudget -> Ty a -> QC.Gen (TExpr a)
genRootExpr scope budget ty =
    case ty of
        TBool ->
            genAppHeavyBool scope budget
        TFun arg res ->
            let (var, scope') = freshVar arg scope
             in ELam var <$> genRootExpr scope' budget res

genAppHeavyBool :: Scope -> GenBudget -> QC.Gen (TExpr Bool)
genAppHeavyBool scope budget = do
    spineLength <-
        QC.chooseInt
            ( max 4 $ minGeneratedApps `div` 4
            , max 4 $ budgetApps budget `div` 4
            )
    targetItes <-
        QC.chooseInt
            ( minGeneratedItes
            , max minGeneratedItes $ min maxGeneratedItes $ spineLength + 1
            )
    base <-
        genNestedIte
            scope
            GenBudget
                { budgetApps = max 0 $ budgetApps budget `div` 4
                , budgetBranches = budgetBranches budget
                }
            TBool
    addBoolAppSpine scope budget (targetItes - 2) True spineLength base

addBoolAppSpine :: Scope -> GenBudget -> Int -> Bool -> Int -> TExpr Bool -> QC.Gen (TExpr Bool)
addBoolAppSpine scope budget =
    go Nothing
  where
    go _ _ _ count expr
        | count <= 0 =
            pure expr
    go previous itesLeft needsFunIte count expr = do
        (currentHead, usedItes, usedFunIte, expr') <-
            genBoolWrapperApp scope budget previous itesLeft needsFunIte expr
        go currentHead (itesLeft - usedItes) (needsFunIte && not usedFunIte) (count - 1) expr'

genBoolWrapperApp ::
    Scope ->
    GenBudget ->
    Maybe String ->
    Int ->
    Bool ->
    TExpr Bool ->
    QC.Gen (Maybe String, Int, Bool, TExpr Bool)
genBoolWrapperApp scope budget previous itesLeft needsFunIte expr
    | null candidates0 =
        pure (previous, 0, False, expr)
    | needsFunIte && itesLeft > 0 && not (null funIteCandidates) =
        genFunctionIteWrapper
    | otherwise = do
        SomeVarApp var args _ <- QC.elements candidates
        currentSlot <- QC.elements $ boolArgSlots args
        let payloadSlots =
                take
                    (if itesLeft > 0 then 1 else 0)
                    [ slot
                    | slot <- boolArgSlots args
                    , slot /= currentSlot
                    ]
        payloads <-
            mapM
                ( \slot ->
                    fmap
                        (\payload -> (slot, payload))
                        ( genFlatIte
                            scope
                            GenBudget
                                { budgetApps = max 0 $ budgetApps budget `div` 10
                                , budgetBranches = 1
                                }
                            TBool
                        )
                )
                payloadSlots
        expr' <- applyFunctionWithBoolArgs scope budget ((currentSlot, expr) : payloads) (EVar var) args
        pure (Just $ varName var, length payloads, False, expr')
  where
    candidates0 =
        [ candidate
        | candidate@(SomeVarApp _ args _) <- varAppsTo scope TBool 2 6
        , not $ null $ boolArgSlots args
        ]

    candidatesWithoutPrevious =
        [ candidate
        | candidate@(SomeVarApp var _ _) <- candidates0
        , Just (varName var) /= previous
        ]

    candidates
        | null candidatesWithoutPrevious =
            candidates0
        | otherwise =
            candidatesWithoutPrevious

    funIteCandidates =
        [ candidate
        | candidate@(SomeFunIteApp _ _ args _) <- funIteAppsTo scope TBool 2 6
        , not $ null $ boolArgSlots args
        ]

    genFunctionIteWrapper = do
        SomeFunIteApp yesVar noVar args _ <- QC.elements funIteCandidates
        currentSlot <- QC.elements $ boolArgSlots args
        cond <-
            genExpr
                scope
                GenBudget
                    { budgetApps = max 0 $ budgetApps budget `div` 10
                    , budgetBranches = 0
                    }
                TBool
        let payloadSlots =
                take
                    (if itesLeft > 1 then 1 else 0)
                    [ slot
                    | slot <- boolArgSlots args
                    , slot /= currentSlot
                    ]
        payloads <-
            mapM
                ( \slot ->
                    fmap
                        (\payload -> (slot, payload))
                        ( genFlatIte
                            scope
                            GenBudget
                                { budgetApps = max 0 $ budgetApps budget `div` 10
                                , budgetBranches = 1
                                }
                            TBool
                        )
                )
                payloadSlots
        expr' <-
            applyFunctionWithBoolArgs
                scope
                budget
                ((currentSlot, expr) : payloads)
                (EIte cond (EVar yesVar) (EVar noVar))
                args
        pure (Just $ varName yesVar ++ "/" ++ varName noVar, 1 + length payloads, True, expr')

applyFunctionWithBoolArgs ::
    Scope ->
    GenBudget ->
    [(Int, TExpr Bool)] ->
    TExpr f ->
    Args f Bool ->
    QC.Gen (TExpr Bool)
applyFunctionWithBoolArgs scope budget boolArgs fun0 args =
    go 0 fun0 args
  where
    go :: Int -> TExpr g -> Args g Bool -> QC.Gen (TExpr Bool)
    go _ fun ArgsDone =
        pure fun
    go index fun (ArgsCons argTy rest) = do
        arg <-
            case eqTy argTy TBool of
                Just Refl ->
                    case lookup index boolArgs of
                        Just arg ->
                            pure arg
                        Nothing ->
                            genSmallArg scope budget argTy
                Nothing ->
                    genSmallArg scope budget argTy
        go (index + 1) (EApp fun arg) rest


genExpr :: Scope -> GenBudget -> Ty a -> QC.Gen (TExpr a)
genExpr scope budget ty =
    case ty of
        TBool ->
            genBool scope budget
        TFun arg res ->
            genFun scope budget arg res

genBool :: Scope -> GenBudget -> QC.Gen (TExpr Bool)
genBool scope budget
    | budgetApps budget <= 0 && budgetBranches budget <= 0 =
        genLeaf scope TBool
    | otherwise =
        QC.frequency $
            [(2, genLeaf scope TBool)]
                ++ [ (14, genAppTo scope budget TBool)
                   | budgetApps budget > 0
                   ]
                ++ [ (1, genIte scope budget TBool)
                   | budgetBranches budget > 0
                   ]

genFun :: Scope -> GenBudget -> Ty a -> Ty b -> QC.Gen (TExpr (a -> b))
genFun scope budget arg res
    | budgetApps budget <= 0 && budgetBranches budget <= 0 =
        genFunLeaf scope arg res
    | otherwise =
        QC.frequency $
            [(4, genFunLeaf scope arg res)]
                ++ [ (8, genAppTo scope budget $ TFun arg res)
                   | budgetApps budget > 0
                   ]
                ++ [ (1, genIte scope budget $ TFun arg res)
                   | budgetBranches budget > 0
                   ]
                ++ [(8, genLam scope budget arg res)]

genLeaf :: Scope -> Ty a -> QC.Gen (TExpr a)
genLeaf scope ty =
    case ty of
        TBool ->
            QC.frequency $
                [(2, EVal <$> QC.arbitrary)]
                    ++ [ (6, EVar <$> QC.elements vars)
                       | let vars = varsOfType TBool scope
                       , not $ null vars
                       ]
        TFun arg res ->
            genFunLeaf scope arg res

genFunLeaf :: Scope -> Ty a -> Ty b -> QC.Gen (TExpr (a -> b))
genFunLeaf scope arg res =
    QC.frequency $
        [ (6, EVar <$> QC.elements vars)
        | let vars = varsOfType (TFun arg res) scope
        , not $ null vars
        ]
            ++ [(4, genLam scope (GenBudget 0 0) arg res)]

genLam :: Scope -> GenBudget -> Ty a -> Ty b -> QC.Gen (TExpr (a -> b))
genLam scope budget arg res =
    let (var, scope') = freshVar arg scope
     in ELam var
            <$> genExpr
                scope'
                GenBudget
                    { budgetApps = max 0 $ budgetApps budget - 1
                    , budgetBranches = budgetBranches budget
                    }
                res

genAppTo :: Scope -> GenBudget -> Ty b -> QC.Gen (TExpr b)
genAppTo scope budget res =
    case varAppsTo scope res 1 6 of
        [] ->
            genLeaf scope res
        candidates -> do
            SomeVarApp var args count <- QC.elements candidates
            applyVariable
                scope
                GenBudget
                    { budgetApps = max 0 $ budgetApps budget - count
                    , budgetBranches = budgetBranches budget
                }
                var
                args

genFlatIte :: Scope -> GenBudget -> Ty a -> QC.Gen (TExpr a)
genFlatIte scope budget ty = do
    (condApps, yesApps, noApps) <- splitBudget3 $ budgetApps budget
    EIte
        <$> genExpr
            scope
            GenBudget
                { budgetApps = condApps
                , budgetBranches = 0
                }
            TBool
        <*> genExpr
            scope
            GenBudget
                { budgetApps = yesApps
                , budgetBranches = 0
                }
            ty
        <*> genExpr
            scope
            GenBudget
                { budgetApps = noApps
                , budgetBranches = 0
                }
            ty

genNestedIte :: Scope -> GenBudget -> Ty a -> QC.Gen (TExpr a)
genNestedIte scope budget ty = do
    (condApps, nestedApps, otherApps) <- splitBudget3 $ budgetApps budget
    nestedInThen <- QC.arbitrary
    cond <-
        genExpr
            scope
            GenBudget
                { budgetApps = condApps
                , budgetBranches = 0
                }
            TBool
    nested <-
        genFlatIte
            scope
            GenBudget
                { budgetApps = nestedApps
                , budgetBranches = 1
                }
            ty
    other <-
        genExpr
            scope
            GenBudget
                { budgetApps = otherApps
                , budgetBranches = 0
                }
            ty
    pure $
        if nestedInThen
            then EIte cond nested other
            else EIte cond other nested

genIte :: Scope -> GenBudget -> Ty a -> QC.Gen (TExpr a)
genIte scope budget ty = do
    (condApps, yesApps, noApps) <- splitBudget3 $ budgetApps budget
    (condBranches, yesBranches, noBranches) <-
        splitBudget3 $ max 0 $ budgetBranches budget - 1
    EIte
        <$> genExpr
            scope
            GenBudget
                { budgetApps = condApps
                , budgetBranches = condBranches
                }
            TBool
        <*> genExpr
            scope
            GenBudget
                { budgetApps = yesApps
                , budgetBranches = yesBranches
                }
            ty
        <*> genExpr
            scope
            GenBudget
                { budgetApps = noApps
                , budgetBranches = noBranches
                }
            ty

shrinkSomeProgram :: SomeProgram -> [SomeProgram]
shrinkSomeProgram (SomeProgram testType expr) =
    [ SomeProgram testType expr'
    | expr' <- shrinkExpr expr
    , mixedShape expr'
    ]

shrinkExpr :: TExpr a -> [TExpr a]
shrinkExpr expr =
    case expr of
        EVal _ ->
            []
        EVar _ ->
            []
        EApp f x ->
            [ EApp f' x | f' <- shrinkExpr f ]
                ++ [ EApp f x' | x' <- shrinkExpr x ]
        ELam var body ->
            [ ELam var body' | body' <- shrinkExpr body ]
        EIte cond yes no ->
            [yes, no]
                ++ [ EIte cond' yes no | cond' <- shrinkExpr cond ]
                ++ [ EIte cond yes' no | yes' <- shrinkExpr yes ]
                ++ [ EIte cond yes no' | no' <- shrinkExpr no ]

countApps :: TExpr a -> Int
countApps expr =
    case expr of
        EVal _ ->
            0
        EVar _ ->
            0
        EApp f x ->
            1 + countApps f + countApps x
        ELam _ body ->
            countApps body
        EIte cond yes no ->
            countApps cond + countApps yes + countApps no

maxIteDepth :: TExpr a -> Int
maxIteDepth expr =
    case expr of
        EVal _ ->
            0
        EVar _ ->
            0
        EApp f x ->
            max (maxIteDepth f) (maxIteDepth x)
        ELam _ body ->
            maxIteDepth body
        EIte cond yes no ->
            1 + maximum [maxIteDepth cond, maxIteDepth yes, maxIteDepth no]

mixedShape :: TExpr a -> Bool
mixedShape expr =
    countApps expr >= 32
        && countItes expr >= 3
        && maxIteDepth expr == maxGeneratedBranchDepth
        && countFunIteApps expr >= 1

countFunIteApps :: TExpr a -> Int
countFunIteApps expr =
    case expr of
        EVal _ ->
            0
        EVar _ ->
            0
        EApp f x ->
            funIteHead f + countFunIteApps f + countFunIteApps x
        ELam _ body ->
            countFunIteApps body
        EIte cond yes no ->
            countFunIteApps cond + countFunIteApps yes + countFunIteApps no
  where
    funIteHead :: TExpr (a -> b) -> Int
    funIteHead fun =
        case fun of
            EIte{} ->
                1
            _ ->
                0

countItes :: TExpr a -> Int
countItes expr =
    case expr of
        EVal _ ->
            0
        EVar _ ->
            0
        EApp f x ->
            countItes f + countItes x
        ELam _ body ->
            countItes body
        EIte cond yes no ->
            1 + countItes cond + countItes yes + countItes no

iteWork :: TExpr a -> Int
iteWork expr =
    case expr of
        EVal _ ->
            0
        EVar _ ->
            0
        EApp f x ->
            iteWork f + iteWork x
        ELam _ body ->
            iteWork body
        EIte cond yes no ->
            branchFactor cond * (branchFactor yes + branchFactor no)

branchFactor :: TExpr a -> Int
branchFactor expr =
    max 1 $ iteWork expr

normalizeExprR :: ExprR -> ExprR
normalizeExprR =
    normalizeWith Map.empty

normalizeWith :: Map.Map String Bool -> ExprR -> ExprR
normalizeWith env expr =
    case expr of
        ValR b ->
            ValR b
        VarR name ->
            case Map.lookup name env of
                Just value ->
                    ValR value
                Nothing ->
                    VarR name
        AppR f x ->
            normalizeApp env f x
        LamR name body ->
            LamR name $ normalizeWith (Map.delete name env) body
        IteR cond yes no ->
            normalizeIte env cond yes no

normalizeApp :: Map.Map String Bool -> ExprR -> ExprR -> ExprR
normalizeApp env f x =
    case normalizeWith env f of
        LamR name body ->
            normalizeWith env $ substExprR name x body
        IteR cond yes no ->
            normalizeWith env $ IteR cond (AppR yes x) (AppR no x)
        f' ->
            AppR f' $ normalizeWith env x

normalizeIte :: Map.Map String Bool -> ExprR -> ExprR -> ExprR -> ExprR
normalizeIte env cond yes no =
    case normalizeWith env cond of
        ValR True ->
            normalizeWith env yes
        ValR False ->
            normalizeWith env no
        IteR innerCond innerYes innerNo ->
            normalizeWith env $
                IteR
                    innerCond
                    (IteR innerYes yes no)
                    (IteR innerNo yes no)
        cond' ->
            let yes' = normalizeWith (assumeCond cond' True env) yes
                no' = normalizeWith (assumeCond cond' False env) no
             in case (yes', no') of
                    (ValR True, ValR False) ->
                        cond'
                    _ ->
                        IteR cond' yes' no'

assumeCond :: ExprR -> Bool -> Map.Map String Bool -> Map.Map String Bool
assumeCond cond value env =
    case cond of
        VarR name ->
            Map.insert name value env
        _ ->
            env

substExprR :: String -> ExprR -> ExprR -> ExprR
substExprR needle replacement expr =
    case expr of
        ValR b ->
            ValR b
        VarR name
            | name == needle ->
                replacement
            | otherwise ->
                VarR name
        AppR f x ->
            AppR
                (substExprR needle replacement f)
                (substExprR needle replacement x)
        LamR name body
            | name == needle ->
                LamR name body
            | otherwise ->
                LamR name $ substExprR needle replacement body
        IteR cond yes no ->
            IteR
                (substExprR needle replacement cond)
                (substExprR needle replacement yes)
                (substExprR needle replacement no)

countExprRApps :: ExprR -> Int
countExprRApps expr =
    case expr of
        ValR _ ->
            0
        VarR _ ->
            0
        AppR fun arg ->
            1 + countExprRApps fun + countExprRApps arg
        LamR _ body ->
            countExprRApps body
        IteR cond yes no ->
            countExprRApps cond + countExprRApps yes + countExprRApps no

countExprRItes :: ExprR -> Int
countExprRItes expr =
    case expr of
        ValR _ ->
            0
        VarR _ ->
            0
        AppR fun arg ->
            countExprRItes fun + countExprRItes arg
        LamR _ body ->
            countExprRItes body
        IteR cond yes no ->
            1 + countExprRItes cond + countExprRItes yes + countExprRItes no

maxExprRAppDepth :: ExprR -> Int
maxExprRAppDepth expr =
    case expr of
        ValR _ ->
            0
        VarR _ ->
            0
        AppR fun arg ->
            1 + max (maxExprRAppDepth fun) (maxExprRAppDepth arg)
        LamR _ body ->
            maxExprRAppDepth body
        IteR cond yes no ->
            maximum
                [ maxExprRAppDepth cond
                , maxExprRAppDepth yes
                , maxExprRAppDepth no
                ]

maxExprRIteDepth :: ExprR -> Int
maxExprRIteDepth expr =
    case expr of
        ValR _ ->
            0
        VarR _ ->
            0
        AppR fun arg ->
            max (maxExprRIteDepth fun) (maxExprRIteDepth arg)
        LamR _ body ->
            maxExprRIteDepth body
        IteR cond yes no ->
            1 + maximum
                [ maxExprRIteDepth cond
                , maxExprRIteDepth yes
                , maxExprRIteDepth no
                ]

applicationStressDepth :: Int
applicationStressDepth =
    350000

applicationStressTimeoutMicros :: Integer
applicationStressTimeoutMicros =
    capFor 0.63

-- The balanced tree is a third of the cost of the spine, so it gets a third of the budget rather
-- than sharing one and being held to nothing in particular.
balancedApplicationStressTimeoutMicros :: Integer
balancedApplicationStressTimeoutMicros =
    capFor 0.18

applicationStressPropertyCount :: Int
applicationStressPropertyCount =
    60

applicationStressMinGeneratedDepth :: Int
applicationStressMinGeneratedDepth =
    1000

applicationStressMaxGeneratedDepth :: Int
applicationStressMaxGeneratedDepth =
    16500

applicationStressSizeCap :: Int
applicationStressSizeCap =
    applicationStressPropertyCount - 1

applicationStressDepthForSize :: Int -> Int
applicationStressDepthForSize size =
    applicationStressMinGeneratedDepth
        + ( (applicationStressMaxGeneratedDepth - applicationStressMinGeneratedDepth)
                * boundedSize
          )
            `div` applicationStressSizeCap
  where
    boundedSize =
        min applicationStressSizeCap $ max 0 size

applicationStressPropertyTimeoutMicros :: Integer
applicationStressPropertyTimeoutMicros =
    capFor 0.67

balancedApplicationStressDepth :: Int
balancedApplicationStressDepth =
    15

applicationStressPlan :: [Bool]
applicationStressPlan =
    take applicationStressDepth $
        cycle [True, False, False, True, False, True, True, False]

applicationStressTest :: TestTree
applicationStressTest =
    localOption (mkTimeout applicationStressTimeoutMicros) $
        testCase "application-only polymorphic depth" $ do
            let expected = appPlanExprR applicationStressPlan
                actual = withoutCallStack $ guess $ runAppPlan applicationStressPlan
            countExprRApps expected @?= applicationStressDepth
            countExprRItes expected @?= 0
            maxExprRAppDepth expected @?= applicationStressDepth
            assertClosed actual
            alphaEtaNormalForm actual @?= alphaEtaNormalForm expected

balancedApplicationStressTest :: TestTree
balancedApplicationStressTest =
    localOption (mkTimeout balancedApplicationStressTimeoutMicros) $
        testCase "application-only balanced polymorphic tree" $ do
            let seed = 0
                expected = balancedAppPlanExprR balancedApplicationStressDepth seed
                actual =
                    withoutCallStack $
                        guess $ runBalancedAppPlan balancedApplicationStressDepth seed
                expectedApps = 3 * (2 ^ balancedApplicationStressDepth) - 2
            countExprRApps expected @?= expectedApps
            countExprRItes expected @?= 0
            assertClosed actual
            alphaEtaNormalForm actual @?= alphaEtaNormalForm expected

propApplicationStressCase :: ApplicationStressCase -> QC.Property
propApplicationStressCase stressCase =
    let (expected, actual) = applicationStressCaseExprs stressCase
        expectedApps = applicationStressCaseApps stressCase
     in QC.counterexample (show stressCase) $
            QC.conjoin
                [ QC.counterexample "application count changed" $
                    countExprRApps expected QC.=== expectedApps
                , QC.counterexample "an application-only case produced an if" $
                    countExprRItes expected QC.=== 0
                , QC.counterexample "guess returned an open expression" $
                    QC.property $ isClosedExprR actual
                , alphaEtaNormalForm actual QC.=== alphaEtaNormalForm expected
                ]

applicationStressProperties :: IORef Int -> TestTree
applicationStressProperties passedCount =
    localOption NoTimeout $
        reportPropertyProgress
            passedCount
            (mkTimeout applicationStressPropertyTimeoutMicros) $
            localOption (QC.QuickCheckTests applicationStressPropertyCount) $
                localOption (QC.QuickCheckMaxSize applicationStressPropertyCount) $
                    QC.testProperty "increasing polymorphic application spines" $
                        QCP.callback
                            ( QCP.PostTest QCP.NotCounterexample $
                                recordPropertyProgress passedCount
                            ) $
                            QC.forAllShrinkShow
                                genApplicationStressCase
                                (const [])
                                show
                                propApplicationStressCase

repeatedChainDepth :: Int
repeatedChainDepth =
    4000

repeatedChainTimeoutMicros :: Integer
repeatedChainTimeoutMicros =
    capFor 1.22

repeatedChain :: Int -> (a -> Bool) -> a -> Bool
repeatedChain 0 predicate input =
    predicate input
repeatedChain depth predicate input =
    if predicate input
        then repeatedChain (depth - 1) predicate input
        else False
{-# NOINLINE repeatedChain #-}

repeatedChainExprR :: Int -> ExprR
repeatedChainExprR depth =
    LamR "predicate" $
        LamR "input" $
            go depth
  where
    condition =
        AppR (VarR "predicate") (VarR "input")

    go 0 =
        condition
    go remaining =
        IteR condition (go $ remaining - 1) (ValR False)

repeatedChainTest :: TestTree
repeatedChainTest =
    localOption (mkTimeout repeatedChainTimeoutMicros) $
        testCase "one-sided condition chain" $ do
            let expected =
                    repeatedChainExprR repeatedChainDepth
                actual =
                    withoutCallStack $
                        guess $ repeatedChain repeatedChainDepth
            countExprRApps expected @?= repeatedChainDepth + 1
            countExprRItes expected @?= repeatedChainDepth
            maxExprRIteDepth expected @?= repeatedChainDepth
            assertClosed actual
            alphaEtaNormalForm actual @?= alphaEtaNormalForm expected

branchStressWidth :: Int
branchStressWidth =
    30

branchStressTimeoutMicros :: Integer
branchStressTimeoutMicros =
    capFor 0.20

-- Twenty-five generated plans cost about twice what the two fixed ones do, and are budgeted
-- separately for the same reason the two application stress cases are.
branchStressPropertyTimeoutMicros :: Integer
branchStressPropertyTimeoutMicros =
    capFor 0.28

branchStressPropertyCount :: Int
branchStressPropertyCount =
    25

branchStressPlan :: BoolPlan
branchStressPlan =
    foldr
        ( \index rest ->
            BoolIf (BoolInput index) (BoolConst False) rest
        )
        (BoolConst True)
        [0 .. branchStressWidth - 1]

branchStressNames :: [String]
branchStressNames =
    ["b" ++ show index | index <- [0 .. branchStressWidth - 1]]

assertBranchStressPlan :: BoolPlan -> Int -> Int -> IO ()
assertBranchStressPlan plan expectedItes expectedDepth = do
    let expected =
            foldr LamR
                (exprROfBoolPlan branchStressNames plan)
                branchStressNames
        actual = withoutCallStack $ guess $ runBoolPlan30 plan
    countExprRApps expected @?= 0
    countExprRItes expected @?= expectedItes
    maxExprRIteDepth expected @?= expectedDepth
    assertClosed actual
    alphaEtaNormalForm actual @?= alphaEtaNormalForm expected

branchTreeStressDepth :: Int
branchTreeStressDepth =
    11

branchStressTest :: TestTree
branchStressTest =
    localOption (mkTimeout branchStressTimeoutMicros) $
        testCase "branch-only decision depth" $ do
            assertBranchStressPlan
                branchStressPlan
                branchStressWidth
                branchStressWidth
            let stressCase = BranchStressTree branchTreeStressDepth 0 1
                plan = branchStressCasePlan stressCase
            assertBranchStressPlan
                plan
                (branchStressCaseItes stressCase)
                (branchStressCaseDepth stressCase)

propBranchStressCase :: BranchStressCase -> QC.Property
propBranchStressCase stressCase =
    let plan = branchStressCasePlan stressCase
        expectedItes = branchStressCaseItes stressCase
        expectedDepth = branchStressCaseDepth stressCase
        expected =
            foldr LamR
                (exprROfBoolPlan branchStressNames plan)
                branchStressNames
        actual = withoutCallStack $ guess $ runBoolPlan30 plan
     in QC.counterexample (show stressCase) $
            QC.conjoin
                [ QC.counterexample "a branch-only case produced an application" $
                    countExprRApps expected QC.=== 0
                , QC.counterexample "branch count changed" $
                    countExprRItes expected QC.=== expectedItes
                , QC.counterexample "branch depth changed" $
                    maxExprRIteDepth expected QC.=== expectedDepth
                , QC.counterexample "guess returned an open expression" $
                    QC.property $ isClosedExprR actual
                , alphaEtaNormalForm actual QC.=== alphaEtaNormalForm expected
                ]

branchStressProperties :: IORef Int -> TestTree
branchStressProperties passedCount =
    localOption NoTimeout $
        reportPropertyProgress passedCount (mkTimeout branchStressPropertyTimeoutMicros) $
            localOption (QC.QuickCheckTests branchStressPropertyCount) $
                QC.testProperty "heavy zero-application branch plans" $
                    QCP.callback
                        ( QCP.PostTest QCP.NotCounterexample $
                            recordPropertyProgress passedCount
                        ) $
                        QC.forAllShrinkShow
                            genBranchStressCase
                            (const [])
                            show
                            propBranchStressCase

closedRootCallCount :: Int
closedRootCallCount =
    1800000

closedRootInput :: Bool -> Int -> Bool
closedRootInput expected callIndex
    | callIndex == 0 = not expected
    | otherwise = expected
{-# NOINLINE closedRootInput #-}

assertClosedRoot :: Bool -> IO ()
assertClosedRoot expected =
    go closedRootCallCount
  where
    go 0 =
        pure ()
    go remaining = do
        actual <-
            evaluate $
                withoutCallStack $
                    guess $ closedRootInput expected remaining
        case actual of
            ValR result
                | result == expected ->
                    go $ remaining - 1
            _ ->
                actual @?= ValR expected

closedRootTimeoutMicros :: Integer
closedRootTimeoutMicros =
    capFor 0.20

closedRootTests :: TestTree
closedRootTests =
    localOption (mkTimeout closedRootTimeoutMicros) $
    testGroup
        "closed roots"
        [ testCase "True" $ assertClosedRoot True
        , testCase "False" $ assertClosedRoot False
        ]

concurrentGuessTestTimeoutMicros :: Integer
concurrentGuessTestTimeoutMicros =
    7000000

concurrentProgressTimeoutMicros :: Int
concurrentProgressTimeoutMicros =
    2000000

concurrentCleanupTimeoutMicros :: Int
concurrentCleanupTimeoutMicros =
    2000000

exprRSize :: ExprR -> Int
exprRSize expression =
    case expression of
        ValR value ->
            value `seq` 1
        VarR name ->
            1 + length name
        AppR fun arg ->
            1 + exprRSize fun + exprRSize arg
        LamR name body ->
            1 + length name + exprRSize body
        IteR condition yes no ->
            1 + exprRSize condition + exprRSize yes + exprRSize no

fullyEvaluateExprR :: ExprR -> IO ExprR
fullyEvaluateExprR expression = do
    _ <- evaluate $ exprRSize expression
    pure expression

type ExprWorker =
    (ThreadId, MVar (Either SomeException ExprR))

spawnExprWorker :: IO ExprR -> IO ExprWorker
spawnExprWorker action = do
    resultVar <- newEmptyMVar
    threadId <- forkFinally action $ putMVar resultVar
    pure (threadId, resultVar)

stopExprWorker :: ExprWorker -> IO ()
stopExprWorker (threadId, _) =
    killThread threadId

handshakeValue :: MVar () -> MVar () -> a -> a
handshakeValue ownGate peerGate value =
    unsafePerformIO $ do
        void $ tryPutMVar ownGate ()
        readMVar peerGate
        pure value
{-# NOINLINE handshakeValue #-}

type ConcurrentGuess =
    MVar () -> MVar () -> ExprR

concurrentIdentityGuess :: ConcurrentGuess
concurrentIdentityGuess ownGate peerGate =
    withoutCallStack $
        guess (handshakeValue ownGate peerGate :: Bool -> Bool)

concurrentNegationGuess :: ConcurrentGuess
concurrentNegationGuess ownGate peerGate =
    withoutCallStack $
        guess $ \(predicate :: Bool -> Bool) input ->
            handshakeValue ownGate peerGate $
                if predicate input then False else True

concurrentSelectionGuess :: ConcurrentGuess
concurrentSelectionGuess ownGate peerGate =
    withoutCallStack $
        guess $ \(condition :: Bool) first second input ->
            handshakeValue ownGate peerGate $
                (if condition then first else second) input

expectExprResult :: String -> ExprR -> Either SomeException ExprR -> IO ()
expectExprResult label expected result =
    case result of
        Left exception ->
            assertFailure $ label ++ " raised " ++ show exception
        Right actual -> do
            assertClosed actual
            alphaEtaNormalForm actual @?= alphaEtaNormalForm expected

assertConcurrentPair ::
    ConcurrentGuess ->
    ExprR ->
    ConcurrentGuess ->
    ExprR ->
    IO ()
assertConcurrentPair makeA expectedA makeB expectedB = do
    startGate <- newEmptyMVar
    readyA <- newEmptyMVar
    readyB <- newEmptyMVar
    enteredA <- newEmptyMVar
    enteredB <- newEmptyMVar

    let releaseEverything = do
            void $ tryPutMVar startGate ()
            void $ tryPutMVar enteredA ()
            void $ tryPutMVar enteredB ()

        action ready make ownGate peerGate = do
            putMVar ready ()
            readMVar startGate
            fullyEvaluateExprR $ make ownGate peerGate

        actionA =
            action readyA makeA enteredA enteredB

        actionB =
            action readyB makeB enteredB enteredA

        cleanup worker = do
            releaseEverything
            stopExprWorker worker

    bracket (spawnExprWorker actionA) cleanup $ \(_, doneA) ->
        bracket (spawnExprWorker actionB) cleanup $ \(_, doneB) -> do
            ready <-
                timeout concurrentProgressTimeoutMicros $ do
                    readMVar readyA
                    readMVar readyB
            case ready of
                Nothing ->
                    assertFailure "concurrent workers did not reach the start barrier"
                Just () ->
                    pure ()

            void $ tryPutMVar startGate ()
            beforeCleanup <-
                timeout concurrentProgressTimeoutMicros $ do
                    resultA <- readMVar doneA
                    resultB <- readMVar doneB
                    pure (resultA, resultB)

            releaseEverything
            settled <-
                timeout concurrentCleanupTimeoutMicros $ do
                    resultA <- readMVar doneA
                    resultB <- readMVar doneB
                    pure (resultA, resultB)

            case settled of
                Nothing ->
                    assertFailure "concurrent workers did not settle during cleanup"
                Just (resultA, resultB) -> do
                    expectExprResult "concurrent worker A" expectedA resultA
                    expectExprResult "concurrent worker B" expectedB resultB

            case beforeCleanup of
                Nothing ->
                    assertFailure "independent guess calls could not make concurrent progress"
                Just _ ->
                    pure ()

concurrentGuessTests :: TestTree
concurrentGuessTests =
    localOption (mkTimeout concurrentGuessTestTimeoutMicros) $
        testGroup
            "concurrent guesses"
            [ testCase "independent identities make concurrent progress" $
                assertConcurrentPair
                    concurrentIdentityGuess
                    (LamR "left" $ VarR "left")
                    concurrentIdentityGuess
                    (LamR "right" $ VarR "right")
            , testCase "concurrent conditionals stay independent" $
                assertConcurrentPair
                    concurrentNegationGuess
                    ( LamR "predicate" $
                        LamR "input" $
                            IteR
                                (AppR (VarR "predicate") $ VarR "input")
                                (ValR False)
                                (ValR True)
                    )
                    concurrentSelectionGuess
                    ( LamR "condition" $
                        LamR "first" $
                            LamR "second" $
                                LamR "input" $
                                    IteR
                                        (VarR "condition")
                                        (AppR (VarR "first") $ VarR "input")
                                        (AppR (VarR "second") $ VarR "input")
                    )
            ]

propertyTests :: IO TestTree
propertyTests = do
    applicationPassedCount <- newIORef 0
    branchPassedCount <- newIORef 0
    mixedPassedCount <- newIORef 0
    pure $
        testGroup
            "properties"
            [ closedRootTests
            , applicationStressTest
            , balancedApplicationStressTest
            , applicationStressProperties applicationPassedCount
            , repeatedChainTest
            , concurrentGuessTests
            , branchStressTest
            , branchStressProperties branchPassedCount
            , localOption NoTimeout $
                reportPropertyProgress mixedPassedCount (mkTimeout mixedPropertyTimeoutMicros) $
                    localOption (QC.QuickCheckTests mixedPropertyTestCount) $
                        localOption (QC.QuickCheckMaxSize mixedPropertyMaxSize) $
                            QC.testProperty "generated typed mixed lambdas normalize as guessed" $
                                QCP.callback
                                    ( QCP.PostTest QCP.NotCounterexample $
                                        recordPropertyProgress mixedPassedCount
                                    )
                                    $ QC.forAllShrinkShow
                                        genSomeProgram
                                        shrinkSomeProgram
                                        showProgram
                                        propSomeProgram
            ]

showProgram :: SomeProgram -> String
showProgram (SomeProgram testType expr) =
    "type: "
        ++ showTy (testTypeRepr testType)
        ++ "\napplications: "
        ++ show (countApps expr)
        ++ "\nif count: "
        ++ show (countItes expr)
        ++ "\nbranch depth: "
        ++ show (maxIteDepth expr)
        ++ "\nif work: "
        ++ show (iteWork expr)
        ++ "\nfunction-if applications: "
        ++ show (countFunIteApps expr)
        ++ "\nterm:\n"
        ++ renderExprR (exprROf expr)

propSomeProgram :: SomeProgram -> QC.Property
propSomeProgram (SomeProgram testType expr) =
    let source = exprROf expr
        expected = normalizeExprR source
        actual = testTypeGuess testType $ evalExpr emptyEvalEnv expr
        expectedNormal = alphaEtaNormalForm expected
        actualNormal = alphaEtaNormalForm actual
        shape = mixedShape expr
     in QC.counterexample (showProgram $ SomeProgram testType expr) $
            QC.counterexample ("expected:\n" ++ renderExprR expected) $
                QC.counterexample ("actual:\n" ++ renderExprR actual) $
                    QC.counterexample ("expected modulo alpha/eta:\n" ++ show expectedNormal) $
                        QC.counterexample ("actual modulo alpha/eta:\n" ++ show actualNormal) $
                            QC.conjoin
                                [ QC.counterexample
                                    "generated term escaped the mixed-shape invariant"
                                    shape
                                , QC.counterexample
                                    "guess returned an open expression"
                                    (isClosedExprR actual)
                                , (QC.===)
                                    expectedNormal
                                    actualNormal
                                ]

assertClosed :: ExprR -> IO ()
assertClosed expr =
    if isClosedExprR expr
        then pure ()
        else fail $ "guess returned an open expression:\n" ++ renderExprR expr
