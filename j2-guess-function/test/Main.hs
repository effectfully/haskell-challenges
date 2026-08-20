{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -O0 -fmax-simplifier-iterations=0 #-}

module Main (main) where

import ExprREq
import Lib (guess)
import Lib.ExprR
import NestingTests (nestingTests)
import PerformanceTests (performanceTests)
import PropertyTests (propertyTests)
import StressTests (stressTests)

import Data.List (group, intercalate, sort)
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import GHC.Stack (emptyCallStack, freezeCallStack)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import System.Random.Shuffle (shuffleM)
import System.Timeout (timeout)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Runners (NumThreads(..))

hardcore :: Int
hardcore = 0

withoutCallStack :: (HasCallStack => a) -> a
withoutCallStack x =
    let ?callStack = freezeCallStack emptyCallStack
     in x

data TestExpr where
    TestExpr :: String -> ExprR -> TestExpr

data Case where
    Case :: String -> [TestExpr] -> String -> Case

data TaxonomyLabel = TaxonomyLabel
    { labelPosition :: String
    , labelSource :: Set.Set String
    , labelShape :: Set.Set String
    , labelInvariance :: Set.Set String
    , labelVariant :: String
    }

expr :: [String] -> String
expr = intercalate "\n"

{- Note [Golden coverage taxonomy]
The golden suite tracks normalization along four axes so new tests can fill
coverage holes instead of adding stylistic near-duplicates.

Position:
ARG, FUN, BOTH, TOP, HOCTX.

Condition source:
NONE, DIR, REFL, COMP, CHOOSE1, HOBOOL, CHOOSEHO, MIXED-COND.

Shape:
BASE, APP-NEST, NEST-BR, NEST-COND, SIB, FUN+ARG-SHARED, FUN+ARG-INDEP,
REUSE, DUP-BR, CAPTURE, PAYLOAD-REUSE.

Invariance:
PLAIN, ID, NEG, DBLNEG, CONST, LET, BETA.

Multiple tags can appear in a slot with + when a test covers more than one
pattern on that axis.

The added groups below fill the main holes from the original matrix:
composed conditions in sibling and both-position contexts, higher-order
booleans in function/both/sibling contexts, chosen unary and chosen
higher-order conditions in function/both/sibling contexts, direct let-sharing
outside reflection, explicit ID wrappers for higher-order-driven function and
both-position cases, and composed self-reuse inside a branch.
-}

group00_1 :: Case
group00_1 =
    Case
        "expected00_1"
        [ TestExpr "ARG|DIR|BASE|ID|expr1" $
            withoutCallStack $ guess $
                \f b -> f (if b then True else False)
        , TestExpr "ARG|NONE|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \f b -> f b
        , TestExpr "TOP|REFL|BASE|ID|expr3" $
            withoutCallStack $ guess $
                \g b -> if g b then True else False
        , TestExpr "ARG|DIR|NEST-COND|DBLNEG|expr5" $
            withoutCallStack $ guess $
                \f b -> f (if (if b then False else True) then False else True)
        ]
        $ expr
            [ "\\f b ->"
            , "  f b"
            ]

group01 :: Case
group01 =
    Case
        "expected01"
        [ TestExpr "ARG|DIR|BASE|NEG|expr1" $
            withoutCallStack $ guess $
                \f b -> f (if b then False else True)
        ]
        $ expr
            [ "\\f b ->"
            , "  f (if b then False else True)"
            ]

group02 :: Case
group02 =
    Case
        "expected02"
        [ TestExpr "FUN|DIR|BASE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f g b c -> (if b then f else g) c
        ]
        $ expr
            [ "\\f g b c ->"
            , "  if b then f c else g c"
            ]

group02_b :: Case
group02_b =
    Case
        "expected02_b"
        [ TestExpr "FUN|REFL|BASE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \h f g b c -> (if h b then f else g) c
        ]
        $ expr
            [ "\\h f g b c ->"
            , "  if h b then f c else g c"
            ]

group03 :: Case
group03 =
    Case
        "expected03"
        [ TestExpr "ARG|DIR|APP-NEST|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f g b c -> f (g (if b then c else False))
        ]
        $ expr
            [ "\\f g b c ->"
            , "  f (g (if b then c else False))"
            ]

group04 :: Case
group04 =
    Case
        "expected04"
        [ TestExpr "ARG|NONE|REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f b -> f b b
        ]
        $ expr
            [ "\\f b ->"
            , "  f b b"
            ]

group05 :: Case
group05 =
    Case
        "expected05"
        [ TestExpr "ARG|DIR|SIB+PAYLOAD-REUSE|NEG|expr1" $
            withoutCallStack $ guess $
                \f b -> f (if b then False else True) (if b then True else False)
        ]
        $ expr
            [ "\\f b ->"
            , "  f (if b then False else True) b"
            ]

group06 :: Case
group06 =
    Case
        "expected06"
        [ TestExpr "ARG|DIR|PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f b c -> f (if b then c else b)
        , TestExpr "ARG|DIR|NEST-COND|ID|expr2" $
            withoutCallStack $ guess $
                \f b c -> f (if (if b then c else False) then True else False)
        , TestExpr "ARG|DIR|BASE|PLAIN|expr4" $
            withoutCallStack $ guess $
                \f b c -> f (if b then c else False)
        ]
        $ expr
            [ "\\f b c ->"
            , "  f (if b then c else False)"
            ]

group07 :: Case
group07 =
    Case
        "expected07"
        [ TestExpr "ARG|DIR|SIB+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f b c -> f b (if b then c else False)
        ]
        $ expr
            [ "\\f b c ->"
            , "  f b (if b then c else False)"
            ]

group08 :: Case
group08 =
    Case
        "expected08"
        [ TestExpr "ARG|DIR|APP-NEST|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f g h b c -> f (g (h (if b then c else False)))
        ]
        $ expr
            [ "\\f g h b c ->"
            , "  f (g (h (if b then c else False)))"
            ]

group09 :: Case
group09 =
    Case
        "expected09"
        [ TestExpr "FUN|DIR|APP-NEST|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f g b c d -> (if b then f else g) c d
        ]
        $ expr
            [ "\\f g b c d ->"
            , "  if b then f c d else g c d"
            ]

group10 :: Case
group10 =
    Case
        "expected10"
        [ TestExpr "ARG|REFL|BASE|NEG|expr1" $
            withoutCallStack $ guess $
                \g f b -> f (if g b then False else True)
        ]
        $ expr
            [ "\\g f b ->"
            , "  f (if g b then False else True)"
            ]

group11 :: Case
group11 =
    Case
        "expected11"
        [ TestExpr "BOTH|DIR|FUN+ARG-INDEP+PAYLOAD-REUSE|CONST|expr1" $
            withoutCallStack $ guess $
                \f g b c -> (if b then f else g) (if c then b else False)
        ]
        $ expr
            [ "\\f g b c ->"
            , "  if b then f c else g (if c then False else False)"
            ]

group12 :: Case
group12 =
    Case
        "expected12"
        [ TestExpr "ARG|DIR|SIB+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f b c -> f (if b then c else False) (if b then b else c)
        ]
        $ expr
            [ "\\f b c ->"
            , "  f (if b then c else False) (if b then True else c)"
            ]

group13 :: Case
group13 =
    Case
        "expected13"
        [ TestExpr "ARG|DIR|NEST-BR|NEG|expr1" $
            withoutCallStack $ guess $
                \f b c -> f (if b then (if c then False else True) else c)
        ]
        $ expr
            [ "\\f b c ->"
            , "  f (if b then if c then False else True else c)"
            ]

group13b :: Case
group13b =
    Case
        "expected13b"
        [ TestExpr "ARG|DIR|NEST-COND|NEG|expr1" $
            withoutCallStack $ guess $
                \f b c -> f (if (if b then c else False) then False else True)
        ]
        $ expr
            [ "\\f b c ->"
            , "  f (if b then if c then False else True else True)"
            ]

group14 :: Case
group14 =
    Case
        "expected14"
        [ TestExpr "ARG|CHOOSE1|BASE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \g h f b c -> f ((if b then g else h) c)
        , TestExpr "ARG|CHOOSE1|NEST-COND|ID|expr2" $
            withoutCallStack $ guess $
                \g h f b x -> f (if (if b then g else h) x then True else False)
        ]
        $ expr
            [ "\\g h f b c ->"
            , "  f (if b then g c else h c)"
            ]

group15 :: Case
group15 =
    Case
        "expected15"
        [ TestExpr "ARG|NONE|REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \g f b -> f (g b) (g b)
        ]
        $ expr
            [ "\\g f b ->"
            , "  f (g b) (g b)"
            ]

group16 :: Case
group16 =
    Case
        "expected16"
        [ TestExpr "ARG|DIR|SIB|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f b c d -> f (if b then c else d) (if c then b else d)
        ]
        $ expr
            [ "\\f b c d ->"
            , "  f (if b then c else d) (if c then b else d)"
            ]

group17 :: Case
group17 =
    Case
        "expected17"
        [ TestExpr "ARG|REFL|DUP-BR|CONST|expr1" $
            withoutCallStack $ guess $
                \g f b -> f (if g b then False else False)
        ]
        $ expr
            [ "\\g f b ->"
            , "  f (if g b then False else False)"
            ]

group18 :: Case
group18 =
    Case
        "expected18"
        [ TestExpr "ARG|REFL|DUP-BR|CONST|expr1" $
            withoutCallStack $ guess $
                \g f b -> f (if g b then True else True)
        ]
        $ expr
            [ "\\g f b ->"
            , "  f (if g b then True else True)"
            ]

group19 :: Case
group19 =
    Case
        "expected19"
        [ TestExpr "ARG|REFL|SIB|NEG|expr1" $
            withoutCallStack $ guess $
                \g f b -> f (if g b then False else True) (if g b then True else False)
        , TestExpr "ARG|REFL|SIB|LET+NEG|expr2" $
            withoutCallStack $ guess $ \g f b ->
                let z = g b
                 in f (if z then False else True) (if z then True else False)
        , TestExpr "ARG|REFL|SIB+PAYLOAD-REUSE|NEG|expr3" $
            withoutCallStack $ guess $
                \g f b -> f (if g b then False else True) (g b)
        , TestExpr "ARG|REFL|SIB+PAYLOAD-REUSE|ID+NEG|expr4" $
            withoutCallStack $ guess $
                \g f b ->
                    f
                        (if (if g b then True else False) then False else True)
                        (if g b then True else False)
        ]
        $ expr
            [ "\\g f b ->"
            , "  f (if g b then False else True) (g b)"
            ]

group20 :: Case
group20 =
    Case
        "expected20"
        [ TestExpr "BOTH|REFL|FUN+ARG-SHARED|NEG|expr1" $
            withoutCallStack $ guess $
                \g f h b -> (if g b then f else h) (if g b then False else True)
        ]
        $ expr
            [ "\\g f h b ->"
            , "  if g b"
            , "    then f (if g b then False else True)"
            , "    else h (if g b then False else True)"
            ]

group21 :: Case
group21 =
    Case
        "expected21"
        [ TestExpr "ARG|REFL|PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \g h f b -> f (if g b then h b else g b)
        , TestExpr "ARG|REFL|PAYLOAD-REUSE|ID|expr2" $
            withoutCallStack $ guess $
                \g h f b -> f (if (if g b then True else False) then h b else g b)
        ]
        $ expr
            [ "\\g h f b ->"
            , "  f (if g b then h b else g b)"
            ]

group22 :: Case
group22 =
    Case
        "expected22"
        [ TestExpr "ARG|REFL|SIB+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \g f b c -> f (if g b then c else b) (if g b then b else c)
        , TestExpr "ARG|REFL|SIB+PAYLOAD-REUSE|LET|expr2" $
            withoutCallStack $ guess $ \g f b c ->
                let z = g b
                 in f (if z then c else b) (if z then b else c)
        ]
        $ expr
            [ "\\g f b c ->"
            , "  f (if g b then c else b) (if g b then b else c)"
            ]

group23 :: Case
group23 =
    Case
        "expected23"
        [ TestExpr "ARG|REFL|SIB|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f g x a b c d -> g (if f x then a else b) (if f x then c else d)
        ]
        $ expr
            [ "\\f g x a b c d ->"
            , "  g"
            , "    (if f x then a else b)"
            , "    (if f x then c else d)"
            ]

group24 :: Case
group24 =
    Case
        "expected24"
        [ TestExpr "ARG|REFL|NEST-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f g x a b c -> g (if f x then (if f x then a else b) else c)
        ]
        $ expr
            [ "\\f g x a b c ->"
            , "  g (if f x then if f x then a else b else c)"
            ]

group25 :: Case
group25 =
    Case
        "expected25"
        [ TestExpr "ARG|COMP|BASE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f g h x a b -> h (if g (f x) then a else b)
        ]
        $ expr
            [ "\\f g h x a b ->"
            , "  h (if g (f x) then a else b)"
            ]

group26 :: Case
group26 =
    Case
        "expected26"
        [ TestExpr "TOP|MIXED-COND|DUP-BR|ID|expr1" $
            withoutCallStack $ guess $ \u b ->
                if b
                    then if u (\x -> x) then True else False
                    else if u (\x -> x) then True else False
        , TestExpr "TOP|MIXED-COND|DUP-BR|LET+ID|expr2" $
            withoutCallStack $ guess $ \u b ->
                let z = u (\x -> x)
                 in if b
                        then if z then True else False
                        else if z then True else False
        , TestExpr "TOP|MIXED-COND|DUP-BR|LET+ID|expr3" $
            withoutCallStack $ guess $ \u b ->
                if b
                    then let z = u (\x -> x) in if z then True else False
                    else let z = u (\x -> x) in if z then True else False
        ]
        $ expr
            [ "\\u b ->"
            , "  if b then u (\\x -> x) else u (\\x -> x)"
            ]

group27 :: Case
group27 =
    Case
        "expected27"
        [ TestExpr "HOCTX|DIR|BASE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \u v' w x -> u (if x then v' else w) x
        ]
        $ expr
            [ "\\u v' w x ->"
            , "  u (if x then v' else w) x"
            ]

group28 :: Case
group28 =
    Case
        "expected28"
        [ TestExpr "HOCTX|REFL|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \u f g h x -> u (if h x then f else g) (h x)
        , TestExpr "HOCTX|REFL|BASE|LET+ID|expr3" $
            withoutCallStack $ guess $ \u v' w f x ->
                let z = f x
                 in u (if z then v' else w) (if z then True else False)
        , TestExpr "HOCTX|REFL|BASE|ID|expr5" $
            withoutCallStack $ guess $
                \u f g h x -> u (if (if h x then True else False) then f else g) (h x)
        ]
        $ expr
            [ "\\u v' w f x ->"
            , "  u (if f x then v' else w) (f x)"
            ]

group29 :: Case
group29 =
    Case
        "expected29"
        [ TestExpr "HOCTX|DIR|BASE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \u f g x y -> u (if x then f else g) y
        ]
        $ expr
            [ "\\u f g x y ->"
            , "  u (if x then f else g) y"
            ]

group31 :: Case
group31 =
    Case
        "expected31"
        [ TestExpr "TOP|HOBOOL|BASE|ID|expr1" $
            withoutCallStack $ guess $ \u x ->
                if u (\y -> y) x then True else False
        ]
        $ expr
            [ "\\u x ->"
            , "  u (\\y -> y) x"
            ]

group32 :: Case
group32 =
    Case
        "expected32"
        [ TestExpr "ARG|REFL|SIB+APP-NEST|ID|expr1" $
            withoutCallStack $ guess $
                \g f b -> f (if g (g b) then True else False) (if g b then True else False)
        ]
        $ expr
            [ "\\g f b ->"
            , "  f (g (g b)) (g b)"
            ]

group33 :: Case
group33 =
    Case
        "expected33"
        [ TestExpr "TOP|DIR|NEST-COND|DBLNEG|expr1" $
            withoutCallStack $ guess $
                \b -> if (if b then True else False) then False else True
        ]
        $ expr
            [ "\\b ->"
            , "  if b then False else True"
            ]

group34 :: Case
group34 =
    Case
        "expected34"
        [ TestExpr "TOP|REFL|NEST-COND|DBLNEG|expr1" $
            withoutCallStack $ guess $
                \g b -> if (if g b then True else False) then False else True
        ]
        $ expr
            [ "\\g b ->"
            , "  if g b then False else True"
            ]

group35 :: Case
group35 =
    Case
        "expected35"
        [ TestExpr "TOP|DIR|CAPTURE|ID|expr1" $
            withoutCallStack $ guess $
                \u b -> if u (\x -> if b then x else False) then True else False
        ]
        $ expr
            [ "\\u b ->"
            , "  u (\\x -> if b then x else False)"
            ]

group36 :: Case
group36 =
    Case
        "expected36"
        [ TestExpr "ARG|REFL|SIB+PAYLOAD-REUSE|ID|expr1" $
            withoutCallStack $ guess $
                \g f b c -> f (if g b then c else False) (if g b then True else False)
        ]
        $ expr
            [ "\\g f b c ->"
            , "  f (if g b then c else False) (g b)"
            ]

group37 :: Case
group37 =
    Case
        "expected37"
        [ TestExpr "TOP|REFL|CAPTURE|ID|expr1" $
            withoutCallStack $ guess $
                \u g b -> if u (\x -> if g b then x else False) then True else False
        ]
        $ expr
            [ "\\u g b ->"
            , "  u (\\x -> if g b then x else False)"
            ]

group38 :: Case
group38 =
    Case
        "expected38"
        [ TestExpr "FUN|REFL|NEST-COND|ID|expr1" $
            withoutCallStack $ guess $
                \f g h b -> (if (if h b then True else False) then f else g) b
        ]
        $ expr
            [ "\\f g h b ->"
            , "  if h b then f b else g b"
            ]

group40 :: Case
group40 =
    Case
        "expected40"
        [ TestExpr "HOCTX|REFL|BASE|ID|expr1" $
            withoutCallStack $ guess $
                \u v' w f x -> u (if (if f x then True else False) then v' else w) x
        ]
        $ expr
            [ "\\u v' w f x ->"
            , "  u (if f x then v' else w) x"
            ]

group41 :: Case
group41 =
    Case
        "expected41"
        [ TestExpr "ARG|COMP|BASE|ID|expr1" $
            withoutCallStack $ guess $
                \g h f x -> f (if g (h x) then True else False)
        ]
        $ expr
            [ "\\g h f x ->"
            , "  f (g (h x))"
            ]

group42 :: Case
group42 =
    Case
        "expected42"
        [ TestExpr "FUN|COMP|BASE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f g h k x -> (if h (k x) then f else g) x
        ]
        $ expr
            [ "\\f g h k x ->"
            , "  if h (k x) then f x else g x"
            ]

group43 :: Case
group43 =
    Case
        "expected43"
        [ TestExpr "BOTH|DIR|FUN+ARG-SHARED|ID|expr1" $
            withoutCallStack $ guess $
                \f g b c -> (if (if b then True else False) then f else g) (if b then c else False)
        ]
        $ expr
            [ "\\f g b c ->"
            , "  if b then f c else g False"
            ]

group44 :: Case
group44 =
    Case
        "expected44"
        [ TestExpr "HOCTX|DIR|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \u f g b -> u (\x -> if b then f x else g x) b
        ]
        $ expr
            [ "\\u f g b ->"
            , "  u (\\x -> if b then f x else g x) b"
            ]

group45 :: Case
group45 =
    Case
        "expected45"
        [ TestExpr "ARG|REFL|SIB+NEST-COND+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \g f b c ->
                    f
                        (if g (if b then c else False) then True else False)
                        (if b then c else False)
        ]
        $ expr
            [ "\\g f b c ->"
            , "  f (g (if b then c else False)) (if b then c else False)"
            ]

group46 :: Case
group46 =
    Case
        "expected46"
        [ TestExpr "HOCTX|DIR|CAPTURE+NEST-COND|ID|expr1" $
            withoutCallStack $ guess $
                \u g b x -> u (\f y -> if f (if b then y else False) then True else False) g x
        ]
        $ expr
            [ "\\u g b x ->"
            , "  u (\\f y -> f (if b then y else False)) g x"
            ]

group47 :: Case
group47 =
    Case
        "expected47"
        [ TestExpr "ARG|MIXED-COND|NEST-COND|ID|expr1" $
            withoutCallStack $ guess $
                \g f a b c -> f (if (if g a then g b else g c) then True else False)
        , TestExpr "ARG|MIXED-COND|BASE|PLAIN|expr3" $
            withoutCallStack $ guess $
                \g f a b c -> f (if g a then g b else g c)
        ]
        $ expr
            [ "\\g f a b c ->"
            , "  f (if g a then g b else g c)"
            ]

group48 :: Case
group48 =
    Case
        "expected48"
        [ TestExpr "ARG|MIXED-COND|NEST-COND|ID|expr1" $
            withoutCallStack $ guess $
                \g h f x b -> f (if (if b then g x else h x) then True else False)
        , TestExpr "ARG|MIXED-COND|BASE|PLAIN|expr3" $
            withoutCallStack $ guess $
                \g h f x b -> f (if b then g x else h x)
        ]
        $ expr
            [ "\\g h f x b ->"
            , "  f (if b then g x else h x)"
            ]

group49 :: Case
group49 =
    Case
        "expected49"
        [ TestExpr "ARG|MIXED-COND|NEST-COND|ID|expr1" $
            withoutCallStack $ guess $
                \g h f b x y -> f (if (if b then g x else h y) then True else False)
        , TestExpr "ARG|MIXED-COND|BASE|PLAIN|expr3" $
            withoutCallStack $ guess $
                \g h f b x y -> f (if b then g x else h y)
        ]
        $ expr
            [ "\\g h f b x y ->"
            , "  f (if b then g x else h y)"
            ]

group51 :: Case
group51 =
    Case
        "expected51"
        [ TestExpr "ARG|MIXED-COND|NEST-COND|ID|expr1" $
            withoutCallStack $ guess $
                \g f b x y -> f (if g (if b then x else y) then True else False)
        , TestExpr "ARG|MIXED-COND|BASE|PLAIN|expr3" $
            withoutCallStack $ guess $
                \g f b x y -> f (g (if b then x else y))
        ]
        $ expr
            [ "\\g f b x y ->"
            , "  f (g (if b then x else y))"
            ]

group52 :: Case
group52 =
    Case
        "expected52"
        [ TestExpr "ARG|HOBOOL+CHOOSE1|NEST-COND|ID|expr1" $
            withoutCallStack $ guess $
                \u g h f b x -> f (if u (if b then g else h) x then True else False)
        , TestExpr "ARG|HOBOOL+CHOOSE1|BASE|PLAIN|expr3" $
            withoutCallStack $ guess $
                \u g h f b x -> f (u (if b then g else h) x)
        ]
        $ expr
            [ "\\u g h f b x ->"
            , "  f (u (if b then g else h) x)"
            ]

group53 :: Case
group53 =
    Case
        "expected53"
        [ TestExpr "ARG|HOBOOL|NEST-COND|ID|expr1" $
            withoutCallStack $ guess $
                \u g f b x y -> f (if u g (if b then x else y) then True else False)
        , TestExpr "ARG|HOBOOL|BASE|PLAIN|expr3" $
            withoutCallStack $ guess $
                \u g f b x y -> f (u g (if b then x else y))
        ]
        $ expr
            [ "\\u g f b x y ->"
            , "  f (u g (if b then x else y))"
            ]

group54 :: Case
group54 =
    Case
        "expected54"
        [ TestExpr "ARG|CHOOSEHO|NEST-COND|ID|expr1" $
            withoutCallStack $ guess $
                \u v' g f b x -> f (if (if b then u else v') g x then True else False)
        , TestExpr "ARG|CHOOSEHO|BASE|PLAIN|expr3" $
            withoutCallStack $ guess $
                \u v' g f b x -> f ((if b then u else v') g x)
        ]
        $ expr
            [ "\\u v' g f b x ->"
            , "  f (if b then u g x else v' g x)"
            ]

group55 :: Case
group55 =
    Case
        "expected55"
        [ TestExpr "ARG|MIXED-COND+COMP|NEST-BR|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h x a b c d ->
                h (if g (f x) then (if f x then a else b) else (if g x then c else d))
        ]
        $ expr
            [ "\\f g h x a b c d ->"
            , "  h"
            , "    (if g (f x) then if f x then a else b else if g x then c else d)"
            ]

group56 :: Case
group56 =
    Case
        "expected56"
        [ TestExpr "ARG|DIR|SIB|PLAIN|expr1" $
            withoutCallStack $ guess $ \f a b c d e ->
                f (if a then b else c) (if a then d else e)
        ]
        $ expr
            [ "\\f a b c d e ->"
            , "  f (if a then b else c) (if a then d else e)"
            ]

group57 :: Case
group57 =
    Case
        "expected57"
        [ TestExpr "ARG|COMP|SIB|PLAIN|expr1" $
            withoutCallStack $ guess $
                \g h f x a b c d ->
                    f (if g (h x) then a else b) (if g (h x) then c else d)
        , TestExpr "ARG|COMP|SIB|LET|expr1" $
            withoutCallStack $ guess $ \g h f x a b c d ->
                let z = g (h x)
                 in f (if z then a else b) (if z then c else d)
        ]
        $ expr
            [ "\\g h f x a b c d ->"
            , "  f"
            , "    (if g (h x) then a else b)"
            , "    (if g (h x) then c else d)"
            ]

group58 :: Case
group58 =
    Case
        "expected58"
        [ TestExpr "TOP|DIR|BASE|ID|expr1" $
            withoutCallStack $ guess $
                \b -> if b then True else False
        , TestExpr "TOP|NONE|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \b -> b
        ]
        $ expr
            [ "\\b ->"
            , "  b"
            ]

group59 :: Case
group59 =
    Case
        "expected59"
        [ TestExpr "BOTH|COMP|FUN+ARG-SHARED|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f g h k x y -> (if h (k x) then f else g) (if h (k x) then x else y)
        ]
        $ expr
            [ "\\f g h k x y ->"
            , "  if h (k x)"
            , "    then f (if h (k x) then x else y)"
            , "    else g (if h (k x) then x else y)"
            ]

group60 :: Case
group60 =
    Case
        "expected60"
        [ TestExpr "ARG|REFL|BASE|ID|expr1" $
            withoutCallStack $ guess $
                \g f b -> f (if g b then True else False)
        , TestExpr "ARG|REFL|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \g f b -> f (g b)
        , TestExpr "ARG|REFL|NEST-COND|DBLNEG|expr3" $
            withoutCallStack $ guess $
                \g f b -> f (if (if g b then False else True) then False else True)
        ]
        $ expr
            [ "\\g f b ->"
            , "  f (g b)"
            ]

group61 :: Case
group61 =
    Case
        "expected61"
        [ TestExpr "TOP|HOBOOL|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \u x -> u (\y -> y) x
        ]
        $ expr
            [ "\\u x ->"
            , "  u (\\y -> y) x"
            ]

group62 :: Case
group62 =
    Case
        "expected62"
        [ TestExpr "TOP|REFL|APP-NEST|ID|expr1" $
            withoutCallStack $ guess $
                \g b -> if g (g b) then True else False
        , TestExpr "TOP|REFL|APP-NEST|PLAIN|expr2" $
            withoutCallStack $ guess $
                \g b -> g (g b)
        ]
        $ expr
            [ "\\g b ->"
            , "  g (g b)"
            ]

group63 :: Case
group63 =
    Case
        "expected63"
        [ TestExpr "ARG|REFL|SIB+APP-NEST|PLAIN|expr2" $
            withoutCallStack $ guess $
                \g f b -> f (g (g b)) (g b)
        ]
        $ expr
            [ "\\g f b ->"
            , "  f (g (g b)) (g b)"
            ]

group64 :: Case
group64 =
    Case
        "expected64"
        [ TestExpr "TOP|DIR|CAPTURE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \u b -> u (\x -> if b then x else False)
        , TestExpr "TOP|DIR|CAPTURE|LET+ID|expr3" $
            withoutCallStack $ guess $ \u b ->
                let k = \x -> if b then x else False
                 in if u k then True else False
        ]
        $ expr
            [ "\\u b ->"
            , "  u (\\x -> if b then x else False)"
            ]

group65 :: Case
group65 =
    Case
        "expected65"
        [ TestExpr "TOP|REFL|CAPTURE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \u g b -> u (\x -> if g b then x else False)
        ]
        $ expr
            [ "\\u g b ->"
            , "  u (\\x -> if g b then x else False)"
            ]

group66 :: Case
group66 =
    Case
        "expected66"
        [ TestExpr "FUN|HOBOOL|BASE|ID|expr1" $
            withoutCallStack $ guess $
                \u f g h x -> (if (if u h x then True else False) then f else g) x
        , TestExpr "FUN|HOBOOL|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \u f g h x -> (if u h x then f else g) x
        ]
        $ expr
            [ "\\u f g h x ->"
            , "  if u h x then f x else g x"
            ]

group67 :: Case
group67 =
    Case
        "expected67"
        [ TestExpr "FUN|REFL|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \f g h b -> (if h b then f else g) b
        ]
        $ expr
            [ "\\f g h b ->"
            , "  if h b then f b else g b"
            ]

group68 :: Case
group68 =
    Case
        "expected68"
        [ TestExpr "ARG|REFL|SIB+PAYLOAD-REUSE|LET|expr1" $
            withoutCallStack $ guess $ \g f b c ->
                let z = g b
                 in f (if z then c else False) (if z then True else False)
        , TestExpr "ARG|REFL|SIB+PAYLOAD-REUSE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \g f b c -> f (if g b then c else False) (g b)
        , TestExpr "ARG|REFL|SIB+PAYLOAD-REUSE|ID|expr3" $
            withoutCallStack $ guess $
                \g f b c ->
                    f
                        (if (if g b then True else False) then c else False)
                        (if g b then True else False)
        ]
        $ expr
            [ "\\g f b c ->"
            , "  f (if g b then c else False) (g b)"
            ]

group69 :: Case
group69 =
    Case
        "expected69"
        [ TestExpr "BOTH|HOBOOL|FUN+ARG-SHARED|ID|expr1" $
            withoutCallStack $ guess $
                \u f g h x y ->
                    (if (if u h x then True else False) then f else g)
                        (if u h x then x else y)
        , TestExpr "BOTH|HOBOOL|FUN+ARG-SHARED|PLAIN|expr2" $
            withoutCallStack $ guess $
                \u f g h x y -> (if u h x then f else g) (if u h x then x else y)
        ]
        $ expr
            [ "\\u f g h x y ->"
            , "  if u h x"
            , "    then f (if u h x then x else y)"
            , "    else g (if u h x then x else y)"
            ]

group70 :: Case
group70 =
    Case
        "expected70"
        [ TestExpr "FUN|CHOOSE1|BASE|ID|expr1" $
            withoutCallStack $ guess $
                \f g h k b x ->
                    (if (if (if b then h else k) x then True else False) then f else g) x
        , TestExpr "FUN|CHOOSE1|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \f g h k b x -> (if (if b then h else k) x then f else g) x
        ]
        $ expr
            [ "\\f g h k b x ->"
            , "  if b"
            , "    then if h x then f x else g x"
            , "    else if k x then f x else g x"
            ]

groupChoose1BothFunArgShared :: Case
groupChoose1BothFunArgShared =
    Case
        "expected71"
        [ TestExpr "BOTH|CHOOSE1|FUN+ARG-SHARED|ID|expr1" $
            withoutCallStack $ guess $
                \f g h k b x y ->
                    (if (if (if b then h else k) x then True else False) then f else g)
                        (if (if b then h else k) x then x else y)
        , TestExpr "BOTH|CHOOSE1|FUN+ARG-SHARED|PLAIN|expr2" $
            withoutCallStack $ guess $
                \f g h k b x y ->
                    (if (if b then h else k) x then f else g)
                        (if (if b then h else k) x then x else y)
        ]
        $ expr
            [ "\\f g h k b x y ->"
            , "  if b"
            , "    then if h x"
            , "      then f (if h x then x else y)"
            , "      else g (if h x then x else y)"
            , "    else if k x"
            , "      then f (if k x then x else y)"
            , "      else g (if k x then x else y)"
            ]

group72 :: Case
group72 =
    Case
        "expected72"
        [ TestExpr "FUN|CHOOSEHO|BASE|ID|expr1" $
            withoutCallStack $ guess $
                \f g u v h b x ->
                    (if (if (if b then u else v) h x then True else False) then f else g) x
        , TestExpr "FUN|CHOOSEHO|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \f g u v h b x -> (if (if b then u else v) h x then f else g) x
        ]
        $ expr
            [ "\\f g u v h b x ->"
            , "  if b"
            , "    then if u h x then f x else g x"
            , "    else if v h x then f x else g x"
            ]

group73 :: Case
group73 =
    Case
        "expected73"
        [ TestExpr "BOTH|DIR|FUN+ARG-SHARED|PLAIN|expr2" $
            withoutCallStack $ guess $
                \f g b c -> (if b then f else g) (if b then c else False)
        ]
        $ expr
            [ "\\f g b c ->"
            , "  if b then f c else g False"
            ]

group74 :: Case
group74 =
    Case
        "expected74"
        [ TestExpr "BOTH|CHOOSEHO|FUN+ARG-SHARED|ID|expr1" $
            withoutCallStack $ guess $
                \f g u v h b x y ->
                    (if (if (if b then u else v) h x then True else False) then f else g)
                        (if (if b then u else v) h x then x else y)
        , TestExpr "BOTH|CHOOSEHO|FUN+ARG-SHARED|PLAIN|expr2" $
            withoutCallStack $ guess $
                \f g u v h b x y ->
                    (if (if b then u else v) h x then f else g)
                        (if (if b then u else v) h x then x else y)
        ]
        $ expr
            [ "\\f g u v h b x y ->"
            , "  if b"
            , "    then if u h x"
            , "      then f (if u h x then x else y)"
            , "      else g (if u h x then x else y)"
            , "    else if v h x"
            , "      then f (if v h x then x else y)"
            , "      else g (if v h x then x else y)"
            ]

group75 :: Case
group75 =
    Case
        "expected75"
        [ TestExpr "ARG|REFL|SIB+NEST-COND+PAYLOAD-REUSE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \g f b c -> f (g (if b then c else False)) (if b then c else False)
        , TestExpr "ARG|REFL|SIB+NEST-COND+PAYLOAD-REUSE|LET+ID|expr3" $
            withoutCallStack $ guess $ \g f b c ->
                let z = if b then c else False
                 in f (if g z then True else False) z
        ]
        $ expr
            [ "\\g f b c ->"
            , "  f (g (if b then c else False)) (if b then c else False)"
            ]

group76 :: Case
group76 =
    Case
        "expected76"
        [ TestExpr "HOCTX|DIR|CAPTURE|LET|expr1" $
            withoutCallStack $ guess $ \u f g b ->
                let h = \x -> if b then f x else g x
                 in u h b
        , TestExpr "HOCTX|DIR|CAPTURE|ID|expr3" $
            withoutCallStack $ guess $
                \u f g b -> u (\x -> if (if b then True else False) then f x else g x) b
        ]
        $ expr
            [ "\\u f g b ->"
            , "  u (\\x -> if b then f x else g x) b"
            ]

group77 :: Case
group77 =
    Case
        "expected77"
        [ TestExpr "ARG|COMP|NEST-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f g h x a b c ->
                    f (if g (h x) then (if g (h x) then a else b) else c)
        ]
        $ expr
            [ "\\f g h x a b c ->"
            , "  f"
            , "    (if g (h x) then if g (h x) then a else b else c)"
            ]

group78 :: Case
group78 =
    Case
        "expected78"
        [ TestExpr "HOCTX|DIR|CAPTURE+NEST-COND|LET|expr1" $
            withoutCallStack $ guess $ \u g b x ->
                let k = \f y -> if f (if b then y else False) then True else False
                 in u k g x
        ]
        $ expr
            [ "\\u g b x ->"
            , "  u (\\f y -> f (if b then y else False)) g x"
            ]

group79 :: Case
group79 =
    Case
        "expected79"
        [ TestExpr "ARG|HOBOOL|SIB|PLAIN|expr1" $
            withoutCallStack $ guess $ \u h f x a b c d ->
                f (if u h x then a else b) (if u h x then c else d)
        ]
        $ expr
            [ "\\u h f x a b c d ->"
            , "  f"
            , "    (if u h x then a else b)"
            , "    (if u h x then c else d)"
            ]

group80 :: Case
group80 =
    Case
        "expected80"
        [ TestExpr "ARG|CHOOSE1|SIB|PLAIN|expr1" $
            withoutCallStack $ guess $ \g h f b x a c d e ->
                f
                    (if (if b then g else h) x then a else c)
                    (if (if b then g else h) x then d else e)
        ]
        $ expr
            [ "\\g h f b x a c d e ->"
            , "  f"
            , "    (if b then if g x then a else c else if h x then a else c)"
            , "    (if b then if g x then d else e else if h x then d else e)"
            ]

group81 :: Case
group81 =
    Case
        "expected81"
        [ TestExpr "ARG|CHOOSEHO|SIB|PLAIN|expr1" $
            withoutCallStack $ guess $ \u v h f b x a c d e ->
                f
                    (if (if b then u else v) h x then a else c)
                    (if (if b then u else v) h x then d else e)
        ]
        $ expr
            [ "\\u v h f b x a c d e ->"
            , "  f"
            , "    (if b then if u h x then a else c else if v h x then a else c)"
            , "    (if b then if u h x then d else e else if v h x then d else e)"
            ]

group82 :: Case
group82 =
    Case
        "expected82"
        [ TestExpr "ARG|DIR|SIB+PAYLOAD-REUSE|LET|expr1" $
            withoutCallStack $ guess $ \f b c ->
                let z = b
                 in f (if z then c else False) z
        , TestExpr "ARG|DIR|SIB+PAYLOAD-REUSE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \f b c -> f (if b then c else False) b
        ]
        $ expr
            [ "\\f b c ->"
            , "  f (if b then c else False) b"
            ]

group83 :: Case
group83 =
    Case
        "expected83"
        [ TestExpr "TOP|COMP|BASE|ID|expr1" $
            withoutCallStack $ guess $
                \g h x -> if g (h x) then True else False
        , TestExpr "TOP|COMP|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \g h x -> g (h x)
        ]
        $ expr
            [ "\\g h x ->"
            , "  g (h x)"
            ]

group84 :: Case
group84 =
    Case
        "expected84"
        [ TestExpr "TOP|CHOOSE1|BASE|ID|expr1" $
            withoutCallStack $ guess $
                \g h b x -> if (if b then g else h) x then True else False
        , TestExpr "TOP|CHOOSE1|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \g h b x -> (if b then g else h) x
        ]
        $ expr
            [ "\\g h b x ->"
            , "  if b then g x else h x"
            ]

group85 :: Case
group85 =
    Case
        "expected85"
        [ TestExpr "TOP|COMP|CAPTURE|ID|expr1" $
            withoutCallStack $ guess $ \u g h b ->
                if u (\x -> if g (h b) then x else False) then True else False
        , TestExpr "TOP|COMP|CAPTURE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \u g h b -> u (\x -> if g (h b) then x else False)
        ]
        $ expr
            [ "\\u g h b ->"
            , "  u (\\x -> if g (h b) then x else False)"
            ]

group86 :: Case
group86 =
    Case
        "expected86"
        [ TestExpr "ARG|COMP|NEST-COND|ID|expr1" $
            withoutCallStack $ guess $
                \g h f x -> f (if (if g (h x) then True else False) then True else False)
        , TestExpr "ARG|COMP|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \g h f x -> f (g (h x))
        ]
        $ expr
            [ "\\g h f x ->"
            , "  f (g (h x))"
            ]

group87 :: Case
group87 =
    Case
        "expected87"
        [ TestExpr "FUN|COMP|NEST-COND|ID|expr1" $
            withoutCallStack $ guess $
                \f g h k x -> (if (if h (k x) then True else False) then f else g) x
        ]
        $ expr
            [ "\\f g h k x ->"
            , "  if h (k x) then f x else g x"
            ]

group88 :: Case
group88 =
    Case
        "expected88"
        [ TestExpr "TOP|CHOOSEHO|BASE|ID|expr1" $
            withoutCallStack $ guess $
                \u v h b x -> if (if b then u else v) h x then True else False
        , TestExpr "TOP|CHOOSEHO|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \u v h b x -> (if b then u else v) h x
        ]
        $ expr
            [ "\\u v h b x ->"
            , "  if b then u h x else v h x"
            ]

group89 :: Case
group89 =
    Case
        "expected89"
        [ TestExpr "FUN|MIXED-COND|BASE|ID|expr1" $
            withoutCallStack $ guess $
                \g f h a b c x ->
                    (if (if (if g a then g b else g c) then True else False) then f else h) x
        , TestExpr "FUN|MIXED-COND|BASE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \g f h a b c x -> (if (if g a then g b else g c) then f else h) x
        ]
        $ expr
            [ "\\g f h a b c x ->"
            , "  if g a"
            , "    then if g b then f x else h x"
            , "    else if g c then f x else h x"
            ]

group90 :: Case
group90 =
    Case
        "expected90"
        [ TestExpr "BOTH|MIXED-COND|FUN+ARG-SHARED|ID|expr1" $
            withoutCallStack $ guess $
                \g f h a b c x y ->
                    (if (if (if g a then g b else g c) then True else False) then f else h)
                        (if (if g a then g b else g c) then x else y)
        , TestExpr "BOTH|MIXED-COND|FUN+ARG-SHARED|PLAIN|expr2" $
            withoutCallStack $ guess $
                \g f h a b c x y ->
                    (if (if g a then g b else g c) then f else h)
                        (if (if g a then g b else g c) then x else y)
        ]
        $ expr
            [ "\\g f h a b c x y ->"
            , "  if g a"
            , "    then if g b"
            , "      then f"
            , "      (if g a"
            , "        then if g b then x else y"
            , "        else if g c then x else y)"
            , "      else h"
            , "      (if g a"
            , "        then if g b then x else y"
            , "        else if g c then x else y)"
            , "    else if g c"
            , "      then f"
            , "      (if g a"
            , "        then if g b then x else y"
            , "        else if g c then x else y)"
            , "      else h"
            , "      (if g a"
            , "        then if g b then x else y"
            , "        else if g c then x else y)"
            ]

group91 :: Case
group91 =
    Case
        "expected91"
        [ TestExpr "HOCTX|COMP|CAPTURE|ID|expr1" $
            withoutCallStack $ guess $
                \u g h x ->
                    if u (\y -> if g (h y) then True else False) x then True else False
        , TestExpr "HOCTX|COMP|CAPTURE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \u g h x -> u (\y -> g (h y)) x
        ]
        $ expr
            [ "\\u g h x ->"
            , "  u (\\y -> g (h y)) x"
            ]

group92 :: Case
group92 =
    Case
        "expected92"
        [ TestExpr "HOCTX|CHOOSE1|CAPTURE|ID|expr1" $
            withoutCallStack $ guess $
                \u f g b x ->
                    if u (\y -> if (if b then f else g) y then True else False) x
                        then True
                        else False
        , TestExpr "HOCTX|CHOOSE1|CAPTURE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \u f g b x -> u (\y -> (if b then f else g) y) x
        ]
        $ expr
            [ "\\u f g b x ->"
            , "  u (\\y -> if b then f y else g y) x"
            ]

group93 :: Case
group93 =
    Case
        "expected93"
        [ TestExpr "HOCTX|CHOOSEHO|CAPTURE|ID|expr1" $
            withoutCallStack $ guess $
                \u v w h b x ->
                    if u (\y -> if (if b then v else w) h y then True else False) x
                        then True
                        else False
        , TestExpr "HOCTX|CHOOSEHO|CAPTURE|PLAIN|expr2" $
            withoutCallStack $ guess $
                \u v w h b x -> u (\y -> (if b then v else w) h y) x
        ]
        $ expr
            [ "\\u v w h b x ->"
            , "  u (\\y -> if b then v h y else w h y) x"
            ]

group94 :: Case
group94 =
    Case
        "expected94"
        [ TestExpr "ARG|MIXED-COND+COMP|NEST-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g x a ->
                if a
                    then (if f x then True else False)
                    else g (f x)
        ]
        $ expr
            [ "\\f g x a ->"
            , "  if a"
            , "     then f x"
            , "     else g (f x)"
            ]

group94b :: Case
group94b =
    Case
        "expected94b"
        [ TestExpr "ARG|MIXED-COND+COMP|NEST-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h x a b c ->
                h
                    ( if g (f x)
                        then if f x then a else b
                        else if g (f x) then c else b
                    )
        ]
        $ expr
            [ "\\f g h x a b c ->"
            , "  h"
            , "    (if g (f x)"
            , "       then if f x then a else b"
            , "       else if g (f x) then c else b)"
            ]

group95 :: Case
group95 =
    Case
        "expected95"
        [ TestExpr "ARG|MIXED-COND+COMP|NEST-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g x a ->
                if a
                    then g (f x)
                    else (if f x then True else False)
        ]
        $ expr
            [ "\\f g x a ->"
            , "  if a"
            , "     then g (f x)"
            , "     else f x"
            ]

group95b :: Case
group95b =
    Case
        "expected95b"
        [ TestExpr "ARG|MIXED-COND+COMP|NEST-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h x a b c ->
                h
                    ( if g (f x)
                        then if g (f x) then c else b
                        else if f x then a else b
                    )
        ]
        $ expr
            [ "\\f g h x a b c ->"
            , "  h"
            , "    (if g (f x)"
            , "       then if g (f x) then c else b"
            , "       else if f x then a else b)"
            ]

group96 :: Case
group96 =
    Case
        "expected96"
        [ TestExpr "ARG|DIR|SIB+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \f p a b c d e q ->
                f
                    (if p then a else b)
                    (if p then c else d)
                    (if p then e else q)
        ]
        $ expr
            [ "\\f p a b c d e q ->"
            , "  f"
            , "    (if p then a else b)"
            , "    (if p then c else d)"
            , "    (if p then e else q)"
            ]

group97 :: Case
group97 =
    Case
        "expected97"
        [ TestExpr "ARG|COMP|SIB+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g x a b c d e q ->
                f
                    (if g x then a else b)
                    (if g x then c else d)
                    (if g x then e else q)
        ]
        $ expr
            [ "\\f g x a b c d e q ->"
            , "  f"
            , "    (if g x then a else b)"
            , "    (if g x then c else d)"
            , "    (if g x then e else q)"
            ]

group98 :: Case
group98 =
    Case
        "expected98"
        [ TestExpr "ARG|COMP|SIB|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h k x y z a b c d e q ->
                f
                    (if g x then a else b)
                    (if h y then c else d)
                    (if k z then e else q)
        ]
        $ expr
            [ "\\f g h k x y z a b c d e q ->"
            , "  f"
            , "    (if g x then a else b)"
            , "    (if h y then c else d)"
            , "    (if k z then e else q)"
            ]

group99 :: Case
group99 =
    Case
        "expected99"
        [ TestExpr "FUN|COMP|FUN+ARG-SHARED|PLAIN|expr1" $
            withoutCallStack $ guess $ \f k g h x y ->
                (if g (h x) then f else k) (if g (h x) then x else y)
        ]
        $ expr
            [ "\\f k g h x y ->"
            , "  if g (h x)"
            , "    then f (if g (h x) then x else y)"
            , "    else k (if g (h x) then x else y)"
            ]

group100 :: Case
group100 =
    Case
        "expected100"
        [ TestExpr "TOP|MIXED-COND+COMP|NEST-COND|ID|expr1" $
            withoutCallStack $ guess $ \g h k x y z ->
                if (if g x then h y else k z) then True else False
        ]
        $ expr
            [ "\\g h k x y z ->"
            , "  if g x then h y else k z"
            ]

group101 :: Case
group101 =
    Case
        "expected101"
        [ TestExpr "HOCTX|COMP|CAPTURE+NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \u f g h x ->
                u (\y -> if g (h y) then f y else x) x
        ]
        $ expr
            [ "\\u f g h x ->"
            , "  u (\\y -> if g (h y) then f y else x) x"
            ]

group102 :: Case
group102 =
    Case
        "expected102"
        [ TestExpr "ARG|CHOOSE1+COMP|SIB|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h p x y z a b c d e q ->
                f
                    (if (if p then g else h) x then a else b)
                    (if (if p then g else h) y then c else d)
                    (if (if p then g else h) z then e else q)
        ]
        $ expr
            [ "\\f g h p x y z a b c d e q ->"
            , "  f"
            , "    (if p then if g x then a else b else if h x then a else b)"
            , "    (if p then if g y then c else d else if h y then c else d)"
            , "    (if p then if g z then e else q else if h z then e else q)"
            ]

group103 :: Case
group103 =
    Case
        "expected103"
        [ TestExpr "BOTH|MIXED-COND+COMP|FUN+ARG-SHARED|PLAIN|expr1" $
            withoutCallStack $ guess $ \g f h a b c x y ->
                (if if g a then g b else g c then f else h)
                    (if if g a then g b else g c then x else y)
        ]
        $ expr
            [ "\\g f h a b c x y ->"
            , "  if g a"
            , "    then if g b"
            , "      then f (if g a then if g b then x else y else if g c then x else y)"
            , "      else h (if g a then if g b then x else y else if g c then x else y)"
            , "    else if g c"
            , "      then f (if g a then if g b then x else y else if g c then x else y)"
            , "      else h (if g a then if g b then x else y else if g c then x else y)"
            ]

group104 :: Case
group104 =
    Case
        "expected104"
        [ TestExpr "HOCTX|DIR|CAPTURE+NEST-COND|LET|expr1" $
            withoutCallStack $ guess $ \u f p x ->
                let k = \g y -> if g (if p then y else x) then True else False
                 in u k f x
        ]
        $ expr
            [ "\\u f p x ->"
            , "  u (\\g y -> g (if p then y else x)) f x"
            ]

group105 :: Case
group105 =
    Case
        "expected105"
        [ TestExpr "ARG|REFL|SIB+NEST-COND+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \g f p x a c d ->
                f
                    (g (if p then x else a))
                    (if g (if p then x else a) then c else d)
        ]
        $ expr
            [ "\\g f p x a c d ->"
            , "  f"
            , "    (g (if p then x else a))"
            , "    (if g (if p then x else a) then c else d)"
            ]

group106 :: Case
group106 =
    Case
        "expected106"
        [ TestExpr "TOP|MIXED-COND|NEST-COND|ID|expr1" $
            withoutCallStack $ guess $ \a b c ->
                if (if a then b else c) then True else False
        ]
        $ expr
            [ "\\a b c ->"
            , "  if a then b else c"
            ]

group107 :: Case
group107 =
    Case
        "expected107"
        [ TestExpr "ARG|DIR|NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \f a b c ->
                f (if a then if b then c else a else if c then b else a)
        ]
        $ expr
            [ "\\f a b c ->"
            , "  f"
            , "    (if a then if b then c else True else if c then b else False)"
            ]

group108 :: Case
group108 =
    Case
        "expected108"
        [ TestExpr "FUN|MIXED-COND+COMP|NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h a b x ->
                (if if a then b else h x then f else g) x
        ]
        $ expr
            [ "\\f g h a b x ->"
            , "  if a then if b then f x else g x else if h x then f x else g x"
            ]

group109 :: Case
group109 =
    Case
        "expected109"
        [ TestExpr "HOCTX|DIR|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess $ \u f g a x ->
                u (\y -> (if a then f else g) y) x
        ]
        $ expr
            [ "\\u f g a x ->"
            , "  u (\\y -> if a then f y else g y) x"
            ]

group110 :: Case
group110 =
    Case
        "expected110"
        [ TestExpr "HOCTX|DIR|CAPTURE+NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \u f a b ->
                u (\x -> f (if a then x else b)) b
        ]
        $ expr
            [ "\\u f a b ->"
            , "  u (\\x -> f (if a then x else b)) b"
            ]

group111 :: Case
group111 =
    Case
        "expected111"
        [ TestExpr "BOTH|DIR|FUN+ARG-INDEP|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g a b c d ->
                (if a then f else g) (if b then c else d)
        ]
        $ expr
            [ "\\f g a b c d ->"
            , "  if a then f (if b then c else d) else g (if b then c else d)"
            ]

group112 :: Case
group112 =
    Case
        "expected112"
        [ TestExpr "BOTH|COMP|FUN+ARG-INDEP|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h k x y z ->
                (if h x then f else g) (if k y then x else z)
        ]
        $ expr
            [ "\\f g h k x y z ->"
            , "  if h x then f (if k y then x else z) else g (if k y then x else z)"
            ]

group113 :: Case
group113 =
    Case
        "expected113"
        [ TestExpr "ARG|REFL|SIB+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \g f x y ->
                f (g x) (if g x then y else x) (if g x then x else y)
        ]
        $ expr
            [ "\\g f x y ->"
            , "  f (g x) (if g x then y else x) (if g x then x else y)"
            ]

group114 :: Case
group114 =
    Case
        "expected114"
        [ TestExpr "TOP|REFL|APP-NEST|ID|expr1" $
            withoutCallStack $ guess $ \g h x ->
                if g (h (g x)) then True else False
        ]
        $ expr
            [ "\\g h x ->"
            , "  g (h (g x))"
            ]

group115 :: Case
group115 =
    Case
        "expected115"
        [ TestExpr "ARG|CHOOSEHO|SIB|PLAIN|expr1" $
            withoutCallStack $ guess $ \u v h f p x a b c d ->
                f
                    (if (if p then u else v) h x then a else b)
                    (if u h x then c else d)
        ]
        $ expr
            [ "\\u v h f p x a b c d ->"
            , "  f"
            , "    (if p then if u h x then a else b else if v h x then a else b)"
            , "    (if u h x then c else d)"
            ]

group116 :: Case
group116 =
    Case
        "expected116"
        [ TestExpr "HOCTX|CHOOSE1|CAPTURE+NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \u f g p x ->
                u (\y -> if (if p then f else g) y then x else y) x
        ]
        $ expr
            [ "\\u f g p x ->"
            , "  u (\\y -> if p then if f y then x else y else if g y then x else y) x"
            ]

group117 :: Case
group117 =
    Case
        "expected117"
        [ TestExpr "FUN|DIR|NEST-BR|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h a b x ->
                (if a then if b then f else g else h) x
        ]
        $ expr
            [ "\\f g h a b x ->"
            , "  if a then if b then f x else g x else h x"
            ]

group118 :: Case
group118 =
    Case
        "expected118"
        [ TestExpr "ARG|COMP|NEST-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h x a b c ->
                f (if g (h x) then if h x then a else b else if g x then b else c)
        ]
        $ expr
            [ "\\f g h x a b c ->"
            , "  f"
            , "    (if g (h x) then if h x then a else b else if g x then b else c)"
            ]

group119 :: Case
group119 =
    Case
        "expected119"
        [ TestExpr "BOTH|DIR|FUN+ARG-SHARED|LET|expr1" $
            withoutCallStack $ guess $ \f g a x y ->
                let z = if a then x else y
                 in (if a then f else g) z
        ]
        $ expr
            [ "\\f g a x y ->"
            , "  if a then f x else g y"
            ]

group120 :: Case
group120 =
    Case
        "expected120"
        [ TestExpr "TOP|CHOOSE1+COMP|BASE|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g p x ->
                (if p then f else g) ((if p then f else g) x)
        ]
        $ expr
            [ "\\f g p x ->"
            , "  if p then f (f x) else g (g x)"
            ]

group121 :: Case
group121 =
    Case
        "expected121"
        [ TestExpr "ARG|MIXED-COND|SIB+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \f a b c d e ->
                f
                    (if if a then b else c then d else e)
                    (if if a then b else c then e else d)
        ]
        $ expr
            [ "\\f a b c d e ->"
            , "  f"
            , "    (if a then if b then d else e else if c then d else e)"
            , "    (if a then if b then e else d else if c then e else d)"
            ]

group122 :: Case
group122 =
    Case
        "expected122"
        [ TestExpr "HOCTX|REFL|CAPTURE+NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \u g x ->
                u (\y -> if g y then g x else y) x
        ]
        $ expr
            [ "\\u g x ->"
            , "  u (\\y -> if g y then g x else y) x"
            ]

group123 :: Case
group123 =
    Case
        "expected123"
        [ TestExpr "FUN|REFL|NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h x ->
                (if if h x then h (g x) else h x then f else g) x
        ]
        $ expr
            [ "\\f g h x ->"
            , "  if h x then if h (g x) then f x else g x else if h x then f x else g x"
            ]

group124 :: Case
group124 =
    Case
        "expected124"
        [ TestExpr "ARG|HOBOOL|NEST-COND+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \u h f x a b c ->
                f (if u h x then if h x then a else b else c)
        ]
        $ expr
            [ "\\u h f x a b c ->"
            , "  f"
            , "    (if u (\\x -> h x) x then if h x then a else b else c)"
            ]

group125 :: Case
group125 =
    Case
        "expected125"
        [ TestExpr "BOTH|CHOOSEHO|FUN+ARG-INDEP|PLAIN|expr1" $
            withoutCallStack $ guess $ \u v h f g p x y ->
                (if (if p then u else v) h x then f else g)
                    (if u h y then x else y)
        ]
        $ expr
            [ "\\u v h f g p x y ->"
            , "  if p"
            , "    then if u h x then f (if u h y then x else y)"
            , "      else g (if u h y then x else y)"
            , "    else if v h x then f (if u h y then x else y)"
            , "      else g (if u h y then x else y)"
            ]

group126 :: Case
group126 =
    Case
        "expected126"
        [ TestExpr "ARG|DIR|NEST-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \f a b c d ->
                f (if a then if b then c else d else if b then d else c)
        ]
        $ expr
            [ "\\f a b c d ->"
            , "  f (if a then if b then c else d else if b then d else c)"
            ]

group127 :: Case
group127 =
    Case
        "expected127"
        [ TestExpr "TOP|CHOOSE1+COMP|APP-NEST|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g p x ->
                if (if p then f else g) ((if p then g else f) x) then True else False
        ]
        $ expr
            [ "\\f g p x ->"
            , "  if p then f (g x) else g (f x)"
            ]

group128 :: Case
group128 =
    Case
        "expected128"
        [ TestExpr "HOCTX|DIR|CAPTURE+NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \u f g a b ->
                u (\x -> (if a then f else g) (if b then x else a)) b
        ]
        $ expr
            [ "\\u f g a b ->"
            , "  u (\\x -> if a then f (if b then x else True)"
            , "             else g (if b then x else False)) b"
            ]

group129 :: Case
group129 =
    Case
        "expected129"
        [ TestExpr "BOTH|REFL|FUN+ARG-INDEP|PLAIN|expr1" $
            withoutCallStack $ guess $ \h f g x y ->
                (if h x then f else g) (if h y then x else y)
        ]
        $ expr
            [ "\\h f g x y ->"
            , "  if h x then f (if h y then x else y) else g (if h y then x else y)"
            ]

group130 :: Case
group130 =
    Case
        "expected130"
        [ TestExpr "ARG|MIXED-COND+COMP|NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h x y z ->
                f (if g x then h (if g y then x else z) else h y)
        ]
        $ expr
            [ "\\f g h x y z ->"
            , "  f (if g x then h (if g y then x else z) else h y)"
            ]

group131 :: Case
group131 =
    Case
        "expected131"
        [ TestExpr "FUN|CHOOSE1+COMP|NEST-BR|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h k p q x ->
                (if p then if q then f else g else if h x then k else f) x
        ]
        $ expr
            [ "\\f g h k p q x ->"
            , "  if p then if q then f x else g x else if h x then k x else f x"
            ]

group132 :: Case
group132 =
    Case
        "expected132"
        [ TestExpr "ARG|REFL|SIB+APP-NEST|PLAIN|expr1" $
            withoutCallStack $ guess $ \g f x ->
                f (g (g x)) (if g x then g (g x) else x)
        ]
        $ expr
            [ "\\g f x ->"
            , "  f (g (g x)) (if g x then g (g x) else x)"
            ]

group133 :: Case
group133 =
    Case
        "expected133"
        [ TestExpr "HOCTX|REFL|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess $ \u g f x ->
                u (\y -> f (if g x then y else g y)) x
        ]
        $ expr
            [ "\\u g f x ->"
            , "  u (\\y -> f (if g x then y else g y)) x"
            ]

group134 :: Case
group134 =
    Case
        "expected134"
        [ TestExpr "TOP|HOBOOL+CHOOSE1|NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \u h k p x ->
                if (if p then u h x else u k x) then True else False
        ]
        $ expr
            [ "\\u h k p x ->"
            , "  if p then u h x else u k x"
            ]

group135 :: Case
group135 =
    Case
        "expected135"
        [ TestExpr "ARG|CHOOSEHO|NEST-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \u v h f p x a b c ->
                f (if (if p then u else v) h x then if h x then a else b else c)
        ]
        $ expr
            [ "\\u v h f p x a b c ->"
            , "  f"
            , "    (if p"
            , "       then if u (\\x -> h x) x then if h x then a else b else c"
            , "       else if v (\\x -> h x) x then if h x then a else b else c)"
            ]

group136 :: Case
group136 =
    Case
        "expected136"
        [ TestExpr "BOTH|MIXED-COND|FUN+ARG-INDEP|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g a b c x y ->
                (if if a then b else c then f else g) (if a then x else y)
        ]
        $ expr
            [ "\\f g a b c x y ->"
            , "  if a"
            , "    then if b then f x else g x"
            , "    else if c then f y else g y"
            ]

group137 :: Case
group137 =
    Case
        "expected137"
        [ TestExpr "HOCTX|COMP|CAPTURE+NEST-COND|LET|expr1" $
            withoutCallStack $ guess $ \u g h x ->
                let k = \f y -> f (if g (h y) then h x else y)
                 in u k h x
        ]
        $ expr
            [ "\\u g h x ->"
            , "  u (\\f y -> f (if g (h y) then h x else y)) (\\x -> h x) x"
            ]

group138 :: Case
group138 =
    Case
        "expected138"
        [ TestExpr "ARG|COMP|SIB+NEST-COND+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \g h f x y a b ->
                f
                    (g (if h x then x else y))
                    (if g (if h x then x else y) then a else b)
        ]
        $ expr
            [ "\\g h f x y a b ->"
            , "  f"
            , "    (g (if h x then x else y))"
            , "    (if g (if h x then x else y) then a else b)"
            ]

group139 :: Case
group139 =
    Case
        "expected139"
        [ TestExpr "TOP|REFL|DUP-BR|PLAIN|expr1" $
            withoutCallStack $ guess $ \g x ->
                if g x then g x else g (if g x then x else False)
        ]
        $ expr
            [ "\\g x ->"
            , "  if g x then g x else g (if g x then x else False)"
            ]

group140 :: Case
group140 =
    Case
        "expected140"
        [ TestExpr "ARG|DIR|CAPTURE+NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \f a b ->
                f (\x -> if a then x else b) (if a then b else False)
        ]
        $ expr
            [ "\\f a b ->"
            , "  f (\\x -> if a then x else b) (if a then b else False)"
            ]

group141 :: Case
group141 =
    Case
        "expected141"
        [ TestExpr "FUN|HOBOOL|NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \u h f g x y ->
                (if u h (if h x then x else y) then f else g) x
        ]
        $ expr
            [ "\\u h f g x y ->"
            , "  if u (\\x -> h x) (if h x then x else y) then f x else g x"
            ]

group142 :: Case
group142 =
    Case
        "expected142"
        [ TestExpr "ARG|MIXED-COND+COMP|SIB|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h x y a b c d ->
                f
                    (if g x then a else b)
                    (if h (if g x then y else x) then c else d)
        ]
        $ expr
            [ "\\f g h x y a b c d ->"
            , "  f"
            , "    (if g x then a else b)"
            , "    (if h (if g x then y else x) then c else d)"
            ]

group143 :: Case
group143 =
    Case
        "expected143"
        [ TestExpr "BOTH|CHOOSE1+COMP|FUN+ARG-SHARED|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h k p x y ->
                (if (if p then h else k) x then f else g)
                    (if (if p then h else k) x then x else y)
        ]
        $ expr
            [ "\\f g h k p x y ->"
            , "  if p"
            , "    then if h x then f (if h x then x else y) else g (if h x then x else y)"
            , "    else if k x then f (if k x then x else y) else g (if k x then x else y)"
            ]

group144 :: Case
group144 =
    Case
        "expected144"
        [ TestExpr "HOCTX|MIXED-COND+COMP|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess $ \u g h x y ->
                u (\f -> f (if g x then h y else h x)) h
        ]
        $ expr
            [ "\\u g h x y ->"
            , "  u (\\f -> f (if g x then h y else h x)) (\\x -> h x)"
            ]

group145 :: Case
group145 =
    Case
        "expected145"
        [ TestExpr "ARG|REFL|NEST-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \g f x a b c ->
                f (if g x then if g (if g x then a else b) then a else b else c)
        ]
        $ expr
            [ "\\g f x a b c ->"
            , "  f"
            , "    (if g x then if g (if g x then a else b) then a else b else c)"
            ]

group146 :: Case
group146 =
    Case
        "expected146"
        [ TestExpr "TOP|DIR|CAPTURE+NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \a f g x ->
                (if a then \y -> f (if a then y else False) else \y -> g y) x
        ]
        $ expr
            [ "\\a f g x ->"
            , "  if a then f x else g x"
            ]

group147 :: Case
group147 =
    Case
        "expected147"
        [ TestExpr "TOP|REFL|CAPTURE+NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \g a x ->
                (\y -> if g (if a then y else False) then y else a) x
        ]
        $ expr
            [ "\\g a x ->"
            , "  if g (if a then x else False) then x else a"
            ]

group148 :: Case
group148 =
    Case
        "expected148"
        [ TestExpr "HOCTX|DIR|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess $ \u f g a x ->
                u (if a then \h y -> h (f y) else \h y -> h (g y)) f x
        ]
        $ expr
            [ "\\u f g a x ->"
            , "  u (\\h y -> if a then h (f y) else h (g y)) (\\x -> f x) x"
            ]

group149 :: Case
group149 =
    Case
        "expected149"
        [ TestExpr "TOP|REFL|APP-NEST|PLAIN|expr1" $
            withoutCallStack $ guess $ \g x a b ->
                let k = \h y -> h (h y)
                 in if k g x then a else b
        ]
        $ expr
            [ "\\g x a b ->"
            , "  if g (g x) then a else b"
            ]

group150 :: Case
group150 =
    Case
        "expected150"
        [ TestExpr "BOTH|HOBOOL|FUN+ARG-SHARED|PLAIN|expr1" $
            withoutCallStack $ guess $ \u h f g x y ->
                (if u h x then f else g) (if u (\z -> h z) x then x else y)
        ]
        $ expr
            [ "\\u h f g x y ->"
            , "  if u (\\x -> h x) x"
            , "    then f (if u (\\z -> h z) x then x else y)"
            , "    else g (if u (\\z -> h z) x then x else y)"
            ]

group151 :: Case
group151 =
    Case
        "expected151"
        [ TestExpr "ARG|MIXED-COND|SIB+PAYLOAD-REUSE|LET|expr1" $
            withoutCallStack $ guess $ \f a b c d e ->
                let left = if a then b else c
                    right = if a then d else e
                 in f (if left then right else b) (if right then left else c)
        ]
        $ expr
            [ "\\f a b c d e ->"
            , "  f"
            , "    (if a then if b then d else False else if c then e else b)"
            , "    (if a then if d then b else c else if e then c else c)"
            ]

group152 :: Case
group152 =
    Case
        "expected152"
        [ TestExpr "BOTH|CHOOSE1|FUN+ARG-INDEP|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h k a b c x y ->
                (if a then f else g) ((if b then h else k) (if c then x else y))
        ]
        $ expr
            [ "\\f g h k a b c x y ->"
            , "  if a"
            , "    then f (if b then h (if c then x else y) else k (if c then x else y))"
            , "    else g (if b then h (if c then x else y) else k (if c then x else y))"
            ]

group153 :: Case
group153 =
    Case
        "expected153"
        [ TestExpr "TOP|DIR|NEST-COND|LET|expr1" $
            withoutCallStack $ guess $ \a b c ->
                let k = \x -> x
                    z = if a then k b else k c
                 in z
        ]
        $ expr
            [ "\\a b c ->"
            , "  if a then b else c"
            ]

group154 :: Case
group154 =
    Case
        "expected154"
        [ TestExpr "HOCTX|DIR|CAPTURE+NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \u f g a b x ->
                u (\y -> if a then f (if b then y else x) else g (if b then x else y)) x
        ]
        $ expr
            [ "\\u f g a b x ->"
            , "  u"
            , "    (\\y -> if a then f (if b then y else x) else g (if b then x else y))"
            , "    x"
            ]

group155 :: Case
group155 =
    Case
        "expected155"
        [ TestExpr "TOP|CHOOSEHO+CHOOSE1|BASE|PLAIN|expr1" $
            withoutCallStack $ guess $ \u v f g a b x ->
                (if a then u else v) (if b then f else g) x
        ]
        $ expr
            [ "\\u v f g a b x ->"
            , "  if a then u (if b then f else g) x else v (if b then f else g) x"
            ]

group156 :: Case
group156 =
    Case
        "expected156"
        [ TestExpr "ARG|COMP|APP-NEST+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g h x y ->
                f (g (h (g (if h x then x else y))))
        ]
        $ expr
            [ "\\f g h x y ->"
            , "  f (g (h (g (if h x then x else y))))"
            ]

group157 :: Case
group157 =
    Case
        "expected157"
        [ TestExpr "TOP|MIXED-COND+COMP|NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $ \g h x a ->
                if a then True else g (h x)
        ]
        $ expr
            [ "\\g h x a ->"
            , "  if a then True else g (h x)"
            ]

group158 :: Case
group158 =
    Case
        "expected158"
        [ TestExpr "ARG|COMP|SIB+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \f g x y a b ->
                f (g (if a then x else y)) (g (if b then y else x))
        ]
        $ expr
            [ "\\f g x y a b ->"
            , "  f (g (if a then x else y)) (g (if b then y else x))"
            ]

group159 :: Case
group159 =
    Case
        "expected159"
        [ TestExpr "FUN|DIR|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess $ \a f g x ->
                (if a then \y -> f y else \y -> g (if a then y else x)) x
        ]
        $ expr
            [ "\\a f g x ->"
            , "  if a then f x else g x"
            ]

group160 :: Case
group160 =
    Case
        "expected160"
        [ TestExpr "ARG|MIXED-COND+REFL|NEST-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \g h f a x y z ->
                f (if a then g x else if h y then g z else h x)
        ]
        $ expr
            [ "\\g h f a x y z ->"
            , "  f (if a then g x else if h y then g z else h x)"
            ]

group161 :: Case
group161 =
    Case
        "expected161"
        [ TestExpr "ARG|NONE|APP-NEST|PLAIN|expr1" $
            withoutCallStack $ guess $ \f x -> f (f (f x))
        ]
        $ expr
            [ "\\f x ->"
            , "  f (f (f x))"
            ]

group162 :: Case
group162 =
    Case
        "expected162"
        [ TestExpr "TOP|REFL|DUP-BR+PAYLOAD-REUSE|LET|expr1" $
            withoutCallStack $ guess $ \g f x -> let y = f x in if y then g y else g y
        ]
        $ expr
            [ "\\g f x ->"
            , "  if f x then g True else g False"
            ]

group163 :: Case
group163 =
    Case
        "expected163"
        [ TestExpr "TOP|REFL|DUP-BR|PLAIN|expr1" $
            withoutCallStack $ guess $
                \f b -> if f b then f else f
        , TestExpr "TOP|REFL|DUP-BR|ID|expr2" $
            withoutCallStack $ guess $
                \f b -> if f b then (\x -> f x) else f
        ]
        $ expr
            [ "\\f b x ->"
            , "  if f b then f x else f x"
            ]

group164 :: Case
group164 =
    Case
        "expected164"
        [ TestExpr "HOCTX|HOBOOL|CAPTURE+NEST-COND|PLAIN|expr1" $
            withoutCallStack $ guess $
                \v u h f g x ->
                    v (\y -> if u h y then f y else g y) x
        ]
        $ expr
            [ "\\v u h f g x ->"
            , "  v (\\y -> if u h y then f y else g y) x"
            ]

group165 :: Case
group165 =
    Case
        "expected165"
        [ TestExpr "TOP|REFL|NEST-BR+PAYLOAD-REUSE|BETA|expr1" $
            withoutCallStack $ guess $ \g f x a b ->
                (\y -> if y then if y then g y else a else b) (f x)
        ]
        $ expr
            [ "\\g f x a b ->"
            , "  if f x then g True else b"
            ]

group166 :: Case
group166 =
    Case
        "expected166"
        [ TestExpr "TOP|REFL|NEST-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \g f x a b ->
                if f x then if f x then g (f x) else a else b
        ]
        $ expr
            [ "\\g f x a b ->"
            , "  if f x then if f x then g (f x) else a else b"
            ]

group167 :: Case
group167 =
    Case
        "expected167"
        [ TestExpr "ARG|REFL|DUP-BR+PAYLOAD-REUSE|BETA|expr1" $
            withoutCallStack $ guess $ \h g f x ->
                h ((\y -> if y then g y else g y) (f x))
        ]
        $ expr
            [ "\\h g f x ->"
            , "  h (if f x then g True else g False)"
            ]

group168 :: Case
group168 =
    Case
        "expected168"
        [ TestExpr "ARG|REFL|DUP-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \h g f x ->
                h (if f x then g (f x) else g (f x))
        ]
        $ expr
            [ "\\h g f x ->"
            , "  h (if f x then g (f x) else g (f x))"
            ]

group169 :: Case
group169 =
    Case
        "expected169"
        [ TestExpr "HOCTX|REFL|CAPTURE+DUP-BR+PAYLOAD-REUSE|BETA|expr1" $
            withoutCallStack $ guess $ \h g f x ->
                (\y -> h (\z -> if y then g y z else g y z)) (f x)
        ]
        $ expr
            [ "\\h g f x ->"
            , "  h (\\z -> if f x then g True z else g False z)"
            ]

group170 :: Case
group170 =
    Case
        "expected170"
        [ TestExpr "HOCTX|REFL|CAPTURE+DUP-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \h g f x ->
                h (\z -> if f x then g (f x) z else g (f x) z)
        ]
        $ expr
            [ "\\h g f x ->"
            , "  h (\\z -> if f x then g (f x) z else g (f x) z)"
            ]

group171 :: Case
group171 =
    Case
        "expected171"
        [ TestExpr "ARG|DIR|SIB+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \g a b ->
                g a b (if a then b else a)
        , TestExpr "ARG|DIR|SIB+NEST-BR+PAYLOAD-REUSE|PLAIN|expr2" $
            withoutCallStack $ guess $ \g a b ->
                g a b (if a then (if b then a else b) else a)
        ]
        $ expr
            [ "\\g a b ->"
            , "  g a b (if a then b else False)"
            ]

group172 :: Case
group172 =
    Case
        "expected172"
        [ TestExpr "ARG|DIR|SIB+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \g a b ->
                g a b (if a then a else b)
        ]
        $ expr
            [ "\\g a b ->"
            , "  g a b (if a then True else b)"
            ]

group173 :: Case
group173 =
    Case
        "expected173"
        [ TestExpr "ARG|DIR|SIB+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \g a b ->
                g a b (if b then b else a)
        ]
        $ expr
            [ "\\g a b ->"
            , "  g a b (if b then True else a)"
            ]

group174 :: Case
group174 =
    Case
        "expected174"
        [ TestExpr "ARG|DIR|SIB+DUP-BR+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \g a b ->
                g a b (if a then b else a) (if a then b else a)
        ]
        $ expr
            [ "\\g a b ->"
            , "  g a b (if a then b else False) (if a then b else False)"
            ]

group175 :: Case
group175 =
    Case
        "expected175"
        [ TestExpr "ARG|DIR|SIB+PAYLOAD-REUSE|PLAIN|expr1" $
            withoutCallStack $ guess $ \g a b ->
                g a (if a then b else a) b
        ]
        $ expr
            [ "\\g a b ->"
            , "  g a (if a then b else False) b"
            ]

group176 :: Case
group176 =
    Case
        "expected176"
        [ TestExpr "ARG|DIR|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g a b (if a then b else a))
                    :: (Bool->Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 x1 x2 (if x1 then x2 else False)"
            ]

group177 :: Case
group177 =
    Case
        "expected177"
        [ TestExpr "ARG|DIR|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g (if a then b else a) (if b then a else b))
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then x2 else False) (if x2 then x1 else False)"
            ]

group178 :: Case
group178 =
    Case
        "expected178"
        [ TestExpr "ARG|DIR|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b c -> g (if a then b else c) (if a then c else b))
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x0 (if x1 then x2 else x3) (if x1 then x3 else x2)"
            ]

group179 :: Case
group179 =
    Case
        "expected179"
        [ TestExpr "ARG|DIR|BASE|LET|expr1" $
            withoutCallStack $ guess
                ((\g a b -> let y = if a then b else a in g y y)
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then x2 else False) (if x1 then x2 else False)"
            ]

group180 :: Case
group180 =
    Case
        "expected180"
        [ TestExpr "ARG|REFL|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g a b -> g (f a) (if f a then b else a))
                    :: (Bool->Bool) -> (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x1 (x0 x2) (if x0 x2 then x3 else x2)"
            ]

group181 :: Case
group181 =
    Case
        "expected181"
        [ TestExpr "ARG|REFL|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g a -> g (f a) (f (f a)))
                    :: (Bool->Bool) -> (Bool->Bool->Bool) -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x1 (x0 x2) (x0 (x0 x2))"
            ]

group182 :: Case
group182 =
    Case
        "expected182"
        [ TestExpr "ARG|DIR|NEST-BR+SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b c -> g (if a then (if b then c else a) else b) (if c then a else b))
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x0"
            , "  (if x1 then if x2 then x3 else True else x2)"
            , "  (if x3 then x1 else x2)"
            ]

group183 :: Case
group183 =
    Case
        "expected183"
        [ TestExpr "ARG|REFL|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g a b -> g (if f a then b else a) (if f b then a else b))
                    :: (Bool->Bool) -> (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x1 (if x0 x2 then x3 else x2) (if x0 x3 then x2 else x3)"
            ]

group184 :: Case
group184 =
    Case
        "expected184"
        [ TestExpr "ARG|DIR|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g (if a then a else b) b (if b then b else a))
                    :: (Bool->Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then True else x2) x2 (if x2 then True else x1)"
            ]

group185 :: Case
group185 =
    Case
        "expected185"
        [ TestExpr "TOP|REFL|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f a -> if f a then f a else a)
                    :: (Bool->Bool) -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 -> if x0 x1 then x0 x1 else x1"
            ]

group186 :: Case
group186 =
    Case
        "expected186"
        [ TestExpr "ARG|REFL|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g a b -> g a (if a then f b else f a) b)
                    :: (Bool->Bool) -> (Bool->Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x1 x2 (if x2 then x0 x3 else x0 False) x3"
            ]

group187 :: Case
group187 =
    Case
        "expected187"
        [ TestExpr "ARG|DIR|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g (if a then b else False) a b)
                    :: (Bool->Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then x2 else False) x1 x2"
            ]

group188 :: Case
group188 =
    Case
        "expected188"
        [ TestExpr "ARG|DIR|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\h g a b -> h (g a b) (if a then g b a else b))
                    :: (Bool->Bool->Bool) -> (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x0 (x1 x2 x3) (if x2 then x1 x3 True else x3)"
            ]

group189 :: Case
group189 =
    Case
        "expected189"
        [ TestExpr "ARG|DIR|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f a b -> f (if a then b else a) (if b then a else b) (if a then a else b))
                    :: (Bool->Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0"
            , "  (if x1 then x2 else False)"
            , "  (if x2 then x1 else False)"
            , "  (if x1 then True else x2)"
            ]

group190 :: Case
group190 =
    Case
        "expected190"
        [ TestExpr "ARG|DIR|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a -> g (if a then True else False) a)
                    :: (Bool->Bool->Bool) -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 -> x0 x1 x1"
            ]

group191 :: Case
group191 =
    Case
        "expected191"
        [ TestExpr "TOP|REFL|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g a b -> if f a then g a b else g b a)
                    :: (Bool->Bool) -> (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> if x0 x2 then x1 x2 x3 else x1 x3 x2"
            ]

group192 :: Case
group192 =
    Case
        "expected192"
        [ TestExpr "ARG|REFL|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g a b -> g (if a then b else a) (f (if b then a else b)))
                    :: (Bool->Bool) -> (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x1 (if x2 then x3 else False) (x0 (if x3 then x2 else False))"
            ]

group193 :: Case
group193 =
    Case
        "expected193"
        [ TestExpr "ARG|DIR|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b c -> g c (if a then b else c) (if b then c else a) a)
                    :: (Bool->Bool->Bool->Bool->Bool) -> Bool -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x0 x3 (if x1 then x2 else x3) (if x2 then x3 else x1) x1"
            ]

group194 :: Case
group194 =
    Case
        "expected194"
        [ TestExpr "TOP|REFL|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f a b -> if f (if a then b else a) then a else b)
                    :: (Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> if x0 (if x1 then x2 else False) then x1 else x2"
            ]

group195 :: Case
group195 =
    Case
        "expected195"
        [ TestExpr "ARG|DIR|NEST-BR+SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g (if a then (if a then b else a) else b) a)
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then x2 else x2) x1"
            ]

group196 :: Case
group196 =
    Case
        "expected196"
        [ TestExpr "HOCTX|HOBOOL+REFL|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a -> g (\x -> if a then x else a))
                    :: ((Bool->Bool)->Bool) -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 -> x0 (\\x2 -> if x1 then x2 else False)"
            ]

group197 :: Case
group197 =
    Case
        "expected197"
        [ TestExpr "HOCTX|HOBOOL+REFL|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g (\x -> if x then a else b) (if a then b else a))
                    :: ((Bool->Bool)->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (\\x3 -> if x3 then x1 else x2) (if x1 then x2 else False)"
            ]

group198 :: Case
group198 =
    Case
        "expected198"
        [ TestExpr "HOCTX|DIR+HOBOOL|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a -> g (\x y -> if a then x else y))
                    :: ((Bool->Bool->Bool)->Bool) -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 -> x0 (\\x2 x3 -> if x1 then x2 else x3)"
            ]

group199 :: Case
group199 =
    Case
        "expected199"
        [ TestExpr "ARG|DIR|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g (if a then True else True) (if b then a else b))
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then True else True) (if x2 then x1 else False)"
            ]

group200 :: Case
group200 =
    Case
        "expected200"
        [ TestExpr "ARG|DIR|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g True (if a then b else a) False)
                    :: (Bool->Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 True (if x1 then x2 else False) False"
            ]

group201 :: Case
group201 =
    Case
        "expected201"
        [ TestExpr "HOCTX|HOBOOL+REFL|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g f a -> g (\x -> f (if a then x else a)))
                    :: ((Bool->Bool)->Bool) -> (Bool->Bool) -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (\\x3 -> x1 (if x2 then x3 else False))"
            ]

group202 :: Case
group202 =
    Case
        "expected202"
        [ TestExpr "ARG|REFL|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g a -> g (f (if a then a else a)) (f a))
                    :: (Bool->Bool) -> (Bool->Bool->Bool) -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x1 (x0 x2) (x0 x2)"
            ]

group203 :: Case
group203 =
    Case
        "expected203"
        [ TestExpr "ARG|DIR|NEST-COND+SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g (if (if a then b else a) then a else b) b)
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then x2 else x2) x2"
            ]

group204 :: Case
group204 =
    Case
        "expected204"
        [ TestExpr "HOCTX|HOBOOL+REFL|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a -> g (\x -> if a then x else a) (\y -> if a then a else y))
                    :: ((Bool->Bool)->(Bool->Bool)->Bool) -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 -> x0 (\\x2 -> if x1 then x2 else False) (\\x2 -> if x1 then True else x2)"
            ]

group205 :: Case
group205 =
    Case
        "expected205"
        [ TestExpr "ARG|DIR|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g (if a then b else a) (if a then b else a))
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then x2 else False) (if x1 then x2 else False)"
            ]

group206 :: Case
group206 =
    Case
        "expected206"
        [ TestExpr "HOCTX|HOBOOL+REFL|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g f a -> g (\x -> if f x then x else a) (f a))
                    :: ((Bool->Bool)->Bool->Bool) -> (Bool->Bool) -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (\\x3 -> if x1 x3 then x3 else x2) (x1 x2)"
            ]

group207 :: Case
group207 =
    Case
        "expected207"
        [ TestExpr "ARG|DIR|NEST-BR+SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g b (if a then (if b then a else b) else (if b then b else a)))
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 x2 (if x1 then x2 else x2)"
            ]

group208 :: Case
group208 =
    Case
        "expected208"
        [ TestExpr "HOCTX|DIR+HOBOOL|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g (\x y -> if x then y else a) (if b then a else b))
                    :: ((Bool->Bool->Bool)->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (\\x3 x4 -> if x3 then x4 else x1) (if x2 then x1 else False)"
            ]

group209 :: Case
group209 =
    Case
        "expected209"
        [ TestExpr "ARG|REFL|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g a b -> g (f a) (f b) (if f a then b else f b))
                    :: (Bool->Bool) -> (Bool->Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x1 (x0 x2) (x0 x3) (if x0 x2 then x3 else x0 x3)"
            ]

group210 :: Case
group210 =
    Case
        "expected210"
        [ TestExpr "ARG|DIR|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a -> g (g a a) (if a then g a a else a))
                    :: (Bool->Bool->Bool) -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 -> x0 (x0 x1 x1) (if x1 then x0 True True else False)"
            ]

group211 :: Case
group211 =
    Case
        "expected211"
        [ TestExpr "TOP|DIR|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f x y -> if f x y then x else y)
                    :: (a -> a -> Bool) -> a -> a -> a)
        ]
        $ expr
            [ "\\x0 x1 x2 -> if x0 x1 x2 then x1 else x2"
            ]

group212 :: Case
group212 =
    Case
        "expected212"
        [ TestExpr "ARG|REFL|BASE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g x -> g (f x) x)
                    :: (a -> Bool) -> (Bool -> a -> a) -> a -> a)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x1 (x0 x2) x2"
            ]

group213 :: Case
group213 =
    Case
        "expected213"
        [ TestExpr "ARG|REFL|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g x y -> g (if f x then y else x) (if f y then x else y))
                    :: (a -> Bool) -> (a -> a -> a) -> a -> a -> a)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x1 (if x0 x2 then x3 else x2) (if x0 x3 then x2 else x3)"
            ]

group214 :: Case
group214 =
    Case
        "expected214"
        [ TestExpr "HOCTX|HOBOOL+REFL|CAPTURE|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g f -> g (\x -> if f x then f x else False))
                    :: ((a -> Bool) -> Bool) -> (a -> Bool) -> Bool)
        ]
        $ expr
            [ "\\x0 x1 -> x0 (\\x2 -> if x1 x2 then x1 x2 else False)"
            ]

group215 :: Case
group215 =
    Case
        "expected215"
        [ TestExpr "ARG|REFL|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g a b -> g (if f a then f b else a) (if f b then f a else b))
                    :: (Bool->Bool) -> (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x1 (if x0 x2 then x0 x3 else x2) (if x0 x3 then x0 x2 else x3)"
            ]

group216 :: Case
group216 =
    Case
        "expected216"
        [ TestExpr "ARG|DIR|NEST-BR+SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b c -> g (if a then b else c) (if a then (if b then c else a) else c))
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x0"
            , "  (if x1 then x2 else x3)"
            , "  (if x1 then if x2 then x3 else True else x3)"
            ]

group217 :: Case
group217 =
    Case
        "expected217"
        [ TestExpr "ARG|DIR|NEST-BR+SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g (if a then b else a) (if a then (if b then a else b) else (if b then b else a)))
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then x2 else False) (if x1 then x2 else x2)"
            ]

group218 :: Case
group218 =
    Case
        "expected218"
        [ TestExpr "ARG|DIR|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b c -> g (if a then b else c) (if a then c else b) (if a then b else b))
                    :: (Bool->Bool->Bool->Bool) -> Bool -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x0"
            , "  (if x1 then x2 else x3)"
            , "  (if x1 then x3 else x2)"
            , "  (if x1 then x2 else x2)"
            ]

group219 :: Case
group219 =
    Case
        "expected219"
        [ TestExpr "ARG|DIR|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g (if a then True else b) (if a then b else False))
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then True else x2) (if x1 then x2 else False)"
            ]

group220 :: Case
group220 =
    Case
        "expected220"
        [ TestExpr "ARG|REFL|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g h a b -> g (h (if a then b else a)) (if a then a else b))
                    :: (Bool->Bool->Bool) -> (Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x0 (x1 (if x2 then x3 else False)) (if x2 then True else x3)"
            ]

group221 :: Case
group221 =
    Case
        "expected221"
        [ TestExpr "ARG|DIR|BASE|LET|expr1" $
            withoutCallStack $ guess
                ((\g a b -> let y = if a then b else a in g y (if y then b else y))
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then x2 else False) (if x1 then x2 else False)"
            ]

group222 :: Case
group222 =
    Case
        "expected222"
        [ TestExpr "ARG|DIR|BASE|LET|expr1" $
            withoutCallStack $ guess
                ((\g a b -> let y = if a then b else a in g (if y then a else b) y)
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then x2 else x2) (if x1 then x2 else False)"
            ]

group223 :: Case
group223 =
    Case
        "expected223"
        [ TestExpr "ARG|DIR|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g h a b c -> g (h (if a then b else c) (if a then c else b)) (if a then b else c))
                    :: (Bool->Bool->Bool) -> (Bool->Bool->Bool) -> Bool -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 x4 -> x0"
            , "  (x1 (if x2 then x3 else x4) (if x2 then x4 else x3))"
            , "  (if x2 then x3 else x4)"
            ]

group224 :: Case
group224 =
    Case
        "expected224"
        [ TestExpr "ARG|REFL|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g a b -> g (if f a then b else a) (if f a then a else b) (if f a then b else b))
                    :: (Bool->Bool) -> (Bool->Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x1"
            , "  (if x0 x2 then x3 else x2)"
            , "  (if x0 x2 then x2 else x3)"
            , "  (if x0 x2 then x3 else x3)"
            ]

group225 :: Case
group225 =
    Case
        "expected225"
        [ TestExpr "ARG|REFL|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g a b -> g (f (if a then b else a)) (f (if a then a else b)))
                    :: (Bool->Bool) -> (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x1"
            , "  (x0 (if x2 then x3 else False))"
            , "  (x0 (if x2 then True else x3))"
            ]

group226 :: Case
group226 =
    Case
        "expected226"
        [ TestExpr "ARG|DIR|NEST-BR+SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g (if a then (if b then a else b) else b) (if b then (if a then b else a) else a))
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 (if x1 then x2 else x2) (if x2 then x1 else x1)"
            ]

group227 :: Case
group227 =
    Case
        "expected227"
        [ TestExpr "ARG|REFL|SIB|LET|expr1" $
            withoutCallStack $ guess
                ((\f g a b -> let y = f a in g (if y then b else a) (if y then a else b))
                    :: (Bool->Bool) -> (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x1 (if x0 x2 then x3 else x2) (if x0 x2 then x2 else x3)"
            ]

group228 :: Case
group228 =
    Case
        "expected228"
        [ TestExpr "ARG|REFL|SIB|LET|expr1" $
            withoutCallStack $ guess
                ((\f g a b -> let y = f (if a then b else a) in g y (if y then a else b))
                    :: (Bool->Bool) -> (Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x1"
            , "  (x0 (if x2 then x3 else False))"
            , "  (if x0 (if x2 then x3 else False) then x2 else x3)"
            ]

group229 :: Case
group229 =
    Case
        "expected229"
        [ TestExpr "ARG|DIR|NEST-BR+SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b c -> g (if a then (if b then (if c then a else b) else c) else b) (if a then c else b))
                    :: (Bool->Bool->Bool) -> Bool -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x0"
            , "  (if x1 then if x2 then if x3 then True else True else x3 else x2)"
            , "  (if x1 then x3 else x2)"
            ]

group230 :: Case
group230 =
    Case
        "expected230"
        [ TestExpr "ARG|REFL|SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\f g a b -> g (if f a then f b else a) (if f b then f a else b) (if f a then a else b))
                    :: (Bool->Bool) -> (Bool->Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 x3 -> x1"
            , "  (if x0 x2 then x0 x3 else x2)"
            , "  (if x0 x3 then x0 x2 else x3)"
            , "  (if x0 x2 then x2 else x3)"
            ]

group231 :: Case
group231 =
    Case
        "expected231"
        [ TestExpr "ARG|DIR|NEST-BR+SIB|PLAIN|expr1" $
            withoutCallStack $ guess
                ((\g a b -> g a (if a then (if a then b else a) else (if a then a else b)) b)
                    :: (Bool->Bool->Bool->Bool) -> Bool -> Bool -> Bool)
        ]
        $ expr
            [ "\\x0 x1 x2 -> x0 x1 (if x1 then x2 else x2) x2"
            ]
allCases :: [Case]
allCases =
    [ group00_1
    , group01
    , group02
    , group02_b
    , group03
    , group04
    , group05
    , group06
    , group07
    , group08
    , group09
    , group10
    , group11
    , group12
    , group13
    , group13b
    , group14
    , group15
    , group16
    , group17
    , group18
    , group19
    , group20
    , group21
    , group22
    , group23
    , group24
    , group25
    , group26
    , group27
    , group28
    , group29
    , group31
    , group32
    , group33
    , group34
    , group35
    , group36
    , group37
    , group38
    , group40
    , group41
    , group42
    , group43
    , group44
    , group45
    , group46
    , group47
    , group48
    , group49
    , group51
    , group52
    , group53
    , group54
    , group55
    , group56
    , group57
    , group58
    , group59
    , group60
    , group61
    , group62
    , group63
    , group64
    , group65
    , group66
    , group67
    , group68
    , group69
    , group70
    , groupChoose1BothFunArgShared
    , group72
    , group73
    , group74
    , group75
    , group76
    , group77
    , group78
    , group79
    , group80
    , group81
    , group82
    , group83
    , group84
    , group85
    , group86
    , group87
    , group88
    , group89
    , group90
    , group91
    , group92
    , group93
    , group94
    , group94b
    , group95
    , group95b
    , group96
    , group97
    , group98
    , group99
    , group100
    , group101
    , group102
    , group103
    , group104
    , group105
    , group106
    , group107
    , group108
    , group109
    , group110
    , group111
    , group112
    , group113
    , group114
    , group115
    , group116
    , group117
    , group118
    , group119
    , group120
    , group121
    , group122
    , group123
    , group124
    , group125
    , group126
    , group127
    , group128
    , group129
    , group130
    , group131
    , group132
    , group133
    , group134
    , group135
    , group136
    , group137
    , group138
    , group139
    , group140
    , group141
    , group142
    , group143
    , group144
    , group145
    , group146
    , group147
    , group148
    , group149
    , group150
    , group151
    , group152
    , group153
    , group154
    , group155
    , group156
    , group157
    , group158
    , group159
    , group160
    , group161
    , group162
    , group163
    , group164
    , group165
    , group166
    , group167
    , group168
    , group169
    , group170
    , group171
    , group172
    , group173
    , group174
    , group175
    , group176
    , group177
    , group178
    , group179
    , group180
    , group181
    , group182
    , group183
    , group184
    , group185
    , group186
    , group187
    , group188
    , group189
    , group190
    , group191
    , group192
    , group193
    , group194
    , group195
    , group196
    , group197
    , group198
    , group199
    , group200
    , group201
    , group202
    , group203
    , group204
    , group205
    , group206
    , group207
    , group208
    , group209
    , group210
    , group211
    , group212
    , group213
    , group214
    , group215
    , group216
    , group217
    , group218
    , group219
    , group220
    , group221
    , group222
    , group223
    , group224
    , group225
    , group226
    , group227
    , group228
    , group229
    , group230
    , group231
    ]

getCases :: IO [Case]
getCases = shuffleM allCases

allowedPositions :: Set.Set String
allowedPositions =
    Set.fromList
        [ "ARG"
        , "FUN"
        , "BOTH"
        , "TOP"
        , "HOCTX"
        ]

allowedSources :: Set.Set String
allowedSources =
    Set.fromList
        [ "NONE"
        , "DIR"
        , "REFL"
        , "COMP"
        , "CHOOSE1"
        , "HOBOOL"
        , "CHOOSEHO"
        , "MIXED-COND"
        ]

allowedShapes :: Set.Set String
allowedShapes =
    Set.fromList
        [ "BASE"
        , "APP-NEST"
        , "NEST-BR"
        , "NEST-COND"
        , "SIB"
        , "FUN+ARG-SHARED"
        , "FUN+ARG-INDEP"
        , "REUSE"
        , "DUP-BR"
        , "CAPTURE"
        , "PAYLOAD-REUSE"
        ]

allowedInvariances :: Set.Set String
allowedInvariances =
    Set.fromList
        [ "PLAIN"
        , "ID"
        , "NEG"
        , "DBLNEG"
        , "CONST"
        , "LET"
        , "BETA"
        ]

splitOn :: Char -> String -> [String]
splitOn delim = go []
  where
    go revCurrent s =
        case s of
            [] ->
                [reverse revCurrent]
            c : cs
                | c == delim ->
                    reverse revCurrent : go [] cs
                | otherwise ->
                    go (c : revCurrent) cs

parseTagSet :: String -> Set.Set String -> String -> Either String (Set.Set String)
parseTagSet slotName allowed slot =
    let allowedByLength =
            reverse $ Set.toAscList $ Set.map (\tag -> (length tag, tag)) allowed
        parseParts s =
            case s of
                [] -> Just []
                _ ->
                    firstMatch
                        [ case stripToken token s of
                            Nothing -> Nothing
                            Just rest ->
                                (token :) <$> parseParts rest
                        | (_, token) <- allowedByLength
                        ]
        stripToken token s
            | s == token = Just []
            | (token ++ "+") `prefixOf` s = Just $ drop (length token + 1) s
            | otherwise = Nothing
        prefixOf prefix s = take (length prefix) s == prefix
        firstMatch options =
            case [res | Just res <- options] of
                match : _ -> Just match
                [] -> Nothing
     in case parseParts slot of
            Just [] ->
                Left $ slotName ++ " slot must not be empty"
            Just tags
                | length tags /= Set.size (Set.fromList tags) ->
                    Left $ slotName ++ " slot contains duplicate tags: " ++ slot
                | otherwise ->
                    Right $ Set.fromList tags
            Nothing ->
                Left $ slotName ++ " slot contains unknown tags: " ++ slot

parseTaxonomyLabel :: String -> Either String TaxonomyLabel
parseTaxonomyLabel label =
    case splitOn '|' label of
        [pos0, src0, shape0, inv0, variant0] -> do
            if pos0 `Set.member` allowedPositions
                then pure ()
                else Left $ "unknown position tag: " ++ pos0
            source <- parseTagSet "source" allowedSources src0
            shape <- parseTagSet "shape" allowedShapes shape0
            invariance <- parseTagSet "invariance" allowedInvariances inv0
            if null variant0
                then Left "variant slot must not be empty"
                else pure ()
            pure $
                TaxonomyLabel
                    { labelPosition = pos0
                    , labelSource = source
                    , labelShape = shape
                    , labelInvariance = invariance
                    , labelVariant = variant0
                    }
        slots ->
            Left $
                "expected 5 taxonomy slots but found "
                    ++ show (length slots)
                    ++ " in "
                    ++ show label

testExprLabel :: TestExpr -> String
testExprLabel (TestExpr label _) = label

caseLabels :: Case -> [String]
caseLabels (Case _ exprs _) = map testExprLabel exprs

caseName :: Case -> String
caseName (Case name _ _) = name

caseTestPaths :: Case -> [String]
caseTestPaths case0@(Case _ exprs _) =
    map ((caseName case0 ++ "/") ++) $ map testExprLabel exprs

duplicates :: Ord a => [a] -> [a]
duplicates = foldr collect [] . group . sort
  where
    collect values acc =
        case values of
            value : _ : _ -> value : acc
            _ -> acc

allTaxonomyLabels :: [String]
allTaxonomyLabels = concatMap caseLabels allCases

hasCoverage :: [TaxonomyLabel] -> String -> String -> String -> String -> Either String Bool
hasCoverage labels pos src shape inv = do
    sourceReq <- parseTagSet "required source" allowedSources src
    shapeReq <- parseTagSet "required shape" allowedShapes shape
    invReq <- parseTagSet "required invariance" allowedInvariances inv
    pure $
        any
            (\label ->
                labelPosition label == pos
                    && sourceReq `Set.isSubsetOf` labelSource label
                    && shapeReq `Set.isSubsetOf` labelShape label
                    && invReq `Set.isSubsetOf` labelInvariance label
            )
            labels

requiredCoverage :: [(String, String, String, String)]
requiredCoverage =
    [ ("ARG", "DIR", "BASE", "ID")
    , ("ARG", "DIR", "BASE", "NEG")
    , ("ARG", "DIR", "SIB+PAYLOAD-REUSE", "LET")
    , ("ARG", "DIR", "NEST-BR", "NEG")
    , ("ARG", "DIR", "NEST-COND", "DBLNEG")
    , ("FUN", "DIR", "BASE", "PLAIN")
    , ("BOTH", "DIR", "FUN+ARG-SHARED", "ID")
    , ("BOTH", "DIR", "FUN+ARG-INDEP", "CONST")
    , ("TOP", "DIR", "BASE", "ID")
    , ("TOP", "DIR", "CAPTURE", "LET")
    , ("ARG", "REFL", "BASE", "ID")
    , ("ARG", "REFL", "SIB", "NEG")
    , ("ARG", "REFL", "SIB+PAYLOAD-REUSE", "LET")
    , ("ARG", "REFL", "SIB+NEST-COND+PAYLOAD-REUSE", "LET")
    , ("ARG", "REFL", "DUP-BR", "CONST")
    , ("FUN", "REFL", "BASE", "PLAIN")
    , ("FUN", "REFL", "NEST-COND", "ID")
    , ("BOTH", "REFL", "FUN+ARG-SHARED", "NEG")
    , ("TOP", "REFL", "BASE", "ID")
    , ("TOP", "REFL", "APP-NEST", "ID")
    , ("TOP", "REFL", "CAPTURE", "ID")
    , ("ARG", "COMP", "BASE", "ID")
    , ("ARG", "COMP", "SIB", "LET")
    , ("ARG", "COMP", "NEST-COND", "ID")
    , ("ARG", "COMP", "NEST-BR", "PLAIN")
    , ("FUN", "COMP", "BASE", "PLAIN")
    , ("FUN", "COMP", "NEST-COND", "ID")
    , ("BOTH", "COMP", "FUN+ARG-SHARED", "PLAIN")
    , ("TOP", "COMP", "BASE", "ID")
    , ("TOP", "COMP", "CAPTURE", "ID")
    , ("HOCTX", "COMP", "CAPTURE", "ID")
    , ("ARG", "CHOOSE1", "BASE", "PLAIN")
    , ("ARG", "CHOOSE1", "NEST-COND", "ID")
    , ("ARG", "CHOOSE1", "SIB", "PLAIN")
    , ("FUN", "CHOOSE1", "BASE", "ID")
    , ("BOTH", "CHOOSE1", "FUN+ARG-SHARED", "ID")
    , ("TOP", "CHOOSE1", "BASE", "ID")
    , ("HOCTX", "CHOOSE1", "CAPTURE", "ID")
    , ("ARG", "HOBOOL", "BASE", "PLAIN")
    , ("ARG", "HOBOOL", "NEST-COND", "ID")
    , ("ARG", "HOBOOL", "SIB", "PLAIN")
    , ("FUN", "HOBOOL", "BASE", "ID")
    , ("BOTH", "HOBOOL", "FUN+ARG-SHARED", "ID")
    , ("TOP", "HOBOOL", "BASE", "ID")
    , ("ARG", "CHOOSEHO", "BASE", "PLAIN")
    , ("ARG", "CHOOSEHO", "NEST-COND", "ID")
    , ("ARG", "CHOOSEHO", "SIB", "PLAIN")
    , ("FUN", "CHOOSEHO", "BASE", "ID")
    , ("BOTH", "CHOOSEHO", "FUN+ARG-SHARED", "ID")
    , ("TOP", "CHOOSEHO", "BASE", "ID")
    , ("HOCTX", "CHOOSEHO", "CAPTURE", "ID")
    , ("ARG", "MIXED-COND", "BASE", "PLAIN")
    , ("ARG", "MIXED-COND", "NEST-COND", "ID")
    , ("FUN", "MIXED-COND", "BASE", "ID")
    , ("BOTH", "MIXED-COND", "FUN+ARG-SHARED", "ID")
    , ("TOP", "MIXED-COND", "DUP-BR", "ID")
    , ("ARG", "HOBOOL+CHOOSE1", "NEST-COND", "ID")
    , ("ARG", "MIXED-COND+COMP", "NEST-BR", "PLAIN")
    , ("ARG", "NONE", "REUSE", "PLAIN")
    , ("TOP", "NONE", "BASE", "PLAIN")
    , ("HOCTX", "DIR", "CAPTURE", "LET")
    , ("HOCTX", "DIR", "CAPTURE+NEST-COND", "LET")
    , ("HOCTX", "HOBOOL", "CAPTURE+NEST-COND", "PLAIN")
    , ("TOP", "REFL", "NEST-BR+PAYLOAD-REUSE", "BETA")
    , ("TOP", "REFL", "NEST-BR+PAYLOAD-REUSE", "PLAIN")
    , ("ARG", "REFL", "DUP-BR+PAYLOAD-REUSE", "BETA")
    , ("ARG", "REFL", "DUP-BR+PAYLOAD-REUSE", "PLAIN")
    , ("HOCTX", "REFL", "CAPTURE+DUP-BR+PAYLOAD-REUSE", "BETA")
    , ("HOCTX", "REFL", "CAPTURE+DUP-BR+PAYLOAD-REUSE", "PLAIN")
    ]

labelValidationTests :: TestTree
labelValidationTests =
    testGroup
        "taxonomy"
        [ testCase "labels parse against the declared taxonomy" $
            case
                [ label ++ ": " ++ err
                | label <- allTaxonomyLabels
                , Left err <- [parseTaxonomyLabel label]
                ]
            of
                [] -> pure ()
                errs ->
                    assertFailure $
                        "Invalid taxonomy labels:\n" ++ intercalate "\n" errs
        , testCase "case names and test paths are unique" $
            case
                ( duplicates $ map caseName allCases
                , duplicates $ concatMap caseTestPaths allCases
                )
            of
                ([], []) -> pure ()
                (duplicateCases, duplicatePaths) ->
                    assertFailure $
                        intercalate
                            "\n"
                            [ "Duplicate case names: " ++ show duplicateCases
                            , "Duplicate test paths: " ++ show duplicatePaths
                            ]
        , testCase "required matrix edges are covered" $
            case traverse parseTaxonomyLabel allTaxonomyLabels of
                Left err ->
                    assertFailure $ "Failed to parse taxonomy labels: " ++ err
                Right labels ->
                    case catMaybes <$> traverse checkRequirement requiredCoverage of
                        Left err ->
                            assertFailure err
                        Right [] -> pure ()
                        Right missing ->
                            assertFailure $
                                "Missing required taxonomy coverage:\n"
                                    ++ intercalate "\n" missing
                  where
                    checkRequirement (pos, src, shape, inv) =
                        let rendered = intercalate "|" [pos, src, shape, inv]
                         in case hasCoverage labels pos src shape inv of
                                Left err ->
                                    Left $
                                        "Invalid required coverage entry "
                                            ++ show rendered
                                            ++ ": "
                                            ++ err
                                Right True ->
                                    Right Nothing
                                Right False ->
                                    Right $ Just rendered
        ]

equivalenceTests :: TestTree
equivalenceTests =
    testGroup
        "alpha/eta equality"
        [ equivalent "alpha-renamed binders"
            (LamR "x" $ AppR (VarR "f") (VarR "x"))
            (LamR "argument" $ AppR (VarR "f") (VarR "argument"))
        , equivalent "single eta contraction"
            (LamR "x" $ AppR (VarR "f") (VarR "x"))
            (VarR "f")
        , equivalent "multi-step eta contraction"
            ( LamR "x" $
                LamR "y" $
                    AppR (AppR (VarR "f") (VarR "x")) (VarR "y")
            )
            (VarR "f")
        , equivalent "eta contraction under conditionals"
            ( IteR
                (VarR "condition")
                (LamR "x" $ AppR (VarR "f") (VarR "x"))
                (LamR "y" $ AppR (VarR "g") (VarR "y"))
            )
            (IteR (VarR "condition") (VarR "f") (VarR "g"))
        , equivalent "surviving binders are reindexed after eta contraction"
            (LamR "x" $ AppR (LamR "y" $ VarR "y") (VarR "x"))
            (LamR "z" $ VarR "z")
        , equivalent "shadowing remains alpha-equivalent"
            (LamR "x" $ LamR "x" $ VarR "x")
            (LamR "outer" $ LamR "inner" $ VarR "inner")
        , different "free variable cannot impersonate a binder"
            (LamR "x" $ VarR "x")
            (LamR "broken0" $ VarR "x0")
        , different "shadowed and captured variables differ"
            (LamR "x" $ LamR "x" $ VarR "x")
            (LamR "outer" $ LamR "inner" $ VarR "outer")
        , different "eta side condition checks the function"
            (LamR "x" $ AppR (VarR "x") (VarR "x"))
            (VarR "x")
        , testCase "closedness distinguishes bound and free names" $ do
            assertBool "bound identity reported open" $
                isClosedExprR $ LamR "x0" $ VarR "x0"
            assertBool "free x0 reported bound" $
                not $ isClosedExprR $ LamR "broken0" $ VarR "x0"
        ]
  where
    equivalent name left right =
        testCase name $
            alphaEtaNormalForm left @?= alphaEtaNormalForm right

    different name left right =
        testCase name $
            assertBool
                "terms unexpectedly compared equal"
                (not $ alphaEtaEquivalent left right)

mkExprTest :: String -> TestExpr -> TestTree
mkExprTest expected (TestExpr label expr0) =
    testCase label $
        case parseExprR expected of
            Left err ->
                assertFailure $
                    "Failed to parse expected ExprR:\n" ++ err
            Right expectedExpr -> do
                let actualExpr = expr0
                    rendered = renderExprR actualExpr
                assertBool "expected fixture contains a free variable" $
                    isClosedExprR expectedExpr
                assertBool
                    ("guess returned an open expression:\n" ++ rendered)
                    (isClosedExprR actualExpr)
                alphaEtaNormalForm actualExpr @?= alphaEtaNormalForm expectedExpr
                case parseExprR rendered of
                    Left err ->
                        assertFailure $
                            "Failed to parse rendered ExprR:\n"
                                ++ rendered
                                ++ "\n\n"
                                ++ err
                    Right renderedExpr ->
                        renderedExpr @?= actualExpr

mkTest :: Case -> TestTree
mkTest (Case name exprs expected) =
    testGroup name $ map (mkExprTest expected) exprs

-- Individual performance tests retain their tighter limits; this only prevents the complete suite
-- from running indefinitely.
fullSuiteTimeoutMicros :: Int
fullSuiteTimeoutMicros = 240000000

main :: IO ()
main = do
    cases <- getCases
    props <- propertyTests
    completed <-
        timeout fullSuiteTimeoutMicros $
            defaultMain $
                -- Serially, so that a test's reported time is its own work rather than everyone
                -- else's time slices: the timeouts below are multiples of these numbers.
                localOption (NumThreads 1) $
                testGroup
                    "j2-guess-function"
                    [ equivalenceTests
                    , labelValidationTests
                    , testGroup "goldens" $ map mkTest cases
                    , props
                    , nestingTests hardcore
                    , performanceTests hardcore
                    , stressTests
                    ]
    case completed of
        Just () ->
            pure ()
        Nothing -> do
            hPutStrLn stderr $
                "Test suite exceeded its "
                    ++ show (fromIntegral fullSuiteTimeoutMicros / 1000000 :: Double)
                    ++ "-second time limit"
            exitFailure
