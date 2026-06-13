{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes        #-}

module Main where

import           Lib

import           Control.Monad
import           Data.IORef
import           Data.List
import           System.IO.Unsafe
import           Test.HUnit

hardcore :: Bool
hardcore = True

withTrace :: ((forall b. a -> b -> b) -> c) -> IO ([a], c)
withTrace k = do
    xsVar <- newIORef id
    let z = k $ \x y -> unsafePerformIO $ y <$ modifyIORef xsVar (. (x :))
    ds <- unsafeInterleaveIO $ readIORef xsVar
    return (ds [], z)

tracesAndNats :: IO ([Int], [()])
tracesAndNats =
    withTrace $ \trace ->
        let go n = trace n () : go (n + 1)
        in go 0

data Tree2 a
    = Fork2 (Tree2 a) a (Tree2 a) a
    deriving (Functor, Foldable, Traversable)

zigZag :: Tree2 a -> [a]
zigZag = go False where
    go False (Fork2 _ x r _) = x : go True  r
    go True  (Fork2 l _ _ y) = y : go False l

tracesAndPathsTree2 :: IO ([String], Tree2 ())
tracesAndPathsTree2 =
    withTrace $ \trace ->
        let go p =
              Fork2
                (go (p . ('l' :)))
                (trace (p "x") ())
                (go (p . ('r' :)))
                (trace (p "y") ())
        in go id

data Rose a
    = Rose a [Rose a]
    deriving (Functor, Foldable, Traversable)

rightmost :: Rose a -> [a]
rightmost (Rose x rs) = x : if null rs then [] else rightmost $ last rs

tracesAndPathsRose :: IO ([[Int]], Rose ())
tracesAndPathsRose =
    withTrace $ \trace ->
        let go n p =
              Rose
                (trace (p []) ())
                (map (\m -> go (n + 1) (p . (m :))) [0..n])
        in go 0 id

data L a
    = L (L a) Int
    deriving (Functor, Foldable)

instance Traversable L where
    traverse f (L l i) = flip L i <$> traverse f l

enumL :: L a
enumL = go 0 where
    go n = L (go $ n + 1) n

extractIntsL :: L a -> [Int]
extractIntsL (L l i) = i : extractIntsL l

data E a
    = E (E a) Int Int Int
    deriving (Functor, Foldable)

instance Traversable E where
    traverse f (E l i j k) = E <$> traverse f l <*> pure i <*> pure j <*> pure k

enumE :: E a
enumE = go 0 where
    go n = E (go $ n + 1) (error "left forced") n (error "right forced")

extractIntsE :: E a -> [Int]
extractIntsE (E l _ j _) = j : extractIntsE l

main :: IO ()
main = runTestTTAndExit . TestList $ map TestCase
    [ do
        (traces, nats) <- tracesAndNats
        length (take 6 nats) @?= 6
        traces @?= []
    , do
        (traces, nats) <- tracesAndNats
        length (take 1 $ forceElems nats) @?= 1
        traces @?= [0]
    , do
        (traces, nats) <- tracesAndNats
        length (take 5 $ forceElems nats) @?= 5
        traces @?= [0, 1, 2, 3, 4]
    , do
        (traces, paths) <- tracesAndPathsTree2
        length (take 3 $ zigZag paths) @?= 3
        traces @?= []
    , do
        (traces, paths) <- tracesAndPathsTree2
        length (take 4 . zigZag $ forceElems paths) @?= 4
        sort traces @?= ["rlrx", "rlry", "rlx", "rly", "rx", "ry", "x", "y"]
    , do
        (traces, paths) <- tracesAndPathsRose
        length (take 2 $ rightmost paths) @?= 2
        traces @?= []
    , do
        (traces, paths) <- tracesAndPathsRose
        length (take 7 . rightmost $ forceElems paths) @?= 7
        traces @?= inits [0..5]
    , when hardcore $ do
        take 9 (extractIntsL $ forceElems enumL) @?= [0..8]
    , when hardcore $ do
        take 8 (extractIntsE $ forceElems enumE) @?= [0..7]
    , when hardcore $ do
        (traces, xs) <- withTrace $ \trace ->
            trace "elem" () : error "spine forced beyond what was consumed"
        length (take 1 $ forceElems xs) @?= 1
        traces @?= ["elem"]
    , when hardcore $ do
        (traces, tree) <- withTrace $ \trace ->
            Fork2
                (error "left subtree forced")
                (trace "x" ())
                (error "right subtree forced")
                (trace "y" ())
        case forceElems tree of
            Fork2 _ _ _ _ -> return ()
        sort traces @?= ["x", "y"]
    ]
