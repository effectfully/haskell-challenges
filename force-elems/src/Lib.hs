module Lib
    ( forceElems
    ) where

-- | An 'Identity'-like applicative that distinguishes element positions
-- ('Strict') from everything else ('Lazy'). Composition is lazy in both
-- arguments: the decision of whether to force is deferred until the payload
-- itself gets forced by the final consumer.
data Strictly a
    = Strict a
    | Lazy a

unStrictly :: Strictly a -> a
unStrictly (Strict x) = x
unStrictly (Lazy   x) = x

instance Functor Strictly where
    fmap f sx = Lazy $ case sx of
        Strict x -> f $! x
        Lazy   x -> f x

instance Applicative Strictly where
    pure = Lazy
    sf <*> sx = Lazy $ case sx of
        Strict x -> unStrictly sf $! x
        Lazy   x -> unStrictly sf x

forceElems :: Traversable t => t a -> t a
forceElems = unStrictly . traverse Strict
