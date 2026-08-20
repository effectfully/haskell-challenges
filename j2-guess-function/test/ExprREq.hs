module ExprREq
    ( AlphaEtaExpr
    , alphaEtaEquivalent
    , alphaEtaNormalForm
    , isClosedExprR
    ) where

import Lib.ExprR (ExprR(..))

import Data.List (elemIndex)

-- Binder identities are distinct from source names. This intermediate form
-- makes shadowing explicit and, crucially, cannot confuse a free variable
-- called "x0" with the first bound variable.
data ResolvedExpr
    = ResolvedVal Bool
    | ResolvedBound Int
    | ResolvedFree String
    | ResolvedApp ResolvedExpr ResolvedExpr
    | ResolvedLam Int ResolvedExpr
    | ResolvedIte ResolvedExpr ResolvedExpr ResolvedExpr

-- The public normal form uses de Bruijn indices for surviving binders and a
-- separate constructor for free variables. Eta-reduction happens before this
-- final indexing pass, so removing a binder cannot leave numbering gaps that
-- make alpha-equivalent terms compare differently.
data AlphaEtaExpr
    = AlphaEtaVal Bool
    | AlphaEtaBound Int
    | AlphaEtaFree String
    | AlphaEtaApp AlphaEtaExpr AlphaEtaExpr
    | AlphaEtaLam AlphaEtaExpr
    | AlphaEtaIte AlphaEtaExpr AlphaEtaExpr AlphaEtaExpr
    deriving (Eq, Show)

alphaEtaEquivalent :: ExprR -> ExprR -> Bool
alphaEtaEquivalent left right =
    alphaEtaNormalForm left == alphaEtaNormalForm right

alphaEtaNormalForm :: ExprR -> AlphaEtaExpr
alphaEtaNormalForm =
    indexBinders . etaNormalize . resolveNames

isClosedExprR :: ExprR -> Bool
isClosedExprR =
    isClosedResolved . resolveNames

resolveNames :: ExprR -> ResolvedExpr
resolveNames =
    fst . go [] 0
  where
    go :: [(String, Int)] -> Int -> ExprR -> (ResolvedExpr, Int)
    go env next expr =
        case expr of
            ValR value ->
                (ResolvedVal value, next)
            VarR name ->
                ( maybe (ResolvedFree name) ResolvedBound $ lookup name env
                , next
                )
            AppR fun arg ->
                let (fun', next') = go env next fun
                    (arg', next'') = go env next' arg
                 in (ResolvedApp fun' arg', next'')
            LamR name body ->
                let binder = next
                    (body', next') = go ((name, binder) : env) (next + 1) body
                 in (ResolvedLam binder body', next')
            IteR cond yes no ->
                let (cond', next') = go env next cond
                    (yes', next'') = go env next' yes
                    (no', next''') = go env next'' no
                 in (ResolvedIte cond' yes' no', next''')

-- Standard, capture-avoiding eta-reduction to a fixed normal form. Recursive
-- normalization happens before testing each lambda, so chains such as
-- \x y -> f x y contract fully rather than by a single outer pass.
etaNormalize :: ResolvedExpr -> ResolvedExpr
etaNormalize expr =
    case expr of
        ResolvedVal value ->
            ResolvedVal value
        ResolvedBound binder ->
            ResolvedBound binder
        ResolvedFree name ->
            ResolvedFree name
        ResolvedApp fun arg ->
            ResolvedApp (etaNormalize fun) (etaNormalize arg)
        ResolvedLam binder body ->
            case etaNormalize body of
                ResolvedApp fun (ResolvedBound argBinder)
                    | argBinder == binder
                    , not $ mentionsBinder binder fun ->
                        fun
                body' ->
                    ResolvedLam binder body'
        ResolvedIte cond yes no ->
            ResolvedIte
                (etaNormalize cond)
                (etaNormalize yes)
                (etaNormalize no)

mentionsBinder :: Int -> ResolvedExpr -> Bool
mentionsBinder needle expr =
    case expr of
        ResolvedVal _ ->
            False
        ResolvedBound binder ->
            binder == needle
        ResolvedFree _ ->
            False
        ResolvedApp fun arg ->
            mentionsBinder needle fun || mentionsBinder needle arg
        ResolvedLam _ body ->
            mentionsBinder needle body
        ResolvedIte cond yes no ->
            mentionsBinder needle cond
                || mentionsBinder needle yes
                || mentionsBinder needle no

indexBinders :: ResolvedExpr -> AlphaEtaExpr
indexBinders =
    go []
  where
    go :: [Int] -> ResolvedExpr -> AlphaEtaExpr
    go env expr =
        case expr of
            ResolvedVal value ->
                AlphaEtaVal value
            ResolvedBound binder ->
                case elemIndex binder env of
                    Just index ->
                        AlphaEtaBound index
                    Nothing ->
                        error "indexBinders: escaped bound variable"
            ResolvedFree name ->
                AlphaEtaFree name
            ResolvedApp fun arg ->
                AlphaEtaApp (go env fun) (go env arg)
            ResolvedLam binder body ->
                AlphaEtaLam $ go (binder : env) body
            ResolvedIte cond yes no ->
                AlphaEtaIte (go env cond) (go env yes) (go env no)

isClosedResolved :: ResolvedExpr -> Bool
isClosedResolved expr =
    case expr of
        ResolvedVal _ ->
            True
        ResolvedBound _ ->
            True
        ResolvedFree _ ->
            False
        ResolvedApp fun arg ->
            isClosedResolved fun && isClosedResolved arg
        ResolvedLam _ body ->
            isClosedResolved body
        ResolvedIte cond yes no ->
            isClosedResolved cond
                && isClosedResolved yes
                && isClosedResolved no
