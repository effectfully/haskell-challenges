{-# LANGUAGE GADTs #-}

module Lib.ExprR
    ( ExprR(..)
    , prettyExprR
    , renderExprR
    , parseExprR
    ) where

import           Control.Applicative (empty)
import           Data.Void
import           Prettyprinter
    ( Doc
    , Pretty(..)
    , defaultLayoutOptions
    , group
    , hang
    , layoutPretty
    , parens
    , sep
    , vsep
    , (<+>)
    )
import           Prettyprinter.Render.String (renderString)
import           Text.Megaparsec
    ( Parsec
    , between
    , eof
    , errorBundlePretty
    , many
    , parse
    , some
    , try
    , (<|>)
    )
import           Text.Megaparsec.Char (alphaNumChar, char, letterChar, space1)
import qualified Text.Megaparsec.Char.Lexer as L

data ExprR where
    ValR :: !Bool -> ExprR
    VarR :: !String -> ExprR
    AppR :: !ExprR -> !ExprR -> ExprR
    LamR :: !String -> !ExprR -> ExprR
    IteR :: !ExprR -> !ExprR -> !ExprR -> ExprR  -- if-then-else

instance Show ExprR where
    show = renderExprR

instance Pretty ExprR where
    pretty = prettyExprR

instance Eq ExprR where
    ValR bL == exprR0 =
        case exprR0 of
            ValR bR -> bL == bR
            _ -> False
    VarR vL == exprR0 =
        case exprR0 of
            VarR vR -> vL == vR
            _ -> False
    AppR fL xL == exprR0 =
        case exprR0 of
            AppR fR xR -> fL == fR && xL == xR
            _ -> False
    LamR vL bodyL == exprR0 =
        case exprR0 of
            LamR vR bodyR -> vL == vR && bodyL == bodyR
            _ -> False
    IteR cL tL eL == exprR0 =
        case exprR0 of
            IteR cR tR eR ->
                cL == cR && tL == tR && eL == eR
            _ -> False

prettyExprR :: ExprR -> Doc ann
prettyExprR = prettyExprRPrec 0

renderExprR :: ExprR -> String
renderExprR =
    renderString
        . layoutPretty defaultLayoutOptions
        . prettyExprR

prettyExprRPrec :: Int -> ExprR -> Doc ann
prettyExprRPrec prec expr =
    case expr of
        ValR x ->
            pretty $ show x
        VarR name ->
            pretty name
        AppR _ _ ->
            parensIf (prec > 1) $
                let (funDoc, argDocs) = collectApps expr
                 in sep $ funDoc : argDocs
        LamR _ _ ->
            parensIf (prec > 0) $
                let (argDocs, bodyDoc) = collectLams expr
                 in group $
                        hang 2 $
                            (pretty "\\" <> sep argDocs <+> pretty "->")
                                <+> bodyDoc
        IteR cond yes no ->
            parensIf (prec > 0) $
                group $
                    hang 2 $
                        vsep
                            [ pretty "if" <+> prettyExprR cond
                            , pretty "then" <+> prettyExprR yes
                            , pretty "else" <+> prettyExprR no
                            ]

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True = parens
parensIf False = id

collectApps :: ExprR -> (Doc ann, [Doc ann])
collectApps = go []
  where
    go :: [Doc ann] -> ExprR -> (Doc ann, [Doc ann])
    go args (AppR fun arg) =
        go (prettyExprRPrec 2 arg : args) fun
    go args other =
        (prettyExprRPrec 1 other, args)

collectLams :: ExprR -> ([Doc ann], Doc ann)
collectLams = go []
  where
    go :: [Doc ann] -> ExprR -> ([Doc ann], Doc ann)
    go revArgs (LamR arg body) =
        go (pretty arg : revArgs) body
    go revArgs other =
        (reverse revArgs, prettyExprR other)

parseExprR :: String -> Either String ExprR
parseExprR input =
    case parse (spaceConsumer *> exprRParser <* eof) "<ExprR>" input of
        Left err ->
            Left $ errorBundlePretty err
        Right expr ->
            Right expr

type ExprRParser = Parsec Void String

spaceConsumer :: ExprRParser ()
spaceConsumer =
    L.space space1 empty empty

lexeme :: ExprRParser a -> ExprRParser a
lexeme = L.lexeme spaceConsumer

symbol :: String -> ExprRParser String
symbol = L.symbol spaceConsumer

exprRParser :: ExprRParser ExprR
exprRParser =
    lamParser <|> ifParser <|> appParser

lamParser :: ExprRParser ExprR
lamParser = do
    _ <- symbol "\\"
    args <- some identifierParser
    _ <- symbol "->"
    foldr LamR <$> exprRParser <*> pure args

ifParser :: ExprRParser ExprR
ifParser = do
    _ <- symbol "if"
    cond <- exprRParser
    _ <- symbol "then"
    yes <- exprRParser
    _ <- symbol "else"
    IteR cond yes <$> exprRParser

appParser :: ExprRParser ExprR
appParser =
    foldl1 AppR <$> some atomParser

atomParser :: ExprRParser ExprR
atomParser =
    boolParser
        <|> VarR <$> identifierParser
        <|> between (symbol "(") (symbol ")") exprRParser

boolParser :: ExprRParser ExprR
boolParser =
    (ValR True <$ symbol "True")
        <|> (ValR False <$ symbol "False")

identifierParser :: ExprRParser String
identifierParser =
    lexeme . try $ do
        first <- letterChar <|> char '_'
        rest <- many $ alphaNumChar <|> char '_' <|> char '\''
        let name = first : rest
        if name `elem` reservedWords
            then fail $ "keyword " ++ show name ++ " cannot be an identifier"
            else pure name

reservedWords :: [String]
reservedWords =
    [ "if"
    , "then"
    , "else"
    , "True"
    , "False"
    ]
