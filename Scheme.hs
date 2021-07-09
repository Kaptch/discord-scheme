{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeApplications     #-}

module Scheme where

import           Control.Monad.Identity
import qualified Data.Char                 as DC
import qualified Data.HashMap              as HM
import qualified Data.List                 as DL
import           Data.Maybe
import           Debug.Trace
import           Numeric                   (readHex)
import qualified Polysemy                  as P
import qualified Polysemy.Error            as P
import qualified Polysemy.Embed            as P
import qualified Polysemy.Reader           as P
import qualified Polysemy.State            as P
import qualified Polysemy.Internal         as P
import           Text.Parsec hiding (try)
import           Text.ParserCombinators.Parsec
import           Text.Parsec.Language
import           Text.Parsec.Token         (LanguageDef(..)
                                           , GenTokenParser
                                           , commentStart
                                           , commentEnd
                                           , commentLine
                                           , nestedComments
                                           , identStart
                                           , identLetter
                                           , reservedNames
                                           , caseSensitive)
import qualified Text.Parsec.Token         as PA

data Environment m = Environment
  {
    parentEnv :: Maybe (Environment m)
  , bindings :: HM.Map String (SchemeValue m)
  }
  deriving (Show)

data Continuation m = Continuation
  {
    contClosure :: Environment m
  , currentCont :: Maybe (Func m)
  , nextCont :: Maybe (SchemeValue m)
  }
  deriving (Show)

type SchemePureEff m = '[P.Error (SchemeError m), P.State (Environment m), P.State (Continuation m)]

type SchemeC' m r = '[P.Error (SchemeError m), P.State (Environment m), P.State (Continuation m), P.Embed m] ~ r

type SchemeFunc m = [SchemeValue m]

data HaskellFunc m where
  HaskellFunc :: SchemeC' m r => (SchemeValue m -> Maybe [SchemeValue m] -> P.Sem r (SchemeValue m)) -> Maybe [SchemeValue m] -> HaskellFunc m

instance Show (HaskellFunc m) where
  show _ = "<HaskellFunc>"

data Func m =
  SF (SchemeFunc m)
  | HF (HaskellFunc m)
  deriving (Show)

data SchemeValue m where
  Atom :: String -> SchemeValue m
  List :: [SchemeValue m] -> SchemeValue m
  DottedList :: [SchemeValue m] -> (SchemeValue m) -> SchemeValue m
  Number :: Int -> SchemeValue m
  String :: String -> SchemeValue m
  Bool :: Bool -> SchemeValue m
  PrimitiveFunc :: SchemeC' m r => ([SchemeValue m] -> P.Sem r (SchemeValue m)) -> SchemeValue m
  Func :: [String] -> Maybe String -> SchemeFunc m -> SchemeValue m
  Cont :: Continuation m -> SchemeValue m
  Env :: Environment m -> SchemeValue m

data SchemeValueErased = AtomE String
  | ListE [SchemeValueErased]
  | DottedListE [SchemeValueErased] (SchemeValueErased)
  | NumberE Int
  | StringE String
  | BoolE Bool
  | FuncE
  deriving (Show)

eraseEff :: SchemeValue m -> SchemeValueErased
eraseEff (Atom a) = AtomE a
eraseEff (List l) = ListE (map eraseEff l)
eraseEff (DottedList l d) = DottedListE (map eraseEff l) (eraseEff d)
eraseEff (Number n) = NumberE n
eraseEff (String s) = StringE s
eraseEff (Bool b) = BoolE b
eraseEff _ = FuncE
  
instance Show (SchemeValue m) where
  show = showSchemeValue
    where
      showSchemeValue :: SchemeValue m -> String
      showSchemeValue (List []) = "<nil>"
      showSchemeValue (List ls) = "(" ++ (DL.intercalate "," $ map showSchemeValue ls) ++ ")"
      showSchemeValue (DottedList ls x) = "(" ++ ((DL.intercalate "," $ map showSchemeValue ls) ++ " . " ++ (showSchemeValue x)) ++ ")"
      showSchemeValue (Number x) = show x
      showSchemeValue (String s) = "\"" ++ s ++ "\""
      showSchemeValue (Bool b) = show b
      showSchemeValue (PrimitiveFunc _) = "<primfunc>"
      showSchemeValue (Func args varargs body) =
        "(lambda (" ++ unwords (map show args)
        ++ (case varargs of
               Nothing -> ""
               Just arg -> " . " ++ arg) ++ ") " ++ show body ++ ")"
      showSchemeValue (Cont _) = "<cont>"
      showSchemeValue (Env e) = show e
      showSchemeValue (Atom e) = e

data SchemeError m =
  NumArgs (Maybe Int) [SchemeValue m]
  | TypeMismatch String (SchemeValue m)
  | Parser ParseError
  | UnboundVar String
  | NotImplemented
  | BadSpecialForm (SchemeValue m)
  | Default String
  deriving (Show)

type EitherSchemeError m = Either (SchemeError m)

schemeDef :: LanguageDef ()
schemeDef 
  = emptyDef
  { commentStart   = "!-"
  , commentEnd     = "-!"
  , commentLine    = "#"
  , nestedComments = True
  , identStart     = letter <|> symbol
  , identLetter    = letter <|> digit <|> symbol
  , reservedNames  = []
  , caseSensitive  = True
  }

symbol :: Parser Char
symbol = oneOf "!$%&|*+-/:<=>?@^_~."

lexer :: GenTokenParser String () Identity
lexer = PA.makeTokenParser schemeDef

dot :: ParsecT String () Identity String
dot = PA.dot lexer

parens :: ParsecT String () Identity a -> ParsecT String () Identity a
parens = PA.parens lexer

brackets :: ParsecT String () Identity a -> ParsecT String () Identity a
brackets = PA.brackets lexer

identifier :: ParsecT String () Identity String
identifier = PA.identifier lexer

whiteSpace :: ParsecT String () Identity ()
whiteSpace = PA.whiteSpace lexer

lexeme :: ParsecT String () Identity a -> ParsecT String () Identity a
lexeme = PA.lexeme lexer

parseAtom :: Parser (SchemeValue m)
parseAtom = do
  atom <- identifier
  if atom == "."
     then pzero
     else pure $ Atom atom

parseBool :: Parser (SchemeValue m)
parseBool = do _ <- string "#"
               x <- oneOf "tf"
               pure $ case x of
                        't' -> Bool True
                        'f' -> Bool False
                        _ -> Bool False

parseDecimalNumber :: Parser (SchemeValue m)
parseDecimalNumber = do
  _ <- try (many (string "#d"))
  sign <- many (oneOf "-")
  num <- many1 digit
  if (length sign) > 1
     then pzero
     else pure $ (Number . read) $ sign ++ num

parseNumber :: Parser (SchemeValue m)
parseNumber = parseDecimalNumber <?>
              "Unable to parse number"

parseHexScalar :: String -> GenParser Char st Char
parseHexScalar num = do
    let ns = readHex num
    case ns of
        [] -> fail $ "Unable to parse hex value " ++ show num
        _ -> pure $ DC.chr $ fst $ head ns

parseEscapedChar :: forall st . GenParser Char st Char
parseEscapedChar = do
  _ <- char '\\'
  c <- anyChar
  case c of
    'a' -> pure '\a'
    'b' -> pure '\b'
    'n' -> pure '\n'
    't' -> pure '\t'
    'r' -> pure '\r'
    'x' -> do
        num <- many $ letter <|> digit
        _ <- char ';'
        parseHexScalar num
    _ -> pure c

parseString :: Parser (SchemeValue m)
parseString = do
  _ <- char '~'
  x <- many (parseEscapedChar <|> noneOf "~")
  _ <- char '~'
  pure $ String x

parseList :: Parser (SchemeValue m)
parseList = liftM List $ sepBy parseExpr whiteSpace

parseDottedList :: Parser (SchemeValue m)
parseDottedList = do
  phead <- endBy parseExpr whiteSpace
  case phead of
    [] -> pzero
    _ -> do
      ptail <- dot >> parseExpr
      case ptail of
        DottedList ls l -> pure $ DottedList (phead ++ ls) l
        List (Atom "unquote" : _) -> pure $ DottedList phead ptail 
        List ls -> pure $ List $ phead ++ ls
        _ -> pure $ DottedList phead ptail

parseQuoted :: Parser (SchemeValue m)
parseQuoted = do
  _ <- lexeme $ char '\''
  x <- parseExpr
  pure $ List [Atom "quote", x]

parseQuasiQuoted :: Parser (SchemeValue m)
parseQuasiQuoted = do
  _ <- lexeme $ char '`'
  x <- parseExpr
  pure $ List [Atom "quasiquote", x]

parseUnquoted :: Parser (SchemeValue m)
parseUnquoted = do
  _ <- try (lexeme $ char ',')
  x <- parseExpr
  pure $ List [Atom "unquote", x]

parseUnquoteSpliced :: Parser (SchemeValue m)
parseUnquoteSpliced = do
  _ <- try (lexeme $ string ",@")
  x <- parseExpr
  pure $ List [Atom "unquote-splicing", x]

parseExpr :: Parser (SchemeValue m)
parseExpr =
  try (lexeme parseNumber)
  <|> parseUnquoteSpliced
  <|> lexeme parseString
  <|> try parseAtom
  <|> lexeme parseBool
  <|> parseQuoted
  <|> parseQuasiQuoted
  <|> parseUnquoted
  <|> try (parens parseList)
  <|> parens parseDottedList
  <|> try (brackets parseList)
  <|> brackets parseDottedList
  <?> "Expression"

mainParser :: Parser (SchemeValue m)
mainParser = do
  _ <- whiteSpace
  parseExpr

readOrThrow :: Parser a -> String -> EitherSchemeError m a
readOrThrow parser input = case parse parser "scheme" input of
    Left err -> Left $ Parser err
    Right val -> pure val

readExpr :: String -> EitherSchemeError m (SchemeValue m)
readExpr = readOrThrow mainParser

readExprList :: String -> EitherSchemeError m [SchemeValue m]
readExprList = readOrThrow (endBy mainParser whiteSpace)

getVar :: SchemeC' m r => String -> P.Sem r (SchemeValue m)
getVar i = do
  res <- P.get >>= getVar' i
  case res of
    Nothing -> P.throw $ UnboundVar i
    Just v -> pure v
    where
      getVar' :: SchemeC' m r => String -> Environment m -> P.Sem r (Maybe (SchemeValue m))
      getVar' i env = case (HM.lookup i (bindings env)) of
        Nothing -> case (parentEnv env) of
          Just env' -> getVar' i env'
          Nothing -> pure Nothing
        v -> pure v

defineVar :: SchemeC' m r => String -> SchemeValue m -> P.Sem r (SchemeValue m)
defineVar i v = P.modify (\(Environment a b) -> Environment a (HM.insert i v b)) >> pure v

envStepDown :: SchemeC' m r => P.Sem r ()
envStepDown = P.modify (\env -> Environment (Just env) HM.empty)

envStepUp :: SchemeC' m r => P.Sem r ()
envStepUp = P.modify (\e@(Environment p _) -> maybe e id p)

bindVars :: SchemeC' m r => [(String, SchemeValue m)] -> P.Sem r ()
bindVars ls = P.modify (\(Environment a b) -> Environment a (HM.union (HM.fromList ls) b))

extendEnv :: SchemeC' m r => Environment m -> [(String, SchemeValue m)] -> Environment m
extendEnv env ls = Environment (parentEnv env) (HM.union (bindings env) (HM.fromList ls))

makeNullContinuation :: SchemeC' m r => P.Sem r (Continuation m)
makeNullContinuation = P.get >>= \x -> pure $ Continuation x Nothing Nothing

makeCPS :: SchemeC' m r => SchemeValue m
        -> (SchemeValue m -> Maybe [SchemeValue m] -> P.Sem r (SchemeValue m))
        -> P.Sem r (Continuation m)
makeCPS cont@(Cont _) cps = do
  env <- P.get
  pure $ Continuation env (Just (HF $ HaskellFunc cps Nothing)) (Just cont)
makeCPS cont _ = P.throw $ TypeMismatch "continuation" cont

makeCPSWArgs :: SchemeC' m r => SchemeValue m
             -> (SchemeValue m -> Maybe [SchemeValue m] -> P.Sem r (SchemeValue m))
             -> [SchemeValue m]
             -> P.Sem r (Continuation m)
makeCPSWArgs cont@(Cont _) cps args = do
  env <- P.get
  pure $ Continuation env (Just (HF $ HaskellFunc cps (Just args))) (Just cont)
makeCPSWArgs cont _ _ = P.throw $ TypeMismatch "continuation" cont

validateFuncParams :: [SchemeValue m] -> Maybe Int -> Either (SchemeError m) Bool
validateFuncParams ps (Just n) = do
  if length ps /= n
    then Left $ NumArgs (Just n) ps
    else validateFuncParams ps Nothing
validateFuncParams ps Nothing = do
  let syms = filter filterArgs ps
  if (length syms) /= (length ps)
    then Left $ Default $ "Invalid lambda parameter(s)"
    else do
    let strs = DL.sort $ map (\(Atom a) -> a) ps
    case dupe strs of
      Just d -> Left $ Default $ "Duplicate lambda parameter " ++ d
      Nothing -> pure True
 where
  filterArgs (Atom _) = True
  filterArgs _ = False
  dupe (a : b : rest)
    | a == b = Just a
    | otherwise = dupe (b : rest)
  dupe _ = Nothing

apply :: SchemeC' m r => SchemeValue m -> [SchemeValue m] -> P.Sem r (SchemeValue m)
apply f a | trace ("apply " ++ show f ++ " " ++ show a) False = undefined
apply (PrimitiveFunc func) args = func args
apply (Func params varargs body) args =
  if length params /= length args && isNothing varargs
  then P.throw $ NumArgs (Just $ length params) args
  else do
    envStepDown
    bindVars $ zip params args
    bindVarArgs varargs
    res <- liftM last $ mapM eval body
    envStepUp
    pure res
  where
    bindVarArgs arg = case arg of
      Just argName -> bindVars [(argName, List (drop (length params) args))]
      Nothing -> pure ()
apply (Cont cont@(Continuation {contClosure = env})) args = do
  P.put env
  P.put cont
  case (length args) of
    0 -> P.throw $ NumArgs (Just 1) []
    1 -> continueEval (head args) Nothing
    _ -> continueEval (head args) (Just $ tail args)
apply v _ = P.throw $ TypeMismatch "function" v

continueEval :: SchemeC' m r => SchemeValue m -> Maybe [SchemeValue m] -> P.Sem r (SchemeValue m)
continueEval e a | trace ("continueEval " ++ show e ++ " " ++ show a) False = undefined
continueEval e a = P.get >>= (\x -> continueEval' (Cont x) e a)
  where
    continueEval' :: SchemeC' m r => SchemeValue m -> SchemeValue m -> Maybe [SchemeValue m] -> P.Sem r (SchemeValue m)
    continueEval' (Cont (Continuation cEnv (Just (HF hf)) (Just (Cont nCont)))) val xargs = do
      let (HaskellFunc f' a') = hf
      let args' = case a' of
                    Nothing -> xargs
                    Just e -> Just e
      P.put cEnv
      P.put nCont
      f' val args'
    continueEval' (Cont (Continuation cEnv (Just (SF sf)) (Just cCont))) val extraArgs = do
      case sf of
        [] -> case cCont of
          Cont _ -> continueEval' cCont val extraArgs 
          _ -> pure val
        (lv : lvs) -> do
          P.put cEnv
          P.put (Continuation cEnv (Just (SF lvs)) (Just cCont))
          eval lv
    continueEval' (Cont (Continuation cEnv Nothing (Just c@(Cont cCont)))) val xargs = do
      P.put cEnv
      P.put cCont
      continueEval' c val xargs
    continueEval' (Cont (Continuation _ Nothing Nothing)) val _ = pure val
    continueEval' _ _ _ = P.throw $ Default "Internal error in continueEval"

eval :: SchemeC' m r => SchemeValue m -> P.Sem r (SchemeValue m)
eval e | trace ("eval " ++ show e) False = undefined
eval (Atom i) = do
  val <- getVar i
  continueEval val Nothing
eval val@(Number _) = continueEval val Nothing
eval val@(String _) = continueEval val Nothing
eval val@(Bool _) = continueEval val Nothing
eval (List [Atom "quote", val]) = continueEval val Nothing
eval (List [Atom "if", cond, code1, code2]) = do
  cont <- P.get
  makeCPS (Cont cont) cps >>= P.put
  continueEval cond Nothing
  where
    cps e _ = do
      e' <- eval e
      case e' of
        Bool False -> eval code2
        Bool True -> eval code1
        badCond -> P.throw $ TypeMismatch "bool" badCond
eval (List [Atom "define", Atom var, form]) = eval form >>= defineVar var
eval (List (Atom "define" : List (Atom var : params) : body)) = do
  _ <- P.fromEither $ validateFuncParams params Nothing
  res <- defineVar var (Func (map show params) Nothing body)
  continueEval res Nothing
eval (List (Atom "define" : DottedList (Atom var : params) varargs : body)) = do
  _ <- P.fromEither $ validateFuncParams (params ++ [varargs]) Nothing
  (pure $ Func (map show params) (Just $ show varargs) body) >>= defineVar var
eval (List (Atom "lambda" : List params : body)) = do
  _ <- P.fromEither $ validateFuncParams params Nothing
  pure (Func (map show params) Nothing body)
eval (List (Atom "lambda" : DottedList params varargs : body)) = do
  _ <- P.fromEither $ validateFuncParams (params ++ [varargs]) Nothing
  pure (Func (map show params) (Just $ show varargs) body)
eval (List (Atom "lambda" : varargs@(Atom _) : body)) =
  pure (Func [] (Just $ show varargs) body)
eval (List (function : args)) = do
  func <- eval function
  argVals <- mapM eval args
  apply func argVals
eval val = P.throw $ BadSpecialForm val

plus :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
plus ([(Number x), (Number y)]) = pure $ Number $ x + y
plus ([x, y]) = P.throw $ TypeMismatch "integer" (List [x, y])
plus badArgList = P.throw $ NumArgs (Just 2) badArgList

car :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
car [List (x : _)] = pure x
car [DottedList (x : _) _] = pure x
car [badArg] = P.throw $ TypeMismatch "list" badArg
car badArgList = P.throw $ NumArgs (Just 1) badArgList

cdr :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
cdr [List (_ : xs)] = pure $ List xs
cdr [DottedList [_] x] = pure x
cdr [DottedList (_ : xs) x] = pure $ DottedList xs x
cdr [badArg] = P.throw $ TypeMismatch "list" badArg
cdr badArgList = P.throw $ NumArgs (Just 1) badArgList

cons :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
cons [x1, List []] = pure $ List [x1]
cons [x, List xs] = pure $ List $ x : xs
cons [x, DottedList xs xlast] = pure $ DottedList (x : xs) xlast
cons [x1, x2] = pure $ DottedList [x1] x2
cons badArgList = P.throw $ NumArgs (Just 2) badArgList

equal :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
equal [l1@(List l1'), l2@(List l2')] = do
  l <- mapM equalPair (zip l1' l2')
  pure $ Bool $ (length l1' == length l2') && (and l)
  where
    equalPair (x, y) = do
      e <- equal [x, y]
      case e of
        Bool val -> pure val
        _ -> pure False
equal [(DottedList xs x), (DottedList ys y)] = equal [(List $ xs ++ [x]), (List $ ys ++ [y])]
equal [arg1, arg2] = pure $ primEqual arg1 arg2
  where
    primEqual (Number x) (Number y) = Bool $ x == y
    primEqual (String x) (String y) = Bool $ x == y
    primEqual (Bool x) (Bool y) = Bool $ x == y
    primEqual _ _ = Bool False
equal badArgList = P.throw $ NumArgs (Just 2) badArgList

stringLength :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
stringLength [String s] = pure $ Number $ length s
stringLength [badType] = P.throw $ TypeMismatch "string" badType
stringLength badArgList = P.throw $ NumArgs (Just 1) badArgList

substring :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
substring [(String s), (Number start), (Number end)] =
  do let slength = end - start
     pure $ String $ (take slength . drop start) s
substring [badType] = P.throw $ TypeMismatch "string number number" badType
substring badArgList = P.throw $ NumArgs (Just 3) badArgList

stringAppend :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
stringAppend [(String s)] = pure $ String s
stringAppend (String st : sts) = do
  rest <- stringAppend sts
  case rest of
    String s -> pure $ String $ st ++ s
    other -> P.throw $ TypeMismatch "string" other
stringAppend [] = pure $ String ""
stringAppend [badType] = P.throw $ TypeMismatch "string" badType
stringAppend  badArgList = P.throw $ NumArgs (Just 1) badArgList

isDottedList :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
isDottedList ([DottedList _ _]) = pure $ Bool True
isDottedList ([List []]) = pure $ Bool False
isDottedList ([List _]) = pure $ Bool True
isDottedList _ = pure $ Bool False

isProcedure :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
isProcedure ([Cont _]) = pure $ Bool True
isProcedure ([PrimitiveFunc _]) = pure $ Bool True
isProcedure ([Func {}]) = pure $ Bool True
isProcedure _ = pure $ Bool False

isList :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
isList ([List _]) = pure $ Bool True
isList _ = pure $ Bool False

isNull :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
isNull ([List []]) = pure $ Bool True
isNull _ = pure $ Bool False

isSymbol :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
isSymbol ([Atom _]) = pure $ Bool True
isSymbol _ = pure $ Bool False

symbolToString :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
symbolToString ([Atom a]) = pure $ String a
symbolToString [notAtom] = P.throw $ TypeMismatch "symbol" notAtom
symbolToString [] = P.throw $ NumArgs (Just 1) []
symbolToString args@(_ : _) = P.throw $ NumArgs (Just 1) args

stringToSymbol :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
stringToSymbol ([String s]) = pure $ Atom s
stringToSymbol [] = P.throw $ NumArgs (Just 1) []
stringToSymbol [notString] = P.throw $ TypeMismatch "string" notString
stringToSymbol args@(_ : _) = P.throw $ NumArgs (Just 1) args

isString :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
isString ([String _]) = pure $ Bool True
isString _ = pure $ Bool False

isBoolean :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
isBoolean ([Bool _]) = pure $ Bool True
isBoolean _ = pure $ Bool False

currEnv :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
currEnv ([]) = do
  env <- P.get
  pure $ Env env
currEnv a = P.throw $ NumArgs (Just 0) a

callCC :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
callCC [func] = do
  cont <- P.get
  case cont of
    Continuation {} -> case func of
      Cont _ -> apply func [Cont cont] 
      PrimitiveFunc f -> do
        result <- f [Cont cont]
        case cont of
          Continuation {contClosure = cEnv} -> do
            P.put cEnv
            continueEval result Nothing
      Func _ (Just _) _ -> apply func [Cont cont]
      Func aparams _ _ ->
        if (length aparams) == 1
        then apply func [Cont cont]
        else P.throw $ NumArgs (Just (length aparams)) [Cont cont]
callCC badArgList = P.throw $ NumArgs (Just 1) badArgList

evalF :: SchemeC' m r => [SchemeValue m] -> P.Sem r (SchemeValue m)
evalF [val] = do
  cont <- P.get
  case cont of
    Continuation {contClosure = env} -> do
      P.put env
      eval val
evalF badArgList = P.throw $ NumArgs (Just 1) badArgList

stdEnv :: SchemeC' m r => Environment m
stdEnv = Environment Nothing $ HM.fromList [ ("+", PrimitiveFunc plus)
                                           , ("car", PrimitiveFunc car)
                                           , ("cdr", PrimitiveFunc cdr)
                                           , ("cons", PrimitiveFunc cons)
                                           , ("equal", PrimitiveFunc equal)
                                           , ("call/cc", PrimitiveFunc callCC)
                                           , ("eval", PrimitiveFunc evalF)
                                           , ("string-length", PrimitiveFunc stringLength)
                                           , ("substring", PrimitiveFunc substring)
                                           , ("string-append", PrimitiveFunc stringAppend)
                                           , ("is-dotted-list", PrimitiveFunc isDottedList)
                                           , ("is-procedure", PrimitiveFunc isProcedure)
                                           , ("is-list", PrimitiveFunc isList)
                                           , ("is-null", PrimitiveFunc isNull)
                                           , ("is-symbol", PrimitiveFunc isSymbol)
                                           , ("is-bool", PrimitiveFunc isBoolean)
                                           , ("is-string", PrimitiveFunc isString)
                                           , ("string-to-symbol", PrimitiveFunc stringToSymbol)
                                           , ("symbol-to-string", PrimitiveFunc symbolToString)
                                           , ("get-env", PrimitiveFunc currEnv)]

nullC :: SchemeC' m r => Continuation m
nullC = Continuation stdEnv Nothing Nothing

evalScheme :: (SchemeC' m r, Monad m) => SchemeValue m -> m (Continuation m, (Environment m, Either (SchemeError m) (SchemeValue m)))
evalScheme = P.runM . P.runState nullC .
             P.runState stdEnv . P.runError . eval

evalScheme' :: (SchemeC' m r, Monad m) => Continuation m -> Environment m -> SchemeValue m -> m (Continuation m, (Environment m, Either (SchemeError m) (SchemeValue m)))
evalScheme' cont env = P.runM . P.runState cont .
             P.runState env . P.runError . eval

-- may throw an error
evalSchemeErased :: (SchemeC' m r, Monad m) => SchemeValue m -> m SchemeValueErased
evalSchemeErased = ((<$>) (eraseEff . fromJust . either (const Nothing) Just . snd . snd)) . evalScheme

parseEval :: Monad m => String -> m (Either ParseError SchemeValueErased)
parseEval str = case parse mainParser "scheme" str of
    Left err -> pure (Left err)
    Right expr -> Right <$> (evalSchemeErased expr)

main' :: String -> IO ()
main' str = do
  case readExpr str of
    Left err -> print err
    Right expr -> do
      let (c, (e, res)) =
            (runIdentity .
                 P.runM .
                 P.runState nullC .
                 P.runState stdEnv .
                 P.runError .
                 eval) expr
      print res
      print e
      print c
