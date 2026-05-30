import Text.Parsec ((<|>), parse, try, many, getPosition, choice, eof)
import Text.Parsec.String (Parser)
import Text.Parsec.Char ( alphaNum, anyChar, char, digit
                        , letter, noneOf, spaces, string)
import Text.Parsec.Combinator (option, many1, sepBy1, chainl1, chainr1, between)
import Text.Printf (printf)
import Data.Map (Map, empty, insert, lookup, singleton, union)
import Data.Set (Set, fromList, member)
import qualified Control.Monad.Fail as Fail
import Control.Monad.State (StateT, runStateT, get, modify, put, lift)
import Prelude hiding (lookup)

keywords :: Set String
keywords = fromList [ "if", "then", "else", "let", "print", "R", "B", "S", "C"
                    , "True", "False" ]

data Type = TNum | TBool | TChar | TString | TFun Type Type deriving (Eq)

instance Show Type where
  show TNum       = "Number"
  show TBool      = "Boolean"
  show TChar      = "Char"
  show TString    = "String"
  show (TFun d r) = printf "Function : %s -> %s" (show d) (show r)

data Expression = Add     Expression Expression
                | Minus   Expression Expression
                | Mult    Expression Expression
                | Div     Expression Expression
                | Power   Expression Expression
                | Neg     Expression Expression
                | And     Expression Expression
                | Or      Expression Expression
                | Imply   Expression Expression
                | Equiv   Expression Expression
                | Ineq    Expression Expression
                | Great   Expression Expression
                | Less    Expression Expression
                | GreatE  Expression Expression
                | LessE   Expression Expression
                | Not     Expression
                | App     Expression Expression
                | Lambda  String     Type       Expression
                | If      Expression Expression Expression
                | Let     String     Type       Expression
                | Assign  String     Expression
                | Seq     Expression Expression
                | Print   Expression
                | Par     Expression
                | Scope   Expression
                | LitNum  Double
                | LitBool Bool
                | LitChar Char
                | LitStr  String
                | Var     String

ifThenElse :: String
ifThenElse = "if %s then %s else %s"

instance Show Expression where
  show (Add    e1 e2) = printf "%s + %s"           (show e1) (show e2)
  show (Minus  e1 e2) = printf "%s - %s"           (show e1) (show e2)
  show (Mult   e1 e2) = printf "%s × %s"           (show e1) (show e2)
  show (Div    e1 e2) = printf "%s ÷ %s"           (show e1) (show e2)
  show (Power  e1 e2) = printf "%s ^ %s"           (show e1) (show e2)
  show (And    e1 e2) = printf "%s && %s"          (show e1) (show e2)
  show (Or     e1 e2) = printf "%s || %s"          (show e1) (show e2)
  show (Imply  e1 e2) = printf "%s => %s"          (show e1) (show e2)
  show (Equiv  e1 e2) = printf "%s == %s"          (show e1) (show e2)
  show (Ineq   e1 e2) = printf "%s != %s"          (show e1) (show e2)
  show (Great  e1 e2) = printf "%s > %s"           (show e1) (show e2)
  show (Less   e1 e2) = printf "%s < %s"           (show e1) (show e2)
  show (GreatE e1 e2) = printf "%s >= %s"          (show e1) (show e2)
  show (LessE  e1 e2) = printf "%s <= %s"          (show e1) (show e2)
  show (Not    e)     = printf "!%s"               (show e)
  show (App   e1 e2)  = printf "%s %s"             (show e1) (show e2)
  show (Lambda v t e) = printf "λ%s : %s -> %s"    v         (show t)  (show e)
  show (If  g t f)    = printf ifThenElse          (show g)  (show t)  (show f)
  show (Let v t e)    = printf "let %s : %s := %s" v         (show t)  (show e)
  show (Seq   e1 e2)  = printf "%s ; %s"           (show e1) (show e2)
  show (Par e)        = printf "(%s)"              (show e)
  show (Scope e)      = printf "{%s}"              (show e)
  show (Print e)      = printf "print %s"          (show e)
  show (LitNum  n)    = show                       n
  show (LitBool b)    = show                       b
  show (LitChar c)    = show                       c
  show (LitStr  s)    = s
  show (Var     v)    = v

--------------------------------------------------------------------------------
------------------------ Auxiliar functions for parsers ------------------------
--------------------------------------------------------------------------------

-- Shift every trailing space after parsing
lexem :: Parser a -> Parser a
lexem p = p <* spaces

-- Shitf a single *legal* word
pWord :: Parser String
pWord = do
  first <- letter <|> char '_'
  rest  <- many (alphaNum <|> char '_' <|> char '\'')
  pure (first:rest)

-- Ask if a read word is whether a keyword or not
pKeyWord :: String -> Parser ()
pKeyWord kw = lexem $ try $ do
  word <- pWord
  if word == kw then pure () else fail $ printf "Keyword %s was expected" kw

-- Ask if a parsed string is an operator
pOperator :: String -> Parser String
pOperator = lexem . try . string

-- Auxiliar for parsing types
pType :: Parser Type
pType = try pFunType <|> pAtomType where
  pAtomType = (pKeyWord "R" >> pure TNum)
          <|> (pKeyWord "B" >> pure TBool)
          <|> (pKeyWord "C" >> pure TChar)
          <|> (pKeyWord "S" >> pure TString)
          <|> between (lexem $ char '(') (lexem $ char ')') pType

  pFunType = do
    d <- lexem pAtomType
    _ <- pOperator "->"
    r <- lexem pType
    pure $ TFun d r

--------------------------------------------------------------------------------
-------------------------------- Actual Parsers --------------------------------
--------------------------------------------------------------------------------

-- Global parser
pLoCal :: Parser Expression
pLoCal = do
  spaces
  e <- pExpr
  eof
  pure e

-- Parsing expresions
pExpr :: Parser Expression
pExpr = pSequence

-- Parsing Sequences
pSequence :: Parser Expression
pSequence = lexem $ chainl1 pPrint pSequence' where
  pSequence' = do
    _ <- pOperator ";"
    pure Seq

-- Parsing prints
pPrint :: Parser Expression
pPrint = (do
  _ <- pKeyWord "print"
  e <- pDef
  pure $ Print e) <|> pDef

-- Parsing definitions
pDef :: Parser Expression
pDef = pLet <|> try pAssign <|> pLambda

pLet :: Parser Expression
pLet = do
  _ <- pKeyWord "let"
  v <- lexem pVariable
  _ <- pOperator ":"
  t <- lexem $ pType
  _ <- pOperator ":="
  e <- lexem $ pLambda
  pure $ Let v t e

pAssign :: Parser Expression
pAssign = do
  v <- lexem pVariable
  _ <- pOperator ":="
  e <- lexem $ pLambda
  pure $ Assign v e

-- Parsing functional abstraction (lambdas)
pLambda :: Parser Expression
pLambda = (do
    _ <- pOperator "/."
    v <- lexem pVariable
    _ <- pOperator ":"
    t <- lexem pType
    _ <- pOperator "=>"
    f <- lexem $ pExpr
    pure $ Lambda v t f) <|> pConditional

-- Parsing conditional expression (if-then-else)
pConditional :: Parser Expression
pConditional = (do
  _  <- pKeyWord "if"
  e1 <- lexem pLambda
  _  <- pKeyWord "then"
  e2 <- lexem pExpr
  _  <- pKeyWord "else"
  e3 <- lexem pExpr
  pure $ If e1 e2 e3) <|> pImply

-- Parsing implication
pImply :: Parser Expression
pImply = lexem $ chainr1 pOr pImply' where
  pImply' = do
    _ <- pOperator "=>"
    pure Imply

-- Parsing logical or
pOr :: Parser Expression
pOr = lexem $ chainl1 pAnd pOr' where
  pOr' = do
    _ <- pOperator "||"
    pure Or

-- Parsing logical and
pAnd :: Parser Expression
pAnd = lexem $ chainl1 pComparison pAnd' where
  pAnd' = do
    _ <- pOperator "&&"
    pure And

-- Parsing comparations
pComparison :: Parser Expression
pComparison = do
  left <- pAddMinus
  comp <- option Nothing (Just <$> pComparators)
  case comp of
    Nothing    -> pure left
    Just comp' -> do
      right <- pAddMinus
      pure $ comp' left right
  where
    mapper :: (String, Expression -> Expression -> Expression) ->
      Parser (Expression -> Expression -> Expression)
    mapper (comp, constr) = pOperator comp >> pure constr
    comparators :: [(String, Expression -> Expression -> Expression)]
    comparators = [ ("==", Equiv), ("!=", Ineq)
                  , ("<=", LessE), ("<", Less)
                  , (">=", GreatE), (">", Great)
                  ]
    pComparators = choice $ map mapper comparators

-- Parsing sums
pAddMinus :: Parser Expression
pAddMinus = lexem $ chainl1 pMultDiv pAddMinus' where
  pAddMinus' = do
    op <- pOperator "+" <|> pOperator "-"
    pure (if op == "+" then Add else Minus)

-- Parsing products
pMultDiv :: Parser Expression
pMultDiv = lexem $ chainl1 pPower pMultDiv' where
  pMultDiv' = do
    op <- pOperator "*" <|> pOperator "/"
    pure $ if op == "*" then Mult else Div

-- Parsing powers
pPower :: Parser Expression
pPower = lexem $ chainr1 pApp pPower' where
  pPower' = do
    _ <- pOperator "^"
    pure Power

-- Parsing unary operations (negation and negative)
pUnary :: Parser Expression
pUnary = (do
  op <- try (pOperator "-" <|> pOperator "!")
  ex <- pApp
  pure $ if op == "-" then Minus (LitNum 0.0) ex else Not ex) <|> pFactor

-- Parsing function application
pApp :: Parser Expression
pApp = lexem $ chainl1 pFactor $ pure App

-- Parsing literals and variables
pFactor :: Parser Expression
pFactor = pStr <|> pChar <|> pNum <|> pBool <|> pPar <|> pScope <|> pVar
  where pVar = (Var <$> pVariable)

-- Parsing strings
pStr :: Parser Expression
pStr = lexem $ do
  _ <- char '"'
  s <- many (noneOf "\"")
  _ <- char '"'
  pure (LitStr s)

-- Parsing chars
pChar :: Parser Expression
pChar = lexem $ do
  _ <- char '\''
  c <- anyChar
  _ <- char '\''
  pure (LitChar c)

-- Parsing numbers
pNum :: Parser Expression
pNum = lexem $ do
  whole <- many1 digit
  decimal <- option ".0" $ pDecimal
  pure (LitNum (read $ whole ++ decimal :: Double))
  where
    pDecimal = do
      point <- char '.'
      decimal <- many1 digit
      pure (point:decimal)

pBool :: Parser Expression
pBool = lexem $ choice $ map (\(s, e) -> pOperator s >> pure e) bools where
  bools = [("True", LitBool True), ("False", LitBool False)]

-- Parsing parenthesis
pPar :: Parser Expression
pPar = do
  _ <- pOperator "("
  e <- pExpr
  _ <- pOperator ")"
  pure $ Par e

-- Parsing scopes
pScope :: Parser Expression
pScope = do
  _ <- pOperator "{"
  e <- pExpr
  _ <- pOperator "}"
  pure $ Scope e

-- Parsing variables
pVariable :: Parser String
pVariable = lexem $ try $ do
  word <- pWord
  if member word keywords then fail $ "Keywords can't be identifiers" else
    pure word

--------------------------------------------------------------------------------
------------------------------- Static analysis --------------------------------
--------------------------------------------------------------------------------
type SymbolTable = [Map String Type]

type LoCalState a = StateT SymbolTable (Either String) a

isFunc :: Type -> Bool
isFunc (TFun _ _) = True
isFunc _          = False

deepLookup :: String -> [Map String Type] -> Maybe Type
deepLookup _ [] = Nothing
deepLookup v (m:ms) = case lookup v m of
  Nothing -> deepLookup v ms
  Just t  -> Just t

flatAST :: Expression -> Expression
flatAST (Par e)    = flatAST e
flatAST expression = expression

biOperations :: Expression -> Expression -> Type -> String -> LoCalState Type
biOperations e1 e2 t e = do
  t1 <- staticAnalysis e1
  t2 <- staticAnalysis e2
  if t1 == t2 && t1 == t then pure t else lift $ Left e

comparations :: Expression -> Expression -> String -> LoCalState Type
comparations e1 e2 e = do
  t1 <- staticAnalysis e1
  t2 <- staticAnalysis e2
  if t1 == t2 && not (isFunc t1) then pure TBool else lift $ Left e

getScopes :: LoCalState SymbolTable
getScopes = do
  st <- get
  if null st then lift $ Left "Error: no active scope was found" else pure st

matchTypes :: Type -> Type -> LoCalState Type
matchTypes t1 t2 =
  if t1 == t2 then pure t1 else lift $ Left $ tMatchError (show t1) (show t2)

tNumError :: String
tNumError = "Type Error: Aritmethic operations are only for numbers"

tBoolError :: String
tBoolError = "Type Error: Boolean operations are only for True/False"

tComparError :: String
tComparError = "Type Error: You can't compare differents types"

tGuardError :: String
tGuardError = "Type Error: Condition of an if-then-else must be boolean"

tMatchError :: String -> String -> String
tMatchError t1 t2 = printf "Type Error: Can't match type %s with type %s" t1 t2

varError :: String -> String
varError var = printf "Error: variable %s doesn't exist" var

varRedefError :: String -> String
varRedefError v = printf "Error: You were intended to redefine variable %s" v

staticAnalysis :: Expression -> LoCalState Type
staticAnalysis (Seq e1 e2)  = do
  _ <- staticAnalysis e1
  staticAnalysis e2
staticAnalysis (Print   e)  = staticAnalysis e
staticAnalysis (Let v t e)  = do
  symbolTable <- getScopes
  let
    st  = head symbolTable
    sts = tail symbolTable
  case lookup v (head symbolTable) of
    Just _  -> lift $ Left $ varRedefError v
    Nothing -> case flatAST e of
      Lambda _ _ _ -> do
        put (insert v t st : sts)
        pure t
      _            -> do
        t' <- staticAnalysis e
        _  <- matchTypes t t'
        put (insert v t' st : sts)
        pure t
staticAnalysis (Assign v e) = do
  t' <- staticAnalysis e
  st <- getScopes
  case deepLookup v st of
    Nothing -> lift $ Left $ varError v
    Just t  -> matchTypes t t'
staticAnalysis (Lambda v  t e) = do
  modify (singleton v t:)
  t' <- staticAnalysis e
  modify tail
  pure $ TFun t t'
staticAnalysis (If     g t f)  = do
  guardType <- staticAnalysis g
  trueType  <- staticAnalysis t
  falseType <- staticAnalysis f
  if guardType == TBool && trueType == falseType
  then pure trueType
  else if guardType /= TBool
  then lift $ Left tGuardError
  else lift $ Left $ tMatchError (show trueType) (show falseType)
staticAnalysis (Imply  e1 e2) = biOperations  e1 e2 TBool tBoolError
staticAnalysis (Or     e1 e2) = biOperations  e1 e2 TBool tBoolError
staticAnalysis (And    e1 e2) = biOperations  e1 e2 TBool tBoolError
staticAnalysis (Equiv  e1 e2) = comparations  e1 e2       tComparError
staticAnalysis (Ineq   e1 e2) = comparations  e1 e2       tComparError
staticAnalysis (Great  e1 e2) = comparations  e1 e2       tComparError
staticAnalysis (Less   e1 e2) = comparations  e1 e2       tComparError
staticAnalysis (GreatE e1 e2) = comparations  e1 e2       tComparError
staticAnalysis (LessE  e1 e2) = comparations  e1 e2       tComparError
staticAnalysis (Add    e1 e2) = biOperations  e1 e2 TNum  tNumError
staticAnalysis (Minus  e1 e2) = biOperations  e1 e2 TNum  tNumError
staticAnalysis (Mult   e1 e2) = biOperations  e1 e2 TNum  tNumError
staticAnalysis (Div    e1 e2) = biOperations  e1 e2 TNum  tNumError
staticAnalysis (Power  e1 e2) = biOperations  e1 e2 TNum  tNumError
staticAnalysis (Not    e)     = do
  t' <- staticAnalysis e
  if t' == TBool then pure TBool else lift $ Left tBoolError
staticAnalysis (App    e1 e2)  = do
  t1 <- staticAnalysis e1
  t2 <- staticAnalysis e2
  case t1 of
    tFunc@(TFun par ret)
      | par == t2 -> pure ret
      | otherwise -> lift $ Left $ tMatchError (show tFunc) (show t2)
    t             -> lift $ Left $ tMatchError (show t)     (show t2)
staticAnalysis (LitNum  _)  = pure TNum
staticAnalysis (LitBool _)  = pure TBool
staticAnalysis (LitChar _)  = pure TChar
staticAnalysis (LitStr  _)  = pure TString
staticAnalysis (Par     e)  = staticAnalysis e
staticAnalysis (Scope   e)  = do
  modify (empty:)
  t <- staticAnalysis e
  modify tail
  pure t
staticAnalysis (Var    v)      = do
  symbolTable <- get
  case deepLookup v symbolTable of
    Nothing -> lift $ Left $ varError v
    Just t  -> pure t

--------------------------------------------------------------------------------
--------------------------------- Interpreter ----------------------------------
--------------------------------------------------------------------------------
data RunTimeResult a = InProgress String (RunTimeResult a)
                     | Fail       String
                     | Success    a

instance (Show a) => Show (RunTimeResult a) where
  show (InProgress s r) = printf "%s\n%s" s $ show r
  show (Fail       s)   = printf "Runtime Error: %s" s
  show (Success    r)   = "" -- printf "Success! Result: %s" $ show r

instance Functor RunTimeResult where
  fmap f (InProgress s r) = InProgress s $ fmap f r
  fmap f (Success r) = Success $ f r
  fmap _ (Fail    s) = Fail s

instance Applicative RunTimeResult where
  pure = Success

  (Success f)      <*> mx = fmap f mx
  (Fail s)         <*> _  = Fail s
  (InProgress s r) <*> mx = InProgress s (r <*> mx)

instance Monad RunTimeResult where
  (Success a)      >>= f = f a
  (Fail s)         >>= _ = Fail s
  (InProgress s r) >>= f = InProgress s (r >>= f)

data Value = VNum     Double
           | VBool    Bool
           | VChar    Char
           | VString  String
           | VClosure String Expression EvalTable

instance Eq Value where
  (VNum n1)    == (VNum n2)    = n1 == n2
  (VBool b1)   == (VBool b2)   = b1 == b2
  (VChar c1)   == (VChar c2)   = c1 == c2
  (VString s1) == (VString s2) = s1 == s2
  _            == _            = False

instance Ord Value where
  compare (VNum n1)    (VNum n2)    = compare n1 n2
  compare (VBool b1)   (VBool b2)   = compare b1 b2
  compare (VChar c1)   (VChar c2)   = compare c1 c2
  compare (VString s1) (VString s2) = compare s1 s2
  compare _            _            = error "Functions are not Ord-able"

instance Show Value where
  show (VNum n)         = show n
  show (VBool b)        = show b
  show (VChar c)        = show c
  show (VString s)      = show s
  show (VClosure s e _) = printf "λ%s -> %s" s $ show e

type EvalTable = Map String Value

unNum :: Value -> Double
unNum (VNum n) = n
unNum _        = undefined -- Unreachable

unBool :: Value -> Bool
unBool (VBool b) = b
unBool _        = undefined -- Unreachable

(==>) :: Bool -> Bool -> Bool
p ==> q = not p || q

biEval :: Expression -> Expression -> EvalTable -> (Value -> a) -> (a -> Value)
  -> (a -> a -> a) -> RunTimeResult (Value, EvalTable)
biEval e1 e2 et unwrap wrap f = do
  (x1, _) <- eval e1 et
  (x2, _) <- eval e2 et
  pure (wrap $ f (unwrap x1) (unwrap x2), et)

comparEval :: Expression -> Expression -> EvalTable -> (Value -> Value -> Bool)
  -> RunTimeResult (Value, EvalTable)
comparEval e1 e2 et f = do
  (v1, _) <- eval e1 et
  (v2, _) <- eval e2 et
  pure (VBool $ f v1 v2, et)

eval :: Expression -> EvalTable -> RunTimeResult (Value, EvalTable)
eval (Seq   e1 e2)        et = itemize e1
  where
    update v e = do
      (val, _) <- eval e  et
      eval e2 $ insert v val et 
    itemize (Par e)        = itemize e
    itemize (Let v _ eIn)  = update v eIn
    itemize (Assign v eIn) = update v eIn
    itemize expr           = do
      (_, et') <- eval expr et
      eval e2 et'
eval (Print    e)         et = do
  (val, _) <- eval e et
  InProgress (show val) $ pure (val, et)
eval (Let  _ _ e)         et = eval e et
eval (Assign v e)         et = do
  (val, _) <- eval e et
  pure (val, insert v val et)
eval (Lambda v t e)       et = pure (VClosure v e et, et)
eval (If g e1 e2) et = do
  (guard, _) <- eval g et
  case guard of
    VBool b -> if b then eval e1 et else eval e2 et
    _       -> Fail "Guard is not boolean"
eval (And    e1 e2)       et = biEval e1 e2 et unBool VBool (&&)
eval (Or     e1 e2)       et = biEval e1 e2 et unBool VBool (||)
eval (Imply  e1 e2)       et = biEval e1 e2 et unBool VBool (==>)
eval (Equiv  e1 e2)       et = comparEval e1 e2 et (==)
eval (Ineq   e1 e2)       et = comparEval e1 e2 et (/=)
eval (Great  e1 e2)       et = comparEval e1 e2 et (>)
eval (Less   e1 e2)       et = comparEval e1 e2 et (<)
eval (GreatE e1 e2)       et = comparEval e1 e2 et (>=)
eval (LessE  e1 e2)       et = comparEval e1 e2 et (<=)
eval (Add   e1 e2)        et = biEval e1 e2 et unNum  VNum  (+)
eval (Minus e1 e2)        et = biEval e1 e2 et unNum  VNum  (-)
eval (Mult  e1 e2)        et = biEval e1 e2 et unNum  VNum  (*)
eval (Div   e1 e2)        et = do
  (VNum n1, _) <- eval e1 et
  (VNum n2, _) <- eval e2 et
  if n2 == 0 then Fail "Runtime Exception: Division by zero"
  else pure (VNum $ n1 / n2, et)
eval (Power e1 e2)        et = biEval e1 e2 et unNum  VNum  (**)
eval (Not    e)           et = do
  (VBool b, _) <- eval e et
  pure (VBool $ not b, et)
eval (App   e1 e2)        et = do
  (VClosure var cuerpo envInterno, _) <- eval e1 et
  (valArg,                         _) <- eval e2 et
  (cont, _) <- eval cuerpo $ insert var valArg $ union envInterno et
  pure (cont, et)
eval (LitNum  n)          et = pure (VNum n, et)
eval (LitBool b)          et = pure (VBool b, et)
eval (LitChar c)          et = pure (VChar c, et)
eval (LitStr  s)          et = pure (VString s, et)
eval (Par      e)         et = eval e et
eval (Scope    e)         et = eval e et
eval (Var     s)          et = case lookup s et of
  Nothing -> Fail "Internal Error: Variable not found after static analysis"
  Just v  -> pure (v, et)

exec :: RunTimeResult Value -> IO ()
exec (InProgress mensaje siguienteEfecto) = do
  putStrLn mensaje
  exec siguienteEfecto
exec r = putStrLn $ show r

runL :: FilePath -> IO ()
runL file = do
  code <- readFile file
  case parse pLoCal file code of
    Left  e   -> putStrLn $ show e
    Right ast -> do
      case runStateT (staticAnalysis ast) [empty] of
        Left e -> putStrLn e
        Right (t, _) -> exec $ fst <$> eval ast empty

instance Fail.MonadFail RunTimeResult where
  fail msg = Fail ("Pattern matching failed in do-block: " ++ msg)

{- Uncomment for debugging
debug :: String -> IO ()
debug program = do
  case parse pLoCal "playground" program of
    Left e    -> putStrLn $ show e
    Right ast -> do
      case runStateT (staticAnalysis ast) [empty] of
        Left e -> putStrLn e
        Right (t, _) -> exec $ fst <$> eval ast empty

main :: IO ()
main = do
  putStrLn "Fibonacci 6"
  debug "let fib : R -> R := (/. n : R => if n <= 1 then n else fib (n - 1) + fib (n - 2));print (fib 6)"
  putStrLn "Print 9.5 and 3.14"
  debug "let x : R := 3.14; {let x : R := 9.5; print x}; print x"
  putStrLn "Crash with variable re-definition"
  debug "let x : R := 3.14; (let x : R := 9.5; print x); print x"
  putStrLn "In both cases, print 9.5, twice"
  putStrLn "  a) With ( )"
  debug "let x : R := 3.14; (x := 9.5; print x); print x"
  putStrLn "  b) With { } --Scopes--"
  debug "let x : R := 3.14; {x := 9.5; print x}; print x"
  putStrLn "It should print 5.0"
  debug "(/. x : R => x := 5; print x) 3.14"
  putStrLn "It should be equivalent to former"
  debug "{let x : R := 3.14; x := 5; print x}"
  putStrLn "Strings: \"Hello, World!\"?"
  debug "print \"Hello, World!\""
  -}
