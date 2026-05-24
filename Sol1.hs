{-# LANGUAGE LambdaCase #-}

import Data.List (group)
import Control.Monad.Free (Free(Pure, Free))
import Data.Map (Map, lookup, insertWith)
import qualified Data.Map as Map
import Control.Monad.State(StateT, runStateT, put, get, liftIO)
import Control.Monad.Except(ExceptT, throwError, runExceptT)
import Data.Char (ord, digitToInt)
import System.IO (hFlush, stdout)
import Safe (headMay)

newtype AccountId = AccountId String deriving (Show, Eq, Ord)
newtype User = User String deriving (Show, Eq)
data Error = InsufficientFunds | AccountNotFound deriving (Show, Eq)

data ATMF a
    = CheckBalance AccountId (Int -> a)
    | Deposit AccountId Int a
    | Withdraw AccountId Int (Either Error a)
    | GetUser AccountId (Maybe User -> a)
instance Functor ATMF where
    {-
      Functor's laws prove
      
      Let g a function and x a type
      
      Identity law (f = id)
      f . g = id . g = g
      f x = id x = x
      
      Composition law (f = f2 . f1)
      fmap (f2 . f1) (Strcuture ... g) = Structure ... ((f2 . f1) . g)
      (f2 . f1) . g = f2 . (f1 . g) (. is associative)
      f2 . (f1 . g) => Structure ... (f2 . (f1 . g))
      Structure ... (f2 . (f1 . g)) = fmap f2 (Structure ... (f1 . g))
      fmap f2 (Structure ... (f1 . g)) = fmap f2 (fmap f1 (Structure ... g))
      f (g x) = (f . g) x (by definition of composition)
      (fmap f2 . fmap f1) (Structure ... g)
      
      Finally,
      
      fmap (f2 . f1) (Strcuture ... g) = (fmap f2 . fmap f1) (Structure ... g)
      
      fmap (f2 . f1) (Structure ... x) = Structure ... ((f2 . f1) . x)
      f (g x) = (f . g) x (by definition of composition)
      Structure ... ((f2 . f1) . x) = Structure ... (f2 (f1 x))
      Structure ... (f2 (f1 x)) = fmap f2 (Structure ... (f1 x))
      fmap f2 (Structure ... (f1 x)) = fmap f2 (fmap f1 (Structure ... x))
      f (g x) = (f . g) x (by definition of composition)
      (fmap f2) . (fmap f1) (Structure ... x)
    -}
    fmap :: (a -> b) -> ATMF a -> ATMF b
    fmap f (CheckBalance aId g) = CheckBalance aId (f . g)
    fmap f (Deposit aId n x)  = Deposit aId n (f x)
    fmap f (Withdraw aId n x) = Withdraw aId n (fmap f x)
    fmap f (GetUser aId g) = GetUser aId (f . g)

checkBalance :: AccountId -> Free ATMF Int
checkBalance aId = Free (CheckBalance aId Pure)

deposit :: AccountId -> Int -> Free ATMF ()
deposit aId n = let x = Pure () in Free (Deposit aId n x)

withdraw :: AccountId -> Int -> Free ATMF (Either Error ())
withdraw aId n = Free (Withdraw aId n (Right (Pure (Right ()))))

getUser :: AccountId -> Free ATMF (Maybe User)
getUser aId = Free (GetUser aId Pure)

transfer :: AccountId -> AccountId -> Int -> Free ATMF (Either Error ())
transfer from to amount = do
  funds <- withdraw from amount
  user <- getUser to
  case funds of
    Left err -> pure (Left err)
    Right () -> do
      case user of
        Nothing -> do
          deposit from amount
          pure (Left AccountNotFound)
        Just _  -> do
          deposit to amount
          pure (Right ())

{-
transfer' :: AccountId -> AccountId -> Float -> Either Error (Free ATMF ())
transfer' from to amount = do
  funds <- result $ withdraw from n
  case funds of
    Left err -> Left err
    Right () -> do
      user <- getUser to <- Here's the Monad's crashing
      **THERE'S NO WAY TO USE THE MONAD FREE INSIDE THE MONAD EITHER.
      THEREFORE, WE CANNOT COMMUTE THESE MONADS**
      case user of
        Nothing -> do
          deposit from amount
          Left AccountNotFound
        Just _  -> Right (deposit to amount)
  where
    n = round amount
    result (Free (Withdraw _ _ x)) = x
-}

newtype BankState = MkBankState (Map AccountId (Int, User))

interpret :: Free ATMF a -> BankState -> (Either Error a, BankState)
interpret atm (MkBankState bankState) = case atm of
  Pure x -> (Right x, MkBankState bankState)
  Free y -> case y of
    CheckBalance aId f -> case Map.lookup aId bankState of
      Nothing -> (Left AccountNotFound, MkBankState bankState)
      Just n  -> interpret (f (fst n)) (MkBankState bankState)
    Deposit aId n x -> interpret x (MkBankState state)
      where
        state :: Map AccountId (Int, User)
        state = insertWith f aId (n, User "") bankState
        f :: (Int, User) -> (Int, User) -> (Int, User)
        f (x1, _) (x2, y2) = (x1 + x2, y2)
    Withdraw aId n s -> case s of
      Right x -> case Map.lookup aId bankState of
        Nothing      -> (Left AccountNotFound, MkBankState bankState)
        Just (k, _) -> let
          failure = (Left InsufficientFunds, MkBankState bankState)
          state = insertWith f aId (n, User "") bankState
          f (x1, _) (x2, y2) = (x2 - x1, y2)
          success = interpret x (MkBankState state) in
          if k < n then failure else success
      Left e -> (Left e, MkBankState bankState)
    GetUser aId f -> case Map.lookup aId bankState of
      Nothing     -> interpret (f Nothing) (MkBankState bankState)
      Just (_, u) -> interpret (f (Just u)) (MkBankState bankState)

accountIDs :: Free ATMF a -> [AccountId]
accountIDs atm = accountIDsTR atm []

accountIDsTR :: Free ATMF a -> [AccountId] -> [AccountId]
accountIDsTR atm aIds = case atm of
  Pure x -> aIds
  Free y -> case y of
    CheckBalance aId f -> accountIDsTR (f 0) (aId:aIds)
    Deposit aId _ next -> accountIDsTR next  (aId:aIds)
    Withdraw aId _ s   -> case s of
      Left _  -> (aId:aIds)
      Right x -> accountIDsTR x (aId:aIds)
    GetUser aId f -> accountIDsTR (f (Just (User ""))) (aId:aIds)
--------------------------------------------------------------------------------
type Weight = Int
newtype Graph a = Graph [(a, [(Weight, a)])]

-- Caminos terminados, Caminos activos, Grafo
newtype MyGraphState a = MyGraphState ([[a]], [[a]], Graph a)

newtype GraphState s a = GraphState { runGraphState :: s -> (a, s) }

instance Functor (GraphState s) where
  fmap :: (a -> b) -> GraphState s a -> GraphState s b
  fmap f (GraphState sa) = GraphState (\s -> let (x, s0) = sa s in (f x, s0))

instance Applicative (GraphState s) where
  pure :: a -> GraphState s a
  pure x = GraphState (\s -> (x, s))
  
  (<*>) :: GraphState s (a -> b) -> GraphState s a -> GraphState s b
  (<*>) (GraphState sf) (GraphState sa) = GraphState (\s -> let
    (fx, s1) = sf s
    (x, s2)  = sa s1 in (fx x, s2))

instance Monad (GraphState s) where
  (>>=) :: GraphState s a -> (a -> GraphState s b) -> GraphState s b
  (>>=) (GraphState sa) f = GraphState (\s -> let
    (x0, s1)      = sa s
    GraphState sb = f x0 in sb s1)

getGraphState :: GraphState s s
getGraphState = GraphState (\s -> (s, s))

putGraphState :: s -> GraphState s ()
putGraphState new = GraphState (\_ -> ((), new))

modifyGraphState :: (s -> s) -> GraphState s ()
modifyGraphState f = GraphState (\s -> ((), f s))

evalGraphState :: GraphState s a -> s -> a
evalGraphState state s = fst $ runGraphState state s

execGraphState :: GraphState s a -> s -> s
execGraphState state s = snd $ runGraphState state s

paths :: forall a . Ord a => a -> Graph a -> [[a]]
paths _ (Graph [])  = []
paths v (Graph xs) = case Prelude.lookup v xs of
  Nothing -> []
  Just ys ->
    let
      active = group $ map snd ys
      start                         = MyGraphState ([], active, Graph xs)
      MyGraphState (finished, _, _) = execGraphState graph start
    in finished

graph :: forall a . Ord a => GraphState (MyGraphState a) ()
graph = do
  MyGraphState (finished, active, g@(Graph xs)) <- getGraphState
  case active of
    [] -> pure ()
    (h@(k:a):as) ->  case Prelude.lookup k xs of
      Nothing -> do
        putGraphState (MyGraphState (h:finished, as, g))
        graph
      Just y -> do
        let
          adjacents = map snd y
          active' = [v:a | v <- adjacents, notElem v h]
          finished' = if null active' then h:finished else finished
        putGraphState (MyGraphState (finished', as ++ active', g))
        graph
--------------------------------------------------------------------------------
data MyExceptT e m a = MyExceptT { runMyExceptT :: m (Either e a) }

instance Functor m => Functor (MyExceptT e m) where
  fmap :: (a -> b) -> MyExceptT e m a -> MyExceptT e m b
  fmap f (MyExceptT x) = MyExceptT (fmap (fmap f) x)
  
instance Applicative m => Applicative (MyExceptT e m) where
  pure :: a -> MyExceptT e m a
  pure x = MyExceptT (pure (Right x))
  
  (<*>) :: MyExceptT e m (a -> b) -> MyExceptT e m a -> MyExceptT e m b
  (<*>) (MyExceptT mf) (MyExceptT mx) = MyExceptT ((<*>) <$> mf <*> mx)

instance Monad m => Monad (MyExceptT e m) where
  (>>=) :: MyExceptT e m a -> (a -> MyExceptT e m b) -> MyExceptT e m b
  (>>=) mx f = do
    argument <- mx
    f argument
--------------------------------------------------------------------------------
data Color = White | Black deriving (Eq, Show)

switch :: Color -> Color
switch White = Black
switch Black = White

data Piece = Pawn   Color
           | Knight Color
           | Bishop Color
           | Rook   Color
           | Queen  Color
           | King   Color
           deriving (Eq)

instance Show Piece where
  show :: Piece -> String
  show p = case p of
    Pawn   White -> "\x2659 \x1b[0m"
    Knight White -> "\x2658 \x1b[0m"
    Bishop White -> "\x2657 \x1b[0m"
    Rook   White -> "\x2656 \x1b[0m"
    Queen  White -> "\x2655 \x1b[0m"
    King   White -> "\x2654 \x1b[0m"
    Pawn   Black -> "\x265F \x1b[0m"
    Knight Black -> "\x265E \x1b[0m"
    Bishop Black -> "\x265D \x1b[0m"
    Rook   Black -> "\x265C \x1b[0m"
    Queen  Black -> "\x265B \x1b[0m"
    King   Black -> "\x265A \x1b[0m"

color :: Piece -> Color
color (Pawn   c) = c
color (Knight c) = c
color (Bishop c) = c
color (Rook   c) = c
color (Queen  c) = c
color (King   c) = c

points :: Piece -> Int
points (Pawn   _) = 1
points (Knight _) = 3
points (Bishop _) = 3
points (Rook   _) = 5
points (Queen  _) = 9
points (King   _) = 0x7FFFFFFFFFFFFFFF

data Position = Position
    { rank :: Int
    , file :: Char
    } deriving (Eq,Ord)

coordinates :: Position -> String
coordinates (Position n c) =
  let c' = 1 + ord c - ord 'a'
  in case mod (n + c') 2 of
    0 -> "\x1b[40m  \x1b[0m"
    1 -> "\x1b[47m  \x1b[0m"

coordinates' :: Position -> Piece -> String
coordinates' (Position n c) p =
  let c' = 1 + ord c - ord 'a'
  in case mod (n + c') 2 of
    0 -> "\x1b[40m" ++ show p
    1 -> "\x1b[47m" ++ show p

instance Show Position where
  show :: Position -> String
  show (Position n c) = c:show n

data Move = Move
    { from :: Position
    , to   :: Position
    } deriving (Eq)

data LineOfAction = Horizontal Int
                  | Vertical Int
                  | Diagonal Int
                  | KnightLeap Int Int
                  | KingSideCastling
                  | QueenSideCastling
                  | NoLine
                  deriving (Eq)

moveType :: Position -> Position -> LineOfAction
moveType (Position r1 f1) (Position r2 f2)
  | r1 == 0 && r2 == 0 && f2 == 'g' = KingSideCastling
  | r1 == 0 && r2 == 0 && f2 == 'c' = QueenSideCastling
  | r1 == r2 = Vertical   dF
  | f1 == f2 = Horizontal dR
  | dR == dF = Diagonal   dR
  | dR == 2 && dF == 1 || dR == 1 && dF == 2 = KnightLeap dR dF
  | otherwise = NoLine
  where
    dR = abs $ r2 - r1
    dF = abs $ fromEnum f2 - fromEnum f1

newtype Board = MkBoard (Map Position Piece)

instance Show Board where
  show :: Board -> String
  show (MkBoard dict) =
    let
      tablero :: [[Position]]
      tablero = [[Position n c | c <- "abcdefgh"] | n <- [8, 7..1]]
      piece :: Map Position Piece -> [Position] -> [String]
      piece dict positions = case positions of
        []     -> []
        (p:ps) -> case Map.lookup p dict of
          Nothing -> (coordinates p):piece dict ps
          Just m  -> (coordinates' p m):piece dict ps
    in unlines $ Prelude.map (concat . (piece dict)) tablero


data BoardState' a = BoardState'
    { board       :: Board
    , turn        :: Color
    , customState :: a
    }

data Custom a = Custom
    { whitePoints :: Int
    , blackPoints :: Int
    , gameStatus  :: a
    , whiteKing   :: Position
    , blackKing   :: Position
    , wKingMoved  :: Bool
    , bKingMoved  :: Bool
    , wRookAMoved :: Bool
    , wRookHMoved :: Bool
    , bRookAMoved :: Bool
    , bRookHMoved :: Bool
    } deriving (Show, Eq)

data GameStatus = InProgress
                | Drawn
                | WhiteChecks
                | BlackChecks
                | CheckMate
                | WhiteResigned
                | BlackResigned
                deriving (Eq, Show)

type AdditionalState = Custom GameStatus

type BoardState = BoardState' AdditionalState

data BoardError
    = InvalidMove { reasonIM :: String }
    deriving (Show)

whitemen :: [(Position, Piece)]
whitemen = pawns ++ men
 where
    pawns = [(Position 2 c, Pawn White) | c <- "abcdefgh"]
    men   = [(Position 1 'a', Rook   White), (Position 1 'b', Knight White),
             (Position 1 'c', Bishop White), (Position 1 'd', Queen  White),
             (Position 1 'e', King   White), (Position 1 'f', Bishop White),
             (Position 1 'g', Knight White), (Position 1 'h', Rook   White)]

blackmen :: [(Position, Piece)]
blackmen = pawns ++ men
  where
    pawns = [(Position 7 c, Pawn Black) | c <- "abcdefgh"]
    men   = [(Position 8 'a', Rook   Black), (Position 8 'b', Knight Black),
             (Position 8 'c', Bishop Black), (Position 8 'd', Queen  Black),
             (Position 8 'e', King   Black), (Position 8 'f', Bishop Black),
             (Position 8 'g', Knight Black), (Position 8 'h', Rook   Black)]

initialBoard :: Board
initialBoard = MkBoard $ Map.fromList (whitemen ++ blackmen)

initialState :: BoardState
initialState = BoardState'
  { board       = initialBoard
  , turn        = White
  , customState = Custom
      { whitePoints = 0
      , blackPoints = 0
      , gameStatus  = InProgress
      , whiteKing   = Position 1 'e'
      , blackKing   = Position 8 'e'
      , wKingMoved  = False -- ¿Se movió el rey blanco?
      , bKingMoved  = False -- ¿Se movió el rey negro?
      , wRookAMoved = False -- ¿Se movió la torre blanca de 'a1'?
      , wRookHMoved = False -- ¿Se movió la torre blanca de 'h1'?
      , bRookAMoved = False -- ¿Se movió la torre negra de 'a8'?
      , bRookHMoved = False -- ¿Se movió la torre negra de 'h8'?
      }
  }

toString :: Board -> String
toString = show

-- ErrorMessages
emptySquare from = "There's no piece on " ++ show from
kingWrongMove    = "King can only move one space"
pathError        = "Is there an obstacle or you tried to move to a square with \
                   \a colleague"
pawnWrongMove    = "A pawn can only move one square forward, or two squares on \
                   \its first move"
pawnWrongCapture = "No piece to capture"
wrongMove        = "That piece can not move like that"
wrongTurn c      = show c ++ "men can not play at this turn"
autoCheckError   = "You left your king in check"
castlingError    = "Illegal castling"

-- Auxiliar Functions
inter :: Int -> Int -> Char -> Char -> LineOfAction -> [Position]
inter r1 r2 f1 f2 v = 
  let
    subList           = drop 1 . init
    crecentIntList    = [r1 + 1..r2 - 1]
    decrecentIntList  = [r1 - 1, r1 - 2..r2 + 1]
    crecentCharList   = subList [f1..f2]
    decrecentCharList = reverse $ subList [f2..f1]
    rankRange = if r1 < r2 then crecentIntList else decrecentIntList
    fileRange = if f1 < f2 then crecentCharList else decrecentCharList
  in case v of
    Vertical _   -> [Position r f1 | r <- rankRange]
    Horizontal _ -> [Position r1 f | f <- fileRange]
    Diagonal   _ -> map (\(x, y) -> Position x y) $ zip rankRange fileRange

isEmpty :: Map Position Piece -> Position -> Bool
isEmpty m p = case Map.lookup p m of
  Nothing -> True
  Just _ -> False

isThereAMan :: Map Position Piece -> Color -> Position -> Bool
isThereAMan m c p = case Map.lookup p m of
  Nothing -> False
  Just p' -> c /= color p'

isPathClear :: Map Position Piece -> Move -> LineOfAction -> Bool
isPathClear m (Move (Position r1 f1) (Position r2 f2)) v =
  all (isEmpty m) $ inter r1 r2 f1 f2 v

pawnMoveConditions :: Color -> Int -> Int -> Int -> Bool
pawnMoveConditions t n r1 r2
  | t == White = r2 > r1 && (n == 1  || n == 2 && r1 == 2)
  | t == Black = r1 > r2 && (n == 1  || n == 2 && r1 == 7)

pawnNormalCapture :: Map Position Piece -> Color -> Position -> Int -> Int ->
  Int -> Bool
pawnNormalCapture m t to r1 r2 n
  | t == White = r2 > r1 && n == 1 && isThereAMan m t to
  | t == Black = r2 < r1 && n == 1 && isThereAMan m t to

calculatePoints :: Map Position Piece -> Position -> Color -> Int -> Int ->
  (Int, Int)
calculatePoints m to t w bl = case Map.lookup to m of
  Nothing -> (w, bl)
  Just p  ->
    let k = points p
    in if color p == White && t == Black then
      (w - k, bl + k)
    else if color p == Black && t == White then
      (w + k, bl - k)
    else
      (w, bl)

char :: Char -> Int -> Char
char c n = toEnum (fromEnum c + n)

checkKnights :: Map Position Piece -> Color -> Position -> Bool
checkKnights m t (Position r f) =
  let
    p = [(2, 1), (2, -1), (-2, 1), (-2, -1), (1, 2), (1, -2), (-1, 2), (-1, -2)]
    positions = [Position (r + x) (char f y) | (x, y) <- p]
    enemyKnight pos = case Map.lookup pos m of
      Nothing -> False
      Just (Knight c) -> c /= t
  in any enemyKnight positions

projection :: Map Position Piece -> [Position] -> Maybe Piece
projection _ [] = Nothing
projection m (p:ps) = case Map.lookup p m of
  Nothing -> projection m ps
  Just p' -> Just p'

checkLinePieces :: Map Position Piece -> Color -> Position -> Bool
checkLinePieces m t (Position r f) =
  let
    upper = [Position (r + k) f | k <- [1..8 - r]]
    lower = [Position (r - k) f | k <- [1..r - 1]]
    right = [Position r k | k <- [succ f..'h']]
    left  = [Position r k | k <- [pred f, pred (pred f)..'a']]

    paths = [upper, lower, right, left]

    isEnemy :: Maybe Piece -> Bool
    isEnemy (Just (Queen c)) = t /= c
    isEnemy (Just (Rook  c)) = t /= c
    isEnemy _              = False
  in any (\x -> isEnemy (projection m x)) paths

checkDiagonals :: Map Position Piece -> Color -> Position -> Bool
checkDiagonals m t (Position r f) =
  let
    toPos (x, y) = Position x y
    rankForward  = [r + 1..8]
    rankBackward = [r - 1, r - 2..1]
    fileForward  = [succ f..'h']
    fileBackward = [pred f, pred (pred f)..'a']
    mainForward  = map toPos $ zip rankForward  fileForward
    mainBackward = map toPos $ zip rankBackward fileBackward
    antiForward  = map toPos $ zip rankBackward fileForward
    antiBackward = map toPos $ zip rankForward  fileBackward

    paths = [mainForward, mainBackward, antiForward, antiBackward]

    isLongRangeEnemy :: Maybe Piece -> Bool
    isLongRangeEnemy (Just (Queen  c)) = t /= c
    isLongRangeEnemy (Just (Bishop c)) = t /= c
    isLongRangeEnemy _                 = False

    checkLongRange = any (\x -> isLongRangeEnemy (projection m x)) paths

    isEnemyPawn pos = case Map.lookup pos m of
      Just (Pawn c) -> t /= c
      _             -> False

    pawnThread = if t == White then
      map headMay [mainForward, antiBackward]
    else
      map headMay [mainBackward, antiForward]

    checkPawns = any isEnemyPawn [pos | Just pos <- pawnThread]
  in checkLongRange || checkPawns

isCheck :: Map Position Piece -> Color -> Position -> Bool
isCheck m t p = check where
  check = checkKnights m t p || checkLinePieces m t p || checkDiagonals m t p

kingLegalMoves :: Map Position Piece -> Color -> Position -> [Position]
kingLegalMoves m t kingPos@(Position r f) =
  let
    offsets = [ (1, 0), (-1, 0), (0, 1), (0, -1)
              , (1, 1), (1, -1), (-1, 1), (-1, -1)
              ]
    potentialPositions = [Position (r + dr) (char f df) | (dr, df) <- offsets]

    isAccessible pos = case Map.lookup pos m of
      Nothing -> True
      Just p  -> color p /= t

    isSafe pos = not $ isCheck m' t pos where
      m' = Map.insert pos (King t) $ Map.delete kingPos m
  in filter (\p -> isAccessible p && isSafe p) potentialPositions

isMate :: Map Position Piece -> Color -> Position -> Bool
isMate m t kingPos =
  let
    myPieces = Map.toList $ Map.filter (\p -> color p == t) m

    allPositions = [Position r f | r <- [1..8], f <- ['a'..'h']]

    allPotentialMoves = 
      [ (from, to) 
      | (from, piece) <- myPieces
      , to <- allPositions
      , isValidPhysicalMove m from to piece 
      ]

    canSave (from, to) =
      let
        piece = m Map.! from
        m' = Map.insert to piece $ Map.delete from m
        actualKingPos = if isKing piece then to else kingPos
      in not (isCheck m' t actualKingPos)

    isKing (King _) = True
    isKing _        = False
  in null (kingLegalMoves m t kingPos) && not (any canSave allPotentialMoves)

isValidPhysicalMove :: Map Position Piece -> Position -> Position -> Piece ->
  Bool
isValidPhysicalMove m from@(Position r1 f1) to@(Position r2 f2) p =
  let 
    mv = Move from to
    destiny = isEmpty m to || isThereAMan m (color p) to
    destinyPawn v = isEmpty m to && isPathClear m mv v
    longRangeMove v = isPathClear m mv v && destiny
    c = color p
  in case moveType from to of
    h@(Horizontal n) -> case p of
      King _  -> n == 1 && destiny
      Queen _ -> longRangeMove h
      Rook _  -> longRangeMove h
      _       -> False
    v@(Vertical n) -> case p of
      King _  -> n == 1 && destiny
      Pawn _  -> pawnMoveConditions c n r1 r2 && destinyPawn v
      Queen _ -> longRangeMove v
      Rook _  -> longRangeMove v
      _       -> False
    d@(Diagonal n) -> case p of
      King _   -> n == 1 && destiny
      Pawn _   -> pawnNormalCapture m c to r1 r2 n
      Queen _  -> longRangeMove d
      Bishop _ -> longRangeMove d
      _        -> False
    KnightLeap h v -> case p of
      Knight _ -> destiny
      _        -> False
    _ -> False

validateCastling :: Map Position Piece -> Color -> LineOfAction ->
  Custom GameStatus -> Bool
validateCastling m c castlingType custom =
  let
    row = if c == White then 1 else 8
    
    kingHasMoved = if c == White then wKingMoved custom else bKingMoved custom
    rookHasMoved = case castlingType of
      KingSideCastling  ->
        if c == White then wRookHMoved custom else bRookHMoved custom
      QueenSideCastling ->
        if c == White then wRookAMoved custom else bRookAMoved custom
      _                 -> True
      
    piecesUnmoved = not kingHasMoved && not rookHasMoved

    emptyFiles = case castlingType of
      KingSideCastling  -> "fg"
      QueenSideCastling -> "dcb"
      _                 -> []
    pathIsEmpty = all (\f -> Map.lookup (Position row f) m == Nothing) emptyFiles

    transitionFiles = case castlingType of
      KingSideCastling  -> "ef"
      QueenSideCastling -> "ed"
      _                 -> []
    noCheckInTransition = all (\f -> not (isCheck m c (Position row f))) transitionFiles

  in piecesUnmoved && pathIsEmpty && noCheckInTransition

executeCastling :: Map Position Piece -> Color -> LineOfAction -> Int -> Int ->
  Position -> Position -> Custom GameStatus -> BoardState' (Custom GameStatus)
executeCastling m c castlingType w bl wk bk custom =
  let
    row = if c == White then 1 else 8
    t'  = switch c
    
    -- Definimos los orígenes y destinos exactos del Rey y la Torre
    (kFrom, kTo, rFrom, rTo) = case castlingType of
      KingSideCastling  ->
        (Position row 'e', Position row 'g', Position row 'h', Position row 'f')
      QueenSideCastling ->
        (Position row 'e', Position row 'c', Position row 'a', Position row 'd')
      _                 ->
        (Position row 'e', Position row 'e', Position row 'a', Position row 'a')
                               
    m' = Map.insert kTo (King c) 
       $ Map.insert rTo (Rook c)
       $ Map.delete kFrom 
       $ Map.delete rFrom m
       
    wk' = if c == White then kTo else wk
    bk' = if c == Black then kTo else bk
    
    enemyKing  = if c == White then bk' else wk'
    enemyCheck = isCheck m' t' enemyKing
    s' | enemyCheck =
          if isMate m' t' enemyKing then CheckMate
          else (if c == White then WhiteChecks else BlackChecks)
       | otherwise  = InProgress

    wkm' = wKingMoved custom  || c == White
    bkm' = bKingMoved custom  || c == Black
    wra' = wRookAMoved custom || c == White && castlingType == QueenSideCastling
    wrh' = wRookHMoved custom || c == White && castlingType == KingSideCastling
    bra' = bRookAMoved custom || c == Black && castlingType == QueenSideCastling
    brh' = bRookHMoved custom || c == Black && castlingType == KingSideCastling
    
    newCustom = Custom w bl s' wk' bk' wkm' bkm' wra' wrh' bra' brh'
  in
    BoardState' (MkBoard m') t' newCustom

move :: Move -> StateT BoardState (ExceptT BoardError IO) ()
move mv@(Move from@(Position r1 f1) to@(Position r2 f2)) = do
  BoardState' (MkBoard m) t
    custom@(Custom w bl s wk bk wkm bkm wra wrh bra brh) <- get

  let kingPosition = if t == White then wk else bk

  case Map.lookup from m of
    Nothing -> throwError $ InvalidMove $ emptySquare from
    Just p  ->
      if t /= color p then
        throwError $ InvalidMove $ wrongTurn $ color p
      else do
        let
          m'    = Map.insert to p $ Map.delete from m
          t'    = switch t
          wk'   = if p == King White then to else wk
          bk'   = if p == King Black then to else bk
          wkm' = wkm || (p == King White)
          bkm' = bkm || (p == King Black)
          wra' = wra || (p == Rook White && from == Position 1 'a')
          wrh' = wrh || (p == Rook White && from == Position 1 'h')
          bra' = bra || (p == Rook Black && from == Position 8 'a')
          brh' = brh || (p == Rook Black && from == Position 8 'h')
          king  = if t == White then wk' else bk'
          enemy = if t == White then bk' else wk'
          autoCheck = isCheck m' t king
          enemyCheck = isCheck m' t' enemy
          materialDraw = case Map.size m of
            2 -> True
            3 -> eitherKnightOrBishop where
                filtered = Map.filter (\x -> isKnight x || isBishop x) m
                eitherKnightOrBishop = not $ null filtered
                isKnight x = x == Knight White || x == Knight Black
                isBishop x = x == Bishop White || x == Bishop Black
            _ -> False
          s' | enemyCheck   = if isMate m' t' enemy
                              then CheckMate
                              else if t == White
                                then WhiteChecks
                                else BlackChecks
             | materialDraw = Drawn
             | otherwise    = InProgress
          (w', bl') = calculatePoints m to t w bl
          newState p wkm bkm wra wrh bra brh = BoardState' (MkBoard m') t'
            (Custom w' bl' s' wk' bk' wkm bkm wra wrh bra brh)
          new p wkm bkm wra wrh bra brh =
            put $ newState p wkm bkm wra wrh bra brh
          destiny = isEmpty m to || isThereAMan m t to
          destinyPawn v = isEmpty m to && isPathClear m mv v
          longRangeMove v = isPathClear m mv v && destiny
        if autoCheck then do
          throwError $ InvalidMove autoCheckError
        else
          case moveType from to of
            KingSideCastling -> do
              if validateCastling m t KingSideCastling custom then do
                put $ executeCastling m t KingSideCastling w bl wk bk custom
              else throwError $ InvalidMove castlingError
            QueenSideCastling -> do
              if validateCastling m t QueenSideCastling custom then do
                put $ executeCastling m t QueenSideCastling w bl wk bk custom
              else throwError $ InvalidMove castlingError
            h@(Horizontal n)   -> case p of
              King  _ ->
                if n == 1 && destiny then new p wkm' bkm' wra' wrh' bra' brh'
                else throwError $ InvalidMove kingWrongMove
              Queen _ ->
                if longRangeMove h then new p wkm' bkm' wra' wrh' bra' brh'
                else throwError $ InvalidMove pathError
              Rook  _ ->
                if longRangeMove h then new p wkm' bkm' wra' wrh' bra' brh'
                else throwError $ InvalidMove pathError
              _       -> throwError $ InvalidMove wrongMove
            v@(Vertical   n)   -> case p of
              King  _ ->
                if n == 1 && destiny then new p wkm' bkm' wra' wrh' bra' brh'
                else throwError $ InvalidMove kingWrongMove
              Pawn  _ ->
                if pawnMoveConditions t n r1 r2 && destinyPawn v then
                  new p wkm' bkm' wra' wrh' bra' brh'
                else throwError $ InvalidMove pawnWrongMove
              Queen _ ->
                if longRangeMove v then new p wkm' bkm' wra' wrh' bra' brh'
                else throwError $ InvalidMove pathError
              Rook  _ ->
                if longRangeMove v then new p wkm' bkm' wra' wrh' bra' brh'
                else throwError $ InvalidMove pathError
              _       -> throwError $ InvalidMove wrongMove
            d@(Diagonal   n)   -> case p of
              King   _ ->
                if n == 1 && destiny then new p wkm' bkm' wra' wrh' bra' brh'
                else throwError $ InvalidMove kingWrongMove
              Pawn   _ ->
                if pawnNormalCapture m t to r1 r2 n {- || enPassant ? -} then
                  new p wkm' bkm' wra' wrh' bra' brh'
                else throwError $ InvalidMove pawnWrongCapture
              Queen  _ ->
                if longRangeMove d then new p wkm' bkm' wra' wrh' bra' brh'
                else throwError $ InvalidMove pathError
              Bishop _ ->
                if longRangeMove d then new p wkm' bkm' wra' wrh' bra' brh'
                else throwError $ InvalidMove pathError
              _        -> throwError $ InvalidMove wrongMove
            KnightLeap h v -> case p of
              Knight _ ->
                if destiny then new p wkm' bkm' wra' wrh' bra' brh'
                else throwError $ InvalidMove pathError
              _        -> throwError $ InvalidMove wrongMove
            NoLine         -> throwError $ InvalidMove wrongMove

parseMove :: String -> Either BoardError Move
parseMove s = case s of
  w:x:y:z:[] ->
    let
      actualMove = x /= z || w /= y
      constraint = fileConstraints w y && rankConstraints x z && actualMove
      x'         = digitToInt x
      z'         = digitToInt z
      m          = Move (Position x' w) (Position z' y)
    in if constraint then Right m else Left e
  "o-o"      -> Right $ Move (Position 0 'e') (Position 0 'g')
  "o-o-o"    -> Right $ Move (Position 0 'e') (Position 0 'c')
  _          -> Left $ InvalidMove "Impossible Move"
  where
    e                     = InvalidMove "Out Of Bounds"
    fileConstraints f1 f2 = elem f1 "abcdefgh" && elem f2 "abcdefgh"
    rankConstraints r1 r2 = elem r1 "12345678" && elem r2 "12345678"

playGame :: StateT BoardState (ExceptT BoardError IO) ()
playGame = do
  liftIO $ putStr "What would you like to play? "
  liftIO $ hFlush stdout
  movement <- liftIO getLine
  case parseMove movement of
    Left err -> do
      liftIO $ putStrLn $ "Syntax error: " ++ show err
      playGame
    Right validMove -> do
      move validMove
      currentState <- get
      liftIO $ putStr $ show (board currentState)
      playGame

playChess :: IO ()
playChess = runExceptT (runStateT playGame initialState) >>= \case
    Left err -> putStrLn $ "Game ended with error: " ++ show err
    Right _ -> putStrLn "Game ended successfully"
--------------------------------------------------------------------------------
main :: IO ()
main = do
  pure ()
