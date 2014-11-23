-- RegEx-DFA: zapoctovy program k Neproceduralnimu programovani, LS 2012
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe (fromJust, fromMaybe)
import Control.Monad

{------------------------------------------------------------------------------
  RegEx
  datovy typ pro regularni vyrazy
------------------------------------------------------------------------------}
data RegEx alph = Nop                           |  -- prazdny jazyk
                  Lambda                        |  -- prazdne slovo
                  Lit alph                      |  -- literal abecedy
                  Or (RegEx alph) (RegEx alph)  |  -- sjednoceni hodnot vyrazu
                  And (RegEx alph) (RegEx alph) |  -- konkatanace vyrazu
                  Itr (RegEx alph)                 -- obecna iterace vyrazu
                  deriving Eq

-- stringova representace vyrazu
regex2str :: Show alph => RegEx alph -> String
regex2str Nop = ""
regex2str Lambda = "_"
regex2str (Lit c) = filter (/='\'') $ show c       -- zrus uvozovky kolem
regex2str (r1 `Or` r2) = "(" ++ regex2str r1 ++ "+" ++ regex2str r2 ++ ")"
regex2str (r1 `And` r2) = "(" ++ regex2str r1 ++ regex2str r2 ++ ")"
regex2str (Itr r) = "(" ++ regex2str r ++ ")*"

instance Show alph => Show (RegEx alph) where
  show = regex2str
  
-- parse regexu ze stringu -- vraci regex a co zbylo ze stringu
parseRegex :: String -> (RegEx Char, String)
parseRegex "" = (Nop, "Not enough operands")
parseRegex (' ':rest) = (reg, rest')
  where (reg, rest') = parseRegex rest
parseRegex ('_':rest) = (Lambda, rest)
parseRegex ('+':rest) = (reg1 `Or` reg2, rest2)
  where (reg1, rest1) = parseRegex rest
        (reg2, rest2) = parseRegex rest1
parseRegex ('.':rest) = (reg1 `And` reg2, rest2)
  where (reg1, rest1) = parseRegex rest
        (reg2, rest2) = parseRegex rest1
parseRegex ('*':rest) = (Itr reg, rest')
  where (reg, rest') = parseRegex rest
parseRegex (c:rest) = (Lit c, rest)             -- literal

-- prevod regexu ze stringu -- vraci regex, je-li chyba v zadani, tak prazdny jaz
str2regex :: String -> RegEx Char
str2regex str | snd tuple == "" && fst tuple /= Nop = fst tuple
              | otherwise                           = Nop
              where tuple = parseRegex str

{------------------------------------------------------------------------------
  DFA
  datovy typ pro (deterministicky) konecny automat
------------------------------------------------------------------------------}
data DFA st8Type alphType = DFA 
  { st8s :: Set.Set st8Type                         -- stavy
  , alph :: [alphType]                              -- vstupni abeceda
  , trans :: Map.Map (st8Type, alphType) st8Type    -- prechodova funkce
  , start :: st8Type                                -- pocatecni stav
  , ends :: Set.Set st8Type                         -- koncove stav
  } deriving (Eq, Ord, Show)

{------------------------------------------------------------------------------
  NFA
  datovy typ pro nedeterministicky konecny automat
------------------------------------------------------------------------------}
data NFA st8Type alphType = NFA
  { nSt8s :: Set.Set st8Type                                 -- stavy
  , nAlph :: [alphType]                                      -- vstupni abeceda
  , nTrans :: Map.Map (st8Type, alphType) (Set.Set st8Type)  -- prechodova fce
  , nStarts :: Set.Set st8Type                               -- pocatecni stavy
  , nEnds :: Set.Set st8Type                                 -- koncove stavy
  } deriving (Eq, Ord, Show)

{------------------------------------------------------------------------------
  Konverzni funkce
    - z NFA na DFA
    - z NFA na NFA (isomorfismus)
    - z regularniho vyrazu na NFA
------------------------------------------------------------------------------}
-- kam se mnozina stavu dostane po precteni zadaneho pismena?
getsTo :: (Ord s, Eq s, Ord a) => Set.Set s -> Map.Map (s, a) (Set.Set s) -> a
  -> Set.Set s
getsTo fromSet trans lit = Set.unions $ [nextOf q | q <- Set.elems fromSet]
  where nextOf q = fromMaybe Set.empty $ Map.lookup (q, lit) trans

-- BFS pruchod potencnim automatem - vraci skutecne dostupne stavy
-- prechod.fce NFA ->zasobnik ->mnozina navstivenych podmnozin stavu ->vysl.
bfs :: (Ord s, Eq s, Ord a) => [a] -> Map.Map (s, a) (Set.Set s) -> [Set.Set s]
  -> Set.Set (Set.Set s) -> Set.Set (Set.Set s)
bfs _ _ [] visited = visited
bfs abc trans (todoSet:todoList) visited = bfs abc trans newTodo visited'
  where newSets = [toSet | lit <- abc, let toSet = getsTo todoSet trans lit,
                   toSet `Set.notMember` visited]
        newTodo = todoList ++ newSets
        visited' = Set.fromList newSets `Set.union` visited
            
-- z NFA na DFA: podmnozinova konstrukce
nfa2dfa :: (Ord s, Eq s, Ord a) => NFA s a -> DFA (Set.Set s) a
nfa2dfa nfa = DFA
  { st8s = reachblSubs            -- mnz dosazitelny podmnozin stavu pri BFS
  , alph = alph'                  -- stejna abeceda
  , trans = parallelTrans         -- prechodova fce mnoziny jako sjednoceni 
                                  -- prechodovych funkci svych prvku
  , start = starts'               -- mnozina pocatecnich stavu v NFA
  , ends = ends' } where          -- mnoziny nedisjunktni s mnz koncovych stavu
  alph' = nAlph nfa
  starts' = nStarts nfa
  trans' = nTrans nfa
  reachblSubs =  bfs alph' trans' [starts'] $ Set.singleton starts'
  parallelTrans = Map.fromList 
    [((fromSet, lit), toSet) | fromSet <- Set.elems reachblSubs, lit <- alph',
     let toSet = getsTo fromSet trans' lit]
     -- toSet = sjednoc. koncu sipek prechod. fce kazdeho prvku podmnoz. stavu
  ends' = Set.fromList [subset | subset <- Set.elems reachblSubs,
                        not $ Set.null $ nEnds nfa `Set.intersection` subset]

-- kartezsky soucin 2 mnozin
cartesian :: (Ord a, Ord b) => Set.Set a -> Set.Set b -> Set.Set (a, b)
cartesian set1 set2 = Set.fromList
                        [(x, y) | x <- Set.elems set1, y <- Set.elems set2]
                        
-- z NFA na NFA: isomorfimus ze stavu na rozsah cisel (zacinajiciho od zadane
-- dolni meze)
isomorph :: (Ord s, Eq s, Ord a) => NFA s a -> Int -> NFA Int a
isomorph oldNfa floor = NFA
  { nSt8s = numSt8s                           -- nove ciselne stavy
  , nAlph = nAlph'
  , nTrans = numTrans
  , nStarts = numStarts
  , nEnds = numEnds} where
  oldSt8s = Set.elems $ nSt8s oldNfa
  range = [floor..floor + length oldSt8s - 1]
  indices = Map.fromList $ zip oldSt8s range  -- zafixovani bijekce
  getIndex q = fromJust $ Map.lookup q indices
  numSt8s = Set.fromList range
  nAlph' = nAlph oldNfa
  numTrans = Map.fromList [((n, lit), set) | p <- oldSt8s, lit <- nAlph',
                           let n = getIndex p
                               toSet = Map.lookup (p, lit) $ nTrans oldNfa
                               set | toSet == Nothing = Set.empty
                                   | otherwise        = Set.map getIndex $
                                                        fromJust toSet]
  numStarts = Set.fromList [getIndex q | q <- Set.elems $ nStarts oldNfa]
  numEnds = Set.fromList [getIndex q | q <- Set.elems $ nEnds oldNfa]


-- z regularniho vyrazu na NFA: inkrementalne (indukci dle slozitosti vyrazu)
-- nutnost znalosti cele abecedy = paremtr "abc"
regex2nfa :: (Show alph, Ord alph) => RegEx alph -> [alph] -> NFA Int alph
-- prazdny jazyk -> NKA bez prijimacich stavu
regex2nfa Nop abc = NFA
  { nSt8s = Set.fromList [0]
  , nAlph = abc
  , nTrans = Map.empty
  , nStarts = Set.fromList [0]
  , nEnds = Set.empty }

-- Lambda -> NKA s odpadnim stavem & stejnym pocatecnim a prijimacim stavem
regex2nfa Lambda abc = NFA
  { nSt8s = Set.fromList [0, 1]      -- 1 = odpadni stav
  , nAlph = abc
  , nTrans = Map.fromList [((n, c), Set.fromList [1]) | n <- [0, 1], c <- abc]
  , nStarts = Set.fromList [0]
  , nEnds = Set.fromList [0]}

-- 1 literal -> NKA s odpadnim stavem a "prijimaci" hranou
regex2nfa (Lit l) abc = NFA
  { nSt8s = Set.fromList [0, 1, 2]   -- 2 = odpadni stav
  , nAlph = abc
  , nTrans = Map.fromList $ [((0, l), Set.fromList [1])] ++
               [((0, c), Set.fromList [2]) | c <- abc, c /= l] ++
               [((n, c), Set.fromList [2]) | n <- [1, 2], c <- abc]
  , nStarts = Set.fromList [0]
  , nEnds = Set.fromList [1]}

-- r1+r2 -> paralelni beh 2 dilcich NKA
regex2nfa (r1 `Or` r2) abc =
  let nfa1 = regex2nfa r1 abc
      nfa2 = regex2nfa r2 abc
      st81 = Set.elems $ nSt8s nfa1
      st82 = Set.elems $ nSt8s nfa2
      para = [(((p1, p2), l), pairs) | p1 <- st81, p2 <- st82, l <- abc,
              let set1 = fromMaybe Set.empty $ Map.lookup (p1, l) $ nTrans nfa1
                  set2 = fromMaybe Set.empty $ Map.lookup (p2, l) $ nTrans nfa2
                  pairs = set1 `cartesian` set2
             ]
  in isomorph (NFA
       { nSt8s = (nSt8s nfa1) `cartesian` (nSt8s nfa2)
       , nAlph = abc
       , nTrans = Map.fromList para
       , nStarts = (nStarts nfa1) `cartesian` (nStarts nfa2)
       , nEnds = (nEnds nfa1 `cartesian` (nSt8s nfa2))
                   `Set.union`
                 (nSt8s nfa1 `cartesian` (nEnds nfa2))}
      ) 0

-- r1.r2 -> beh v 1 automatu, lambda-prepnuti do 2. automatu
regex2nfa (r1 `And` r2) abc =
  let nfa1 = isomorph (regex2nfa r1 abc) 0
      nfa2 = isomorph (regex2nfa r2 abc) (Set.size (nSt8s nfa1))
      st81 = Set.elems $ nSt8s nfa1
      f1   = nEnds nfa1 
      nTrans' = [((q, l), set) | q <- st81, l <- abc,
                 let set | Set.null $ f1 `Set.intersection` delta1 = delta1
                         | otherwise = nStarts nfa2 `Set.union` delta1
                         where delta1 = fromMaybe Set.empty $ Map.lookup (q, l)
                                          $ nTrans nfa1]
      nStarts' | Set.null (nEnds nfa1 `Set.intersection` strts1) = strts1
               | otherwise = nStarts nfa2 `Set.union` strts1      -- Lambda v 1
               where strts1 = nStarts nfa1
  in NFA { nSt8s = nSt8s nfa1 `Set.union` nSt8s nfa2
         , nAlph = abc
         , nTrans = nTrans nfa2 `Map.union` Map.fromList nTrans'
         , nStarts = nStarts'
         , nEnds = nEnds nfa2}
         
-- r* -> jako puvodni automat + restart + dalsi novy pocatek pro Lambda
regex2nfa (Itr r) abc =         
  let nfa1 = isomorph (regex2nfa r abc) 0
      st81 = Set.elems $ nSt8s nfa1
      newStart = length st81
      s1 = nStarts nfa1 
      f1 = nEnds nfa1 
      nTrans' = [((q, l), set) | q <- st81, l <- abc,
                 let set | Set.null $ f1 `Set.intersection` delta1 = delta1
                         -- v koncovych stavech +restart
                         | otherwise = s1 `Set.union` delta1 
                         where delta1 = fromMaybe Set.empty $ Map.lookup (q, l)
                                          $ nTrans nfa1]
  in NFA { nSt8s = newStart `Set.insert` (nSt8s nfa1)
         , nAlph = abc
         , nTrans = Map.fromList nTrans'
         , nStarts = newStart `Set.insert` s1
         , nEnds = newStart `Set.insert` f1}

{------------------------------------------------------------------------------
  Simulace behu automatu
------------------------------------------------------------------------------}
-- kam se DFA dostane od zadaneho stavu po precteni celeho slova?
transWord :: (Ord s, Eq s, Ord a) => DFA s a -> s -> [a] -> Maybe s
transWord dfa fromSt8 [] = Just fromSt8
transWord dfa fromSt8 (firstLit:suffix) 
  | nextSt8 == Nothing = Nothing
  | otherwise          = transWord dfa (fromJust nextSt8) suffix
  -- nextSt8 = stav z fromSt8 po precteni znaku firstLit
  where nextSt8 = Map.lookup (fromSt8, firstLit) (trans dfa)

-- simulace automatu <- akceptuje automat slovo?
acpt :: (Ord s, Eq s, Ord a) => DFA s a -> [a] -> Bool
acpt dfa word | finalSt8 == Nothing = False
              | otherwise           = fromJust finalSt8 `Set.member` (ends dfa)
              where finalSt8 = transWord dfa (start dfa) word

{------------------------------------------------------------------------------
  hlavni program
------------------------------------------------------------------------------}
main = do  
  putStrLn "Regular expression (in prefix notation)? "  
  str <- getLine
  let regex = str2regex str
  forever $ do
    putStrLn ("Test " ++ (show regex) ++ " with? ")  
    word <- getLine
    putStrLn . show $ acpt (nfa2dfa $ regex2nfa regex ['a'..'z']) word

{------------------------------------------------------------------------------
  Debug tools
    - ruzne priklady regexu a automatu (lehcich i lehce drsnejsich :-)
------------------------------------------------------------------------------}
regex1 = Itr (Lambda `Or` (Lit 4 `And` Lit 2))
regex2 = Itr (Lambda `And` (Lit 'a' `And` Lit '2') `Or` Lit 'b')
regex3 = Lambda `Or` Lit 'a'
regex4 = Lambda `Or` Lit 'a' `Or` Lit 'b'
regexFromStr = str2regex ". * .*a.b.*ab *a"  -- ((((a)*(b((a)*b))))*(a)*)

showTrans dfa = putStrLn . Map.showTree $ trans dfa
showNtrans nfa = putStrLn . Map.showTree $ nTrans nfa
showSet a = putStrLn . Set.showTree $ a
st = Set.fromList [1..4]

-- priklad NFA
nfa1 :: NFA Int Char
nfa1 = NFA { nSt8s = Set.fromList [0..7]
           , nAlph = ['a', 'b']
           , nTrans = Map.fromList [((0, 'a'), Set.fromList [4..7]), ((0, 'b'),
               Set.fromList [1]), ((1, 'a'), Set.fromList [1..7])]
           , nStarts = Set.fromList [0]
           , nEnds = Set.fromList [7]}

-- Autogramy [doc. R. Bartak] - slide str. 14 vpravo dole
nfa2 :: NFA Int Char
nfa2 = NFA { nSt8s = Set.fromList [1..4]
           , nAlph = ['a', 'b']
           , nTrans = Map.fromList
                      [((1, 'a'), Set.fromList [1, 2]),
                       ((1, 'b'), Set.fromList [4]),
                       ((2, 'a'), Set.fromList [4]),
                       ((2, 'b'), Set.fromList [3]),
                       ((3, 'a'), Set.fromList [1]),
                       ((3, 'b'), Set.fromList [4]),
                       ((4, 'a'), Set.fromList [1, 4]),
                       ((4, 'b'), Set.fromList [4])]
           , nStarts = Set.fromList [1, 2]
           , nEnds = Set.fromList [1, 3]}

-- automat pro test BFS
nfa3 :: NFA Int Char
nfa3 = NFA { nSt8s = Set.fromList [0..4]
           , nAlph = ['a', 'b']
           , nTrans = Map.fromList
                      [((0, 'a'), Set.fromList [1, 2]),
                       ((0, 'b'), Set.fromList [2]),
                       ((1, 'a'), Set.fromList [1]),
                       ((1, 'b'), Set.fromList [1]),
                       ((2, 'a'), Set.fromList [1]),
                       ((2, 'b'), Set.fromList [1]),
                       ((3, 'a'), Set.fromList [4]),
                       ((3, 'b'), Set.fromList [4]),
                       ((4, 'a'), Set.fromList [3]),
                       ((4, 'b'), Set.fromList [4])]
           , nStarts = Set.fromList [0, 1]
           , nEnds = Set.fromList [2, 4]}

-- priklad DFA
dfa1 :: DFA Int Char
dfa1 = DFA { st8s = Set.fromList [0..10]
           , alph = ['a'..'z']
           , trans = Map.fromList [((0, 'a'), 4), ((0, 'b'), 1), ((1, 'a'), 1)]
           , start = 0
           , ends = Set.fromList [10]}

dfa2 :: DFA (Set.Set Int) Char
dfa2 = nfa2dfa nfa2

-- automaty vytvorene z regexu
dfaLambda = nfa2dfa $ regex2nfa Lambda "abcd"
dfaLit    = nfa2dfa $ regex2nfa (Lit 'c') "bcd"
nfaOr     = regex2nfa (Lambda `Or` Lit 'a') "ab"
nfaAnd    = regex2nfa (Lit 'a' `And` Lit 'b') "ab"
dfaAnd    = nfa2dfa nfaAnd
dfaAndOr  = nfa2dfa $ regex2nfa ((Lit 'a' `And` Lit 'b') `Or` Lit 'a') "ab"
dfaAndItr = nfa2dfa $ regex2nfa (Lit 'a' `And` Itr(Lit 'b') `And` Lit 'a') "ab"
-- regex pro {0,1}-posl. se sudym #1cek
hardRegex = Itr(Itr(Lit 0) `And` (Lit 1) `And` Itr(Lit 0) `And` (Lit 1))
            `And` (Itr(Lit 0))
dfaHard   = nfa2dfa $ regex2nfa hardRegex [0, 1]

-- dtto s retezci 'a', 'b' a sudym #'b'
dfaStr    = nfa2dfa $ regex2nfa regexFromStr "ab"

-- priklad pro simulaci automatu
transWord' = transWord dfa2 (Set.fromList [1, 2]) "ababbbbbaab"
acpt' = acpt dfa2 "abbabbaaa"
acptHard = acpt dfaHard [1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1] -- True
acptStr = acpt dfaStr "aababbabaabaabbbb"                          -- False
