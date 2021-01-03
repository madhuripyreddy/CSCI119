-- Lab 9: Derivative-based conversion from RE' to FSM' (Brzozowski Construction)
import Data.List
import Data.Array
import Control.Monad (replicateM)  -- for strings function below


-- Given alphabet. But your code should work with any finite list of characters.
sigma = ['a', 'b']

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

---- Regular expressions, along with output and input
data RegExp = Empty
             | Let Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp
             deriving (Show, Eq)

-- Compact display form for RegExp
newtype Compact = Compact RegExp

instance (Show Compact) where    -- use precedence to minimize parentheses
  showsPrec d (Compact r) = sp d r where
    sp d Empty         = showString "@"
    sp d (Let c)       = showString [c]
    sp d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                         sp 6 r1 .
                         showString "+" .
                         sp 6 r2
    sp d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                         sp 7 r1 .
                         sp 7 r2
    sp d (Star r1)     = sp 9 r1 .     -- prec(Star) = 8
                         showString "*"

-- Extended regular expressions, including a name for One = Star Empty,
-- and arbitrary numbers of arguments for (associative) Union and Cat
data RegExp' = Zero | One | Let' Char |
               Union' [RegExp'] | Cat' [RegExp'] | Star' RegExp'
  deriving (Eq, Ord, Show)

-- Convert ordinary RegExps into extended REs
fromRE :: RegExp -> RegExp'
fromRE Empty = Zero
fromRE (Let c) = Let' c
fromRE (Union r1 r2) = Union' [fromRE r1, fromRE r2]
fromRE (Cat r1 r2) = Cat' [fromRE r1, fromRE r2]
fromRE (Star r1) = Star' (fromRE r1)

-- Convert extended REs into ordinary REs, eliminating Union' and Cat' on
-- lists of length < 2, and right-associating them on longer lists
fromRE' :: RegExp' -> RegExp
fromRE' Zero = Empty
fromRE' One = Star Empty
fromRE' (Let' c) = Let c
fromRE' (Union' []) = Empty
fromRE' (Union' [r]) = fromRE' r
fromRE' (Union' (r:rs)) = Union (fromRE' r) (fromRE' (Union' rs))
fromRE' (Cat' []) = Star Empty
fromRE' (Cat' [r]) = fromRE' r
fromRE' (Cat' (r:rs)) = Cat (fromRE' r) (fromRE' (Cat' rs))
fromRE' (Star' r) = Star (fromRE' r)

-- Basic postfix parser for RegExp', assuming binary + and ., for testing
toRE' :: String -> RegExp'
toRE' w = go w [] where
  go [] [r] = r
  go ('0':xs) rs = go xs (Zero:rs)
  go ('1':xs) rs = go xs (One:rs)
  go ('+':xs) (r2:r1:rs) = go xs (Union' [r1,r2]:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat' [r1,r2]:rs)
  go ('*':xs) (r:rs) = go xs (Star' r:rs)
  go (x:xs) rs = go xs (Let' x:rs)

-- An extended regular expression simplifier
simp :: RegExp' -> RegExp'
simp Zero = Zero
simp One = One
simp (Let' c) = Let' c
simp (Union' rs) = union' $ flat_uni $ map simp rs
simp (Cat' rs) = union' $ flat_cat $ map simp rs
simp (Star' r) = star' $ simp r

-- Smart constructor for Union' that normalizes its arguments and
-- handles the empty and singleton cases
union' :: [RegExp'] -> RegExp'
union' rs =  case norm rs of
  []  ->  Zero
  [r] -> r
  rs  -> Union' rs

-- Smart constructor for Cat' that handles the empty and singleton cases
cat' :: [RegExp'] -> RegExp'
cat' [] = One
cat' [r] = r
cat' rs = Cat' rs

-- Smart constructor for Star' that handles the constant and Star' cases
star' :: RegExp' -> RegExp'
star' Zero = One
star' One = One
star' (Star' r) = star' r
star' r = Star' r

-- Flatten a list of arguments to Union'; assumes each argument is simplified
flat_uni :: [RegExp'] -> [RegExp']
flat_uni [] = []
flat_uni (Zero:rs) = flat_uni rs
flat_uni (Union' rs':rs) = rs' ++ flat_uni rs
flat_uni (r:rs) = r : flat_uni rs

-- Flatten a list of arguments to Cat', turning them into a list of arguments
-- to Union'; assumes each argument is simplified
flat_cat :: [RegExp'] -> [RegExp']
flat_cat rs = fc [] rs where
  -- fc (args already processed, in reverse order) (args still to be processed)
  fc :: [RegExp'] -> [RegExp'] -> [RegExp']
  fc pr [] = [cat' $ reverse pr]
  fc pr (Zero:rs) = []
  fc pr (One:rs) = fc pr rs
  fc pr (Cat' rs':rs) = fc (reverse rs' ++ pr) rs
  fc pr (Union' rs':rs) = concat $ map (fc pr . (:rs)) rs'
  fc pr (r:rs) = fc (r:pr) rs

-- Finite state machines (as records), indexed by the type of their states
type FSM a = ([a], a, [a], a -> Char -> a)

-- Check whether a finite state machine (qs, s, fs, ts) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (s is in qs)
-- (3) Final states are states (fs is a subset of qs)
-- (4) Transition function gives a state in qs for every state in qs and
--     letter from sigma


-- Cartesian product (preserves normalization)
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Powerset  (preserves normalization)
power :: [a] -> [[a]]
power [] = [[]]
power (x:xs) = let ys = power xs
               in [] : map (x:) ys ++ tail ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

-- delta* construction
star :: (a -> Char -> a) -> (a -> [Char] -> a)
star = foldl'

-- Unary set closure (where "set" = normalized list)
-- uclosure xs g == smallest set containing xs and closed under g
uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, s, fs, d) = (qs', s, fs', d) where
  qs' = uclosure [s] (\q -> map (d q) sigma)
  fs' = filter (`elem` fs) qs'

-- Change the states of an FSM from an equality type to Int 
-- and use an array lookup for the transition function
intify :: Eq a => FSM a -> FSM Int
intify (qs, s, fs, d) = ([0..n-1], s', fs', d') where
  n = length qs
  m = length sigma
  s'  = ind qs s
  fs' = map (ind qs) fs
  arr = listArray ((0,0), (n-1,m-1)) [ind qs (d q a) | q <- qs, a <- sigma]
  d' q a = arr ! (q, ind sigma a)
  ind (q':qs) q = if q == q' then 0 else 1 + ind qs q

reduce :: Ord a => FSM a -> FSM Int
reduce = intify . reachable

-- nodups xs = "xs has no duplicates"
nodups :: Eq a => [a] -> Bool
nodups [] = True           
nodups (x:xs) = notElem x xs && nodups xs

-- subset xs ys == "xs is a subset of ys"
subset :: Eq a => [a] -> [a] -> Bool
subset [] ys = True
subset (x:xs) ys = elem x ys && subset xs ys
-- OR: subset xs ys = all (`elem` ys) xs

-- func d qs == "d is a function from qs x sigma to qs"
func :: Eq a => (a -> Char -> a) -> [a] -> Bool
func d qs = and [elem (d q a) qs | q <- qs, a <- sigma]

-- check whether a finite state machine is correct/complete:
checkFSM :: Eq a => FSM a -> Bool
checkFSM (qs, s, fs, d) = nodups qs &&         -- (1)
                          elem s qs &&         -- (2)
                          subset fs qs &&      -- (3)
                          func d qs            -- (4)

-- All functions below assume that the machine is correct
delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star (_, _, _, d) = foldl d

accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m@(_, s, fs, _) w = elem (delta_star m s w) fs

accept2_aux :: Eq a => FSM a -> a -> [Char] -> Bool
accept2_aux m@(_, _, fs, _) q [] = elem q fs
accept2_aux m@(_, _, _, d) q (a:w) = accept2_aux m (d q a) w

accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 m@(_, s, _, _) w = accept2_aux m s w

-- odd_bs is a machine that accepts strings with an odd number of b's
-- states: (number of b's read so far) mod 2
odd_bs :: FSM Int
odd_bs = ([0,1], 0, [1], f) where
  f q a = if a == 'b' then (q+1) `mod` 2 else q

-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately
avoid_aab :: FSM Int
avoid_aab = ([0,1,2,3],0,[0,1,2], f) where 
    f 3 _ = 3
    f 0 'a' = 1
    f 0 'b' = 0
    f 1 'a' = 2
    f 1 'b' = 0
    f 2 'a' = 2
    f 2 'b' = 3
    f q c = 0

end_ab :: FSM Int
end_ab = ([0,1,2],0,[2], f) where 
    f 0 'a' = 1
    f 0 'b' = 0
    f 1 'a' = 1
    f 1 'b' = 2
    f 2 'a' = 1
    f 2 'b' = 0
    f q c = 0


-- Bypassability for extended regular expressions, computed directly by recursion.
byp :: RegExp' -> Bool
byp Zero = False
byp One = True
byp (Let' c) = False
byp (Union' rs) = any byp rs  
byp (Cat' rs) = all byp rs
byp (Star' r) = True

-- Regular-expression derivatives (aka left quotients) on extended regular
-- expressions, computed directly by recursion.
deriv :: Char -> RegExp' -> RegExp'
deriv a Zero = Zero 
deriv a One = Zero
deriv a (Let' c) = if a == c then One else Zero
deriv a (Union' rs) = Union' (map (\r -> deriv a r) rs)
deriv a (Cat' rs) = Union' (dCat'_h a rs)
deriv a (Star' r) = Cat' ([deriv a r]++[Star' r])

dCat'_h :: Char -> [RegExp']-> [RegExp']
dCat'_h a [] = []
dCat'_h a (r:rs) = (Cat' ((deriv a r):rs) ):(if byp r then dCat'_h a rs else [])


-- Convert an RegExp' to an FSM using the derivative (Brzozowski) construction.
-- States are SIMPLIFIED extended REs.  Note: to construct all the states,
-- you will have to use a unary closure process.
conv :: RegExp' -> FSM RegExp' 
conv r = (qs, s, fs, d) where
  qs = uclosure [simp r] (\r -> [simp (deriv a r) | a <- sigma])
  eclose es qs = uclosure qs (\q -> [q2 | (q1,q2) <- es, q1 == q])
  s = simp r
  fs = [q | q <- qs, byp q]
  d q a = simp (deriv a q)
            
-- Some regular expressions for testing.

ab   = toRE' "aa.bb.+*"            -- every letter is duplicated
ttla = toRE' "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE' "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE' "aba.+*b.b.aab.+*."   -- contains bb exactly once
-- Test, and show your tests! You may copy code from previous labs to help.

{-
*Main> byp Zero
False
*Main> byp One
True
*Main> byp (Let' 'c')
False
*Main> byp (Let' 'a')
False
*Main> byp (Let' 'e')
False
*Main> byp (Union' [Let' 'a'])
False
*Main> byp (Union' [Let' 'a', Let' 'b'])
False
*Main> byp (Union' [Let' 'a', Let' 'b', Let' 'c', Let' 'd'])
False
*Main> byp (Cat' [Let' 'b'])
False
*Main> byp (Cat' [Let' 'b', Let' 'f'])
False
*Main> byp (Cat' [Let' 'b', Let' 'f', Let' 'c', Let' 'd', Let' 'g'])
False
*Main> byp (Star' Zero)
True
*Main> byp (Star' One)
True
*Main> byp (Star' (Star' Zero))
True
*Main> byp (Star' (Star' One))
True       
*Main> byp (toRE' "ab.")
False
*Main> byp (toRE' "b*")
True
*Main> byp (toRE' "a*")
True
*Main> byp (toRE' "aa.bb.+*")
True         
*Main> byp (toRE' "ab.a+")
False       
*Main> byp (toRE' "ab+*a.ab+.ab+.")
False       
*Main> byp (toRE' "b*a.b*.a.*b*.")
True
*Main> byp (toRE' "b*a.b*.a.*")
True
*Main> byp (toRE' "1b+ab+*bb..+")
True   
*Main> byp (toRE' "aaba.+*.")
False                                                                                                                                                                                                                                                              True  
*Main> deriv 'a' Zero
Zero
*Main> deriv 'a' One
Zero
*Main> deriv 'a' (Let' 'c')
Zero
*Main> deriv 'a' (Let' 'e')
Zero
*Main> deriv 'a' (Let' 'a')
One
*Main> deriv 'b' (Let' 'b')
One
*Main> deriv 'b' (Union' [Let' 'e', Let' 'f'])
Union' [Zero,Zero]
*Main> deriv 'e' (Union' [Let' 'e', Let' 'f'])
Union' [One,Zero]
*Main> deriv 'f' (Union' [Let' 'e', Let' 'f'])
Union' [Zero,One]
*Main> deriv 'f' (Cat' [Let' 'e', Let' 'f'])
Union' [Cat' [Zero,Let' 'f']]
*Main> deriv 'e' (Cat' [Let' 'e', Let' 'f'])
Union' [Cat' [One,Let' 'f']]
*Main> deriv 'd' (Cat' [Let' 'e', Let' 'f'])
Union' [Cat' [Zero,Let' 'f']]
*Main> deriv 'd' (Cat' [Let' 'e', Let' 'f', Let' 'g'])
Union' [Cat' [Zero,Let' 'f',Let' 'g']]
*Main> deriv 'g' (Cat' [Let' 'e', Let' 'f', Let' 'g'])
Union' [Cat' [Zero,Let' 'f',Let' 'g']]
*Main> deriv 'a' (Star' Zero)
Cat' [Zero,Star' Zero]
*Main> deriv 'a' (Star' One)
Cat' [Zero,Star' One]
*Main> deriv 'a' (Star' (Star' Zero))
Cat' [Cat' [Zero,Star' Zero],Star' (Star' Zero)]
*Main> deriv 'a' (Star' (Star' One))
Cat' [Cat' [Zero,Star' One],Star' (Star' One)]
*Main> fromRE' (simp ( deriv 'a' (toRE' "@")))
Empty
*Main> fromRE' (simp ( deriv 'c' (toRE' "@")))
Empty
*Main> fromRE' (simp ( deriv 'c' (toRE' "ab+*")))
Empty
*Main> fromRE' (simp ( deriv 'a' (toRE' "ab+*bb..")))
Cat (Star (Union (Let 'a') (Let 'b'))) (Cat (Let 'b') (Let 'b'))
*Main> fromRE' (simp ( deriv 'a' (toRE' "ab*.")))
Star (Let 'b')
*Main> fromRE' (simp ( deriv 'a' (toRE' "aba.+*")))
Star (Union (Let 'a') (Cat (Let 'b') (Let 'a')))
*Main> fromRE' (simp ( deriv 'a' (toRE' "aaba.+*.")))
Star (Union (Let 'a') (Cat (Let 'b') (Let 'a')))
*Main> fromRE' (simp ( deriv 'a' (toRE' "aaba.+*.")))
Star (Union (Let 'a') (Cat (Let 'b') (Let 'a')))
*Main> fromRE' (simp ( deriv 'a' (toRE' "b*a.b*.a.*")))
Cat (Star (Let 'b')) (Cat (Let 'a') (Star (Cat (Star (Let 'b')) (Cat (Let 'a') (Cat (Star (Let 'b')) (Let 'a'))))))
*Main> fromRE' (simp ( deriv 'a' (toRE' "b*a.")))
Star Empty
*Main> checkFSM (intify (conv (toRE' "ab+*bb..")))
True
*Main> checkFSM (intify (conv (toRE' "ab+*")))
True
*Main> checkFSM (intify (conv (toRE' "abab.+*.1a+.")))
True
*Main> checkFSM (intify (conv (toRE' "aa.bb.+*")))
True
*Main> checkFSM (intify (conv (toRE' "b*a.b*.a.*b*.")))
True
*Main> checkFSM (intify (conv (toRE' "aba.+*b.b.aab.+*.")))
True
*Main> checkFSM (intify (conv (toRE' "@")))
True
*Main> checkFSM (intify (conv (toRE' "1b+ab+*bb..+")))
True
*Main> checkFSM (intify (conv (toRE' "bab+*bb..+")))
True
*Main> checkFSM (intify (conv (toRE' "bab+*")))
True
*Main> checkFSM (intify (conv (toRE' "aba.+*")))
True
*Main> checkFSM (intify (conv (toRE' "b*a.b*.a.*")))
True
-}