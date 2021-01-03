-- Lab 8 Solution: Additional constructions, nondeterministic machines

import Data.List
import Data.Array
import Control.Monad (replicateM)  -- for strings function below

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)  
type FSM a = ([a], a, [a], a -> Char -> a)


---------------- Given functions ----------------

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

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Let x:rs)

-- Check whether a finite state machine (qs, s, fs, ts) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (s is in qs)
-- (3) Final states are states (fs is a subset of qs)
-- (4) Transition function gives a state in qs for every state in qs and
--     letter from sigma

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

eodd_bs :: EFSM Int
eodd_bs = ([0,1],[0],[1],f,[(1,0),(1,1)]) where
  f 0 'b' = [1]
  f 1 'b' = [0]
  f q c = [q]

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
    
eend_ab :: EFSM Int
eend_ab = ([0, 1, 2],[0],[2],f,[(2,2),(2,0),(2,1)]) where
  f 0 'a' = [1]
  f 0 'b' = [0]
  f 1 'a' = [1]
  f 1 'b' = [2]
  f 2 'a' = [1]
  f 2 'b' = [0] 

---------------- Part 1: Additional constructions ----------------
-- Define the operations given in Section 7 of the notes

-- Intersection
inters :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a,b)
inters m1@(qs1, s1, fs1, d1) m2@(qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs =  fs1 >< fs2
  -- fs = [(q1,q2) | q1 <- qs1, q2 <- qs2, q1 `elem` fs1, q2 `elem` fs2]
  d (q1, q2) a = (d1 q1 a, d2 q2 a)

{-
*Main> checkFSM (inters odd_bs avoid_aab)
True
*Main> checkFSM (inters odd_bs end_ab)
True
*Main> checkFSM (inters avoid_aab end_ab)
True
*Main> accept1 (inters odd_bs avoid_aab) "b"
True
*Main> accept1 (inters odd_bs end_ab) "b"
False
*Main> accept1 (inters avoid_aab end_ab) "b"
False
*Main> accept1 (inters avoid_aab end_ab) "bb"
False
*Main> accept1 (inters odd_bs end_ab) "bb"
False
*Main> accept1 (inters odd_bs avoid_aab) "bb"
False
*Main>  accept2 (inters odd_bs avoid_aab) "bb"
False
*Main> accept2 (inters odd_bs end_ab) "bb"
False
*Main> accept2 (inters avoid_aab end_ab) "bb"
False
*Main> accept2 (inters avoid_aab end_ab) "b"
False
*Main> accept2 (inters odd_bs end_ab) "b"
False
*Main> accept2 (inters odd_bs avoid_aab) "b"
True
-}
-- Complement
compl :: Eq a => FSM a -> FSM a
compl m@(qs1, s1, fs1, d1) = (qs, s, fs, d) where 
  qs = qs1
  s  = s1
  fs = [q | q <- qs1, q `notElem` fs1]
  -- fs = [q | q <- qs1, null q || overlap q fs1]
  d = d1
  
{-
*Main> checkFSM (compl odd_bs)
True
*Main> checkFSM (compl avoid_aab)
True
*Main> checkFSM (compl end_ab)
True
*Main> accept1 (compl odd_bs) "b"
False
*Main>  accept1 (compl avoid_aab) "bb"
False
*Main>  accept1 (compl end_ab) "bb"
True
*Main>  accept1 (compl avoid_aab) "bbb"
False
*Main>  accept2 (inters odd_bs avoid_aab) "bb"
False
*Main> accept2 (inters odd_bs end_ab) "bb"
False
*Main> accept2 (inters avoid_aab end_ab) "bb"
False
*Main> accept2 (inters avoid_aab end_ab) "b"
False
*Main> accept2 (inters odd_bs end_ab) "b"
False
*Main> accept2 (inters odd_bs avoid_aab) "b"
True
*Main> accept2 (compl avoid_aab) "bbb"
False
*Main> accept2 (compl end_ab) "bb"
True
*Main> accept2 (compl avoid_aab) "bb"
False
*Main> accept2 (compl odd_bs) "b"
False
-}

onestr :: String -> RegExp
onestr [] = Star Empty
onestr [x] = Let x
onestr (x:xs) = Cat (Let x) (onestr xs)

-- Direct homomorphic image: k is a substitution
homo_dir :: (Char -> String) -> RegExp -> RegExp
homo_dir k Empty = Empty
homo_dir k (Let c) = onestr (k c) 
homo_dir k (Union r1 r2) = Union (homo_dir k r1) (homo_dir k r2)
homo_dir k (Cat r1 r2) = Cat (homo_dir k r1) (homo_dir k r2)
homo_dir k (Star r1) = Star (homo_dir k r1)

{-
*Main> homo_dir k1 Empty
Empty
*Main> homo_dir k1 (Let 'a')
Cat (Let 'a') (Cat (Let 'b') (Let 'b'))
*Main> homo_dir k1 (Let 'b')
Cat (Let 'b') (Let 'a')
*Main> homo_dir k1 (Union Empty Empty)
Union Empty Empty
*Main> homo_dir k (Union Empty ab)
Union Empty (Star (Union (Cat (Cat (Let 'a') (Let 'a')) (Cat (Let 'a') 
(Let 'a'))) (Cat (Let 'b') (Let 'b'))))
*Main> homo_dir k1 (Union ab Empty)
Union (Star (Union (Cat (Cat (Let 'a') (Cat (Let 'b') (Let 'b'))) 
(Cat (Let 'a') (Cat (Let 'b') (Let 'b')))) (Cat (Cat (Let 'b') (Let 'a')) 
(Cat (Let 'b') (Let 'a'))))) Empty
*Main> homo_dir k1 (Cat Empty Empty)
Cat Empty Empty
*Main> homo_dir k_switch (Cat Empty ttla)
Cat Empty (Cat (Cat (Cat (Star (Union (Let 'b') (Let 'a'))) (Let 'b')) (Union (Let 'b') (Let 'a'))) 
(Union (Let 'b') (Let 'a')))
*Main> homo_dir k1 (Star Empty)
Star Empty
 homo_dir k1 (Star ab)
Star (Star (Union (Cat (Cat (Let 'a') (Cat (Let 'b') (Let 'b'))) (Cat (Let 'a') 
(Cat (Let 'b') (Let 'b')))) (Cat (Cat (Let 'b') (Let 'a')) (Cat (Let 'b') (Let 'a')))))
-}

-- different functions for use in homomorphic image functions
k :: Char -> String 
k 'b' = "bb"
k 'a' = "a"
k 'c' = "b"

k1 :: (Char -> String)
k1 c = if c == 'a' then "abb" else "ba"

k2 :: (Char -> String)
k2 c = if c == 'b' then "" else [c]

k_del_a :: Char -> String
k_del_a c = if c == 'a' then "" else [c] 

k_switch :: Char -> String
k_switch c = if c == 'a' then "b" else "a" 

-- Some regular expressions for testing.

ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once

-- Inverse homomorphic image
homo_inv :: Eq a => (Char -> String) -> FSM a -> FSM a
homo_inv k m1@(qs1, s1, fs1, d1) = (qs, s, fs, d1) where 
  qs = qs1
  s  = s1
  fs = fs1
  d q a = star d1 (q (k a))

{-
*Main> accept2 (homo_inv k odd_bs) "a"
False
*Main> accept1 (homo_inv k odd_bs) "a"
False
*Main> accept1 (homo_inv k avoid_aab) "a"
True
*Main> accept2 (homo_inv k avoid_aab) "a"
True
*Main> accept2 (homo_inv k end_ab) "a"
False
*Main> accept1 (homo_inv k end_ab) "a"
False
*Main> accept1 (homo_inv k end_ab) "aa"
False
*Main> accept2 (homo_inv k avoid_aab) "aa"
True
*Main> accept2 (homo_inv k avoid_aab) "b"
True
*Main> accept1 (homo_inv k avoid_aab) "b"
True
*Main> accept1 (homo_inv k odd_bs) "b"
True
*Main> accept2 (homo_inv k odd_bs) "b"
True
*Main> accept2 (homo_inv k end_ab) "bb"
False
-}
-- Right quotient
quot_right :: Eq a => [String] -> FSM a -> FSM a
quot_right ws m1@(qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = qs1
  s = s1
  fs = [q | q <- qs1, or [(star d1 q w) `elem` fs1 | w <- ws]] 
  d = d1
  
{-
*Main> accept1 (quot_right ["aaa"] odd_bs) "a"
False
*Main> accept1 (quot_right ["aaa"] odd_bs) "a"
False
*Main> accept1 (quot_right ["aaa"] end_ab) "a"
False
*Main> accept1 (quot_right ["aaa"] avoid_aab) "a"
True
*Main> accept2 (quot_right ["aaa"] odd_bs) "a"
False
*Main> accept2 (quot_right ["aaa"] avoid_aab) "a"
True
*Main> accept2 (quot_right ["aaa"] end_ab) "a"
False
*Main> accept1 (quot_right ["aba"] end_ab) "aa"
False
*Main> accept2 (quot_right ["aba"] end_ab) "aa"
False
*Main> accept2 (quot_right ["aba"] avoid_aab) "a"
False
*Main> accept1 (quot_right ["aba"] avoid_aab) "a"
False
*Main> accept1 (quot_right ["aba"] end_ab) "ab"
False
-}

---------------- Part 2: Nondeterministic machines ----------------

-- Nondeterministic FSMs, indexed by their type of state
-- All states are normalized and the output of d is normalized
-- M = (states, starts, finals, transitions)  
type Trans a = a -> Char -> [a]
type NFSM a = ([a], [a], [a], Trans a)

-- nap_hat d qs a == normalized list of all transitions possible from qs on a
nap_hat :: Ord a => Trans a -> [a] -> Char -> [a]
nap_hat d qs a =  norm $ concat [d q a | q <- qs, a <- sigma]

-- nap_hat_star d qs w == normalized list of transitions possible from qs on w
nap_hat_star :: Ord a => Trans a -> [a] -> [Char] -> [a]
nap_hat_star d qs ws = star (nap_hat d) qs ws
--nap_hat_star = foldl' . nap_hat

-- nacc m w == m accept the string w
nacc :: Ord a => NFSM a -> [Char] -> Bool
nacc (qs, ss, fs, d) w = overlap (nap_hat_star d ss w) fs

{-
*Main> nacc (fsm_to_nfsm odd_bs) "b"
True
*Main> nacc (fsm_to_nfsm avoid_aab) "b"
True
*Main> nacc (fsm_to_nfsm end_ab) "b"
False
*Main>  nacc (fsm_to_nfsm odd_bs) "bb"
True
*Main>  nacc (fsm_to_nfsm avoid_aab) "bb"
True
*Main>  nacc (fsm_to_nfsm end_ab) "bb"
True
*Main>  nacc (fsm_to_nfsm end_ab) "bbb"
True
*Main>  nacc (fsm_to_nfsm avoid_aab) "bbb"
True
*Main>  nacc (fsm_to_nfsm odd_bs) "bbb"
True
True
*Main>  nacc (fsm_to_nfsm avoid_aab) "ababa"
True
*Main>  nacc (fsm_to_nfsm avoid_aab) "abbb"
True
-}

-- Nondeterministic FSMs with epsilon moves, indexed by their type of state
-- M = (states, starts, finals, transitions, epsilon-moves)
type Eps a = [(a, a)]
type EFSM a = ([a], [a], [a], Trans a, Eps a)

-- Normalized epsilon closure of a set of states (Hint: use uclosure)
eclose :: Ord a => Eps a -> [a] -> [a]
eclose es qs = uclosure qs (\q -> [q2 | (q1,q2) <- es, q1 == q])
  
-- eap_has d es qs a == eclosure of transitions possible from qs on a
eap_hat :: Ord a => (Trans a, Eps a) -> [a] -> Char -> [a]
eap_hat (d,es) qs a  = eclose es (nap_hat d qs a)

-- eap_hat_star ts es q w == eclosure of transitions possible from qs on w
eap_hat_star :: Ord a => (Trans a, Eps a) -> [a] -> [Char] -> [a]
eap_hat_star (d,es) qs a  = star (eap_hat (d,es)) qs a
--eap_hat_star = foldl' . eap_hat


eacc :: Ord a => EFSM a -> [Char] -> Bool
eacc (qs, ss, fs, d, es) w = overlap (eap_hat_star (d,es) (eclose es ss) w) fs

{-
*Main> eacc eend_ab ""
False
*Main> eacc eend_ab "a"
False
*Main> eacc eend_ab "ab"
True
*Main> eacc eend_ab "abb"
True
*Main> eacc eend_ab "abba"
True
*Main> eacc eend_ab "abbaa"
True
*Main> eacc eend_ab "abbaab"
True
*Main> eacc eend_ab "abbaaba"
True
*Main> eacc eend_ab "abbaabab"
True
*Main> eacc eend_ab "abbaababa"
True
*Main> eacc eodd_bs "abbaababa"
True
*Main> eacc eodd_bs ""
False
*Main> eacc eodd_bs "a"
True
*Main> eacc eodd_bs "ab"
True
*Main> eacc eodd_bs "abb"
True
*Main> eacc eodd_bs "abba"
True
*Main> eacc eodd_bs "abbaa"
True
*Main> eacc eodd_bs "abbaab"
True
*Main> eacc eodd_bs "abbaaba"
True
*Main> eacc eodd_bs "abbaabab"
True
*Main> eacc eodd_bs "abbaababa"
True
*Main> eacc eodd_bs "abbaababa"
True
-}

---------------- Part 3: Conversion between machines ----------------

-- Easy conversion from FSM to NFSM (given)
fsm_to_nfsm :: Eq a => FSM a -> NFSM a
fsm_to_nfsm (qs1, s1, fs1, d1) = (qs, s, fs, d) where 
  qs = qs1
  s = [s1] 
  fs = fs1
  d q a = [d1 q a]


-- Conversion from NFSM to FSM by the "subset construction"
nfsm_to_fsm :: Ord a => NFSM a -> FSM [a]
nfsm_to_fsm (qs1, ss1, fs1, d1) = (qs, s, fs, d) where
  qs = power(qs1)
  s  = ss1
  fs = [x | x <- qs, x `overlap` fs1] 
  d q a = nap_hat d1 q a


-- Similar conversion from EFSM to FSM using epsilon closure
efsm_to_fsm :: Ord a => EFSM a -> FSM [a]
efsm_to_fsm (qs1, ss1, fs1, d1, es1) = (qs, s, fs, d) where
  qs = subsequences qs1
  s  = eclose es1 ss1
  fs = [x | x <- qs, x `overlap` fs1] 
  d q a =  eap_hat (d1,es1) q a

{-

-}
{- Tests:

1. m and fsm_to_nfsm m accept the same strings

*Main> accept1 odd_bs "a"
False
*Main> accept1 odd_bs "aa"
False
*Main> accept1 odd_bs "aaa"
False
*Main> accept1 odd_bs "aaab"
True
*Main> accept1 avoid_aab "aa"
True
*Main> accept1 avoid_aab "a"
True
*Main> accept1 avoid_aab "aaa"
True
*Main> accept1 avoid_aab "aaab"
False
*Main> accept1 end_ab "a"
False
*Main> accept1 end_ab "aa"
False
*Main> accept1 end_ab "aaa"
False
*Main> accept1 end_ab "aaab"
True
*Main> nacc (fsm_to_nfsm odd_bs) ""
False
*Main> nacc (fsm_to_nfsm odd_bs) "b"
True
*Main> nacc (fsm_to_nfsm odd_bs) "bb"
True
*Main> nacc (fsm_to_nfsm odd_bs) "a"
True
*Main> nacc (fsm_to_nfsm odd_bs) "aa"
True
*Main> nacc (fsm_to_nfsm odd_bs) "aaa"
True
*Main> nacc (fsm_to_nfsm odd_bs) "aaab"
True
*Main> nacc (fsm_to_nfsm avoid_aab) "a"
True
*Main> nacc (fsm_to_nfsm avoid_aab) "aa"
True
*Main> nacc (fsm_to_nfsm avoid_aab) "aaa"
True
*Main> nacc (fsm_to_nfsm avoid_aab) "aaab"
True
*Main> nacc (fsm_to_nfsm end_ab) "a"
False
*Main> nacc (fsm_to_nfsm end_ab) "aa"
True
*Main> nacc (fsm_to_nfsm end_ab) "aaa"
True
*Main> nacc (fsm_to_nfsm end_ab) "aaab"
True

2. m and nfsm_to_fsm m accept the same strings

*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm odd_bs) ""
False
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm odd_bs) "b"
True
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm odd_bs) "bbb"
True
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm odd_bs) "bbba"
True
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm avoid_aab) ""
True
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm avoid_aab) "b"
True
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm avoid_aab) "bb"
True
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm avoid_aab) "bbb"
True
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm avoid_aab) "bbba"
True
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm end_ab) ""
False
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm end_ab) "b"
False
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm end_ab) "bb"
True
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm end_ab) "bbb"
True
*Main> accept1 (nfsm_to_fsm $ fsm_to_nfsm end_ab) "bbba"
True
*Main>  nacc (fsm_to_nfsm odd_bs) ""
False
*Main> nacc (fsm_to_nfsm odd_bs) "b"
True
*Main> nacc (fsm_to_nfsm odd_bs) "bb"
True
*Main> nacc (fsm_to_nfsm odd_bs) "bbb"
True
*Main> nacc (fsm_to_nfsm odd_bs) "bbba"
True
*Main> nacc (fsm_to_nfsm avoid_aab) ""
True
*Main> nacc (fsm_to_nfsm avoid_aab) "b"
True
*Main> nacc (fsm_to_nfsm avoid_aab) "bb"
True
*Main> nacc (fsm_to_nfsm avoid_aab) "bbb"
True
*Main> nacc (fsm_to_nfsm avoid_aab) "bbba"
True
*Main> nacc (fsm_to_nfsm end_ab) ""
False
*Main> nacc (fsm_to_nfsm end_ab) "b"
False
*Main> nacc (fsm_to_nfsm end_ab) "bb"
True
*Main> nacc (fsm_to_nfsm end_ab) "bbb"
True
*Main> nacc (fsm_to_nfsm end_ab) "bbba"
True
3. m and efsm_to_fsm m accept the same strings

*Main> accept1 (efsm_to_fsm eodd_bs) ""
False
*Main> accept1 (efsm_to_fsm eodd_bs) "b"
True
*Main> accept1 (efsm_to_fsm eodd_bs) "bb"
True
*Main> accept1 (efsm_to_fsm eodd_bs) "bba"
True
*Main> accept1 (efsm_to_fsm eodd_bs) "ab"
True
*Main> accept1 (efsm_to_fsm eodd_bs) "abba"
True
*Main> accept1 (efsm_to_fsm eodd_bs) "abbabb"
True
*Main> accept1 (efsm_to_fsm eodd_bs) "abbabba"
True
*Main> accept1 (efsm_to_fsm eodd_bs) "aa"
True
*Main> accept1 (efsm_to_fsm eodd_bs) "aabbb"
True
*Main> accept1 (efsm_to_fsm eodd_bs) "aabbbbbb"
True
*Main> accept1 (efsm_to_fsm eodd_bs) "aabbbbbbbbbbba"
True
*Main> accept1 (efsm_to_fsm eodd_bs) "aabbbbbbbbbbbbba'"
True
*Main> accept1 (efsm_to_fsm eend_ab) ""
False
*Main> accept1 (efsm_to_fsm eend_ab) "b"
False
*Main> accept1 (efsm_to_fsm eend_ab) "bb"
True
*Main> accept1 (efsm_to_fsm eend_ab) "bba"
True
*Main> accept1 (efsm_to_fsm eend_ab) "ab"
True
*Main> accept1 (efsm_to_fsm eend_ab) "abba"
True
*Main> accept1 (efsm_to_fsm eend_ab) "abbabb"
True
*Main> accept1 (efsm_to_fsm eend_ab) "abbabba"
True
*Main> accept1 (efsm_to_fsm eend_ab) "bbbbb"
True
*Main> accept1 (efsm_to_fsm eend_ab) "aa"
True
*Main> accept1 (efsm_to_fsm eend_ab) "aabbbbb"
True
*Main> accept1 (efsm_to_fsm eend_ab) "aabbbbba"
True
*Main> accept1 (efsm_to_fsm eend_ab) "aabbbbbabababa"
True
*Main> accept1 (efsm_to_fsm eend_ab) "aabbbbbabababaa"
True
*Main> accept1 (efsm_to_fsm eend_ab) "aabb"
True
*Main> accept1 (efsm_to_fsm eend_ab) "aabbbb"
True
*Main> eacc eodd_bs "a"
True
*Main> eacc eodd_bs "aa"
True
*Main> eacc eodd_bs "aaa"
True
*Main> eacc eodd_bs "aaab"
True
*Main> eacc eodd_bs "aaabba"
True
*Main> eacc eodd_bs "aaaba"
True
*Main> eacc eodd_bs "aaabab"
True
*Main> eacc eodd_bs "aaababbbbbb"
True
*Main> eacc eodd_bs "aaababbbbbbbbbbbb"
True
*Main> eacc eodd_bs "aaababbbbbbbbbbbbbbba"
True
*Main> eacc eodd_bs "aaaaaa"
True
*Main> eacc eodd_bs "aababababa"
True
*Main> eacc eend_ab "a"
False
*Main> eacc eend_ab "aa"
True
*Main> eacc eend_ab "aaa"
True
*Main> eacc eend_ab "aaab"
True
*Main> eacc eend_ab "aaaba"
True
*Main> eacc eend_ab "aaabab"
True
*Main> eacc eend_ab "aaababbbbb"
True
*Main> eacc eend_ab "aaababbbbbaaabb"
True
*Main> eacc eend_ab "aaababbbbbaaabba"
True
*Main> eacc eend_ab "aaababbbbbaaabba"
True
*Main> eacc eend_ab "aaababbbbbaaabbaa"
True
*Main> eacc eend_ab "aa"
True
*Main> eacc eend_ab "a"
False
*Main> eacc eend_ab "ba"
True
-}
