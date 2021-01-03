-- Lab 6:  FSM constructions for regular operators

import Data.List
import Data.Array
import Control.Monad (replicateM)  -- for strings function below

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]

-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)  
type FSM a = ([a], a, [a], a -> Char -> a)


---------------- A solution to Lab 5, ported to FSM a ------------------------
  
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
odd_bs = ([0,1], 0, [1], d) where
  d q a = if a == 'b' then (q+1) `mod` 2 else q

-- avoid w is a machine that accepts strings that don't have w as a substring
-- states: prefixes of w read so far (with w itself as a trap state)
avoid :: String -> FSM String
avoid xs = (qs, "", init qs, d) where
  qs = inits xs
  d w a = if w == xs then w else head [w | w <- tails (w++[a]), isPrefixOf w xs]

-- no_aab is a machine that accepts strings that don't have "aab" as a substring
no_aab :: FSM String
no_aab = avoid "aab"

-- ends_in w is a machine that accepts strings that end in w
-- states: last <= n characters read (in reverse order, for ease of computation)
-- Note: this machine has 2^(n+1) - 1 states when |sigma| = 2
ends_in :: String -> FSM String
ends_in xs = (qs, "", [reverse xs], d) where
  n = length xs
  qs = strings n
  d w a = take n (a : w)

-- ends_in_ab is a machine that accepts strings ending in "ab"
ends_in_ab :: FSM String
ends_in_ab = ends_in "ab"
---------------- Some additional useful functions --------------------------

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


---------------- Lab 6 begins here -----------------------------------------

-- Complete the FSM constructions for the regular expression operators
-- and test your functions adequately

-- Machine that accepts the empty language
emptyFSM :: FSM Int
emptyFSM = ([0], 0, [], d) where 
    d 0 _ = 0
{-
*Main> checkFSM emptyFSM
True
*Main> accept1 emptyFSM ""
False
*Main> accept1 emptyFSM "a"
False
*Main> accept2 emptyFSM "a"
False
*Main> accept2 emptyFSM ""
False
-}

-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM x = ([0,1,2], 0, [1], d) where 
    d q y = if q == 0 && y == 'a' then 1 else 2
{-
*Main> checkFSM (letterFSM 'a')
True
*Main> accept1 (letterFSM 'a') ""
False
*Main> accept1 (letterFSM 'a') ""
False
*Main> accept1 (letterFSM 'a') "a"
True
*Main> accept1 (letterFSM 'a') "aa"
False
*Main> accept1 (letterFSM 'b') ""
False
*Main> accept1 (letterFSM 'b') "a"
True
*Main> accept1 (letterFSM 'b') "aa"
False
*Main> accept1 (letterFSM 'b') "b"
False
*Main> accept1 (letterFSM 'b') "bb"
False
*Main> accept1 (letterFSM 'c') ""
False
*Main> accept1 (letterFSM 'c') "a"
True
*Main> accept1 (letterFSM 'c') "aa"
False
*Main> accept2 (letterFSM 'a') ""
False
*Main> accept2 (letterFSM 'a') "a"
True
*Main> accept2 (letterFSM 'a') "aa"
False
*Main> accept2 (letterFSM 'b') ""
False
*Main> accept2 (letterFSM 'b') "a"
True
*Main> accept2 (letterFSM 'b') "b"
False
*Main> accept2 (letterFSM 'b') "bb"
False
*Main> accept2 (letterFSM 'c') ""
False
*Main> accept2 (letterFSM 'c') "a"
True
-}
-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs = [(q1,q2) | q1 <- qs1, q2 <- qs2, q1 `elem` fs1 || q2 `elem` fs2]
  d (q1, q2) a = (d1 q1 a, d2 q2 a)
{-
*Main> checkFSM (unionFSM odd_bs no_aab)
True
*Main> checkFSM (unionFSM ends_in_ab no_aab)
True
*Main> checkFSM (unionFSM odd_bs ends_in_ab)
True
*Main> accept1 (unionFSM odd_bs ends_in_ab) "a"
False
*Main> accept1 (unionFSM odd_bs ends_in_ab) "aa"
False
*Main>  accept1 (unionFSM odd_bs ends_in_ab) "aaa"
False
*Main>  accept2 (unionFSM odd_bs ends_in_ab) "aaa"
False
*Main> accept2 (unionFSM odd_bs ends_in_ab) "aa"
False
*Main>  accept2 (unionFSM odd_bs ends_in_ab) "a"
False
*Main> accept1 (unionFSM ends_in_ab no_aab) "a"
False
*Main> accept1 (unionFSM ends_in_ab no_aab) "aa"
False
*Main> accept1 (unionFSM ends_in_ab no_aab) "aaa"
False
*Main>  accept2 (unionFSM ends_in_ab no_aab) "aaa"
False
*Main> accept2 (unionFSM ends_in_ab no_aab) "aa"
False
*Main> accept2 (unionFSM ends_in_ab no_aab) "a"
False
*Main> accept1 (unionFSM odd_bs no_aab) "a"
False
*Main> accept1 (unionFSM odd_bs no_aab) "aa"
False
*Main> accept1 (unionFSM odd_bs no_aab) "aaa"
False
*Main> accept2 (unionFSM odd_bs no_aab) "a"
False
*Main> accept2 (unionFSM odd_bs no_aab) "aa"
False
*Main>  accept2 (unionFSM odd_bs no_aab) "aaa"
True
-}
-- Machine that accepts the concatenation of the languages accepted by m1 and m2
catFSM :: (Eq a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  correctX q x = if q `elem` fs1 then union x [s2] else x
  qs = [(q, correctX q x) | q <- qs1, x <- power qs2]
  s  = (s1, [s2 | s1 `elem` fs1])
  fs = [(q1,x) | (q1,x) <- qs, overlap x fs2]
  d (q,x) a = (q',x') where
     q' = d1 q a
     x' = norm $ [s2 | q' `elem` fs1] ++ map (\q2 -> d2 q2 a) x
{-
*Main> checkFSM (catFSM odd_bs no_aab)
False
*Main> accept1 (catFSM odd_bs no_aab) "a"
False
*Main> accept1 (catFSM odd_bs no_aab) "aa"
False
*Main> accept1 (catFSM odd_bs no_aab) "aaa"
False
*Main> accept2 (catFSM odd_bs no_aab) "a"
False
*Main> accept2 (catFSM odd_bs no_aab) "aa"
False
*Main> accept2 (catFSM odd_bs no_aab) "aaa"
False
*Main> checkFSM (catFSM odd_bs ends_in_ab)
False
*Main> accept1 (catFSM odd_bs ends_in_ab) "a"
False
*Main> accept1 (catFSM odd_bs ends_in_ab) "aa"
False
*Main> accept1 (catFSM odd_bs ends_in_ab) "aaa"
False
*Main> accept2 (catFSM odd_bs ends_in_ab) "a"
False
*Main> accept2 (catFSM odd_bs ends_in_ab) "aa"
False
*Main> accept2 (catFSM odd_bs ends_in_ab) "aaa"
False
*Main> checkFSM (catFSM ends_in_ab no_aab)
True
*Main> accept1 (catFSM ends_in_ab no_aab) "a"
False
*Main> accept1 (catFSM ends_in_ab no_aab) "aa"
False
*Main> accept1 (catFSM ends_in_ab no_aab) "aaa"
False
*Main> accept2 (catFSM odd_bs ends_in_ab) "a"
False
*Main> accept2 (catFSM odd_bs ends_in_ab) "aa"
False
*Main> accept2 (catFSM odd_bs ends_in_ab) "aaa"
False
*Main> checkFSM (catFSM odd_bs ends_in_ab)
False
-}
-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = power qs1
  s  = []
  fs = [q | q <- qs, null q || overlap q fs1]
  d [] a = norm $ [s1 | q `elem` fs1] ++ [q] where q =  d1 s1 a
  d x a = norm $ [s1 | overlap x' fs1] ++ x' where
    x' = map (\q -> d1 q a) x
{-
*Main> checkFSM (starFSM odd_bs)
True
*Main> checkFSM (starFSM ends_in_ab)
True
*Main> checkFSM (starFSM no_aab)
True
*Main> accept1 (starFSM odd_bs) "a"
False
*Main> accept1 (starFSM odd_bs) "aa"
False
*Main> accept1 (starFSM odd_bs) "aaa"
False
*Main> accept1 (starFSM odd_bs) "aaaa"
False
*Main> accept1 (starFSM odd_bs) "aaaaa"
False
*Main> accept2 (starFSM odd_bs) "a"
False
*Main> accept2 (starFSM odd_bs) "aa"
False
*Main> accept2 (starFSM odd_bs) "aaa"
False
*Main> accept2 (starFSM odd_bs) "aaaa"
False
*Main> accept2 (starFSM odd_bs) "aaaaa"
False
*Main> accept1 (starFSM ends_in_ab) "a"
False
*Main> accept1 (starFSM ends_in_ab) "aa"
False
*Main> accept1 (starFSM ends_in_ab) "aaa"
False
*Main> accept1 (starFSM ends_in_ab) "aaaa"
False
*Main> accept1 (starFSM ends_in_ab) "aaaaa"
False
*Main> accept2 (starFSM ends_in_ab) "a"
False
*Main> accept2 (starFSM ends_in_ab) "aa"
False
*Main> accept2 (starFSM ends_in_ab) "aaa"
False
*Main> accept2 (starFSM ends_in_ab) "aaaa"
False
*Main> accept2 (starFSM ends_in_ab) "aaaaa"
False
*Main> accept1 (starFSM no_aab) "a"
True
*Main> accept1 (starFSM no_aab) "aa"
True
*Main> accept1 (starFSM no_aab) "aaa"
True
*Main> accept1 (starFSM no_aab) "aaaa"
True
*Main> accept1 (starFSM no_aab) "aaaaa"
True
*Main> accept2 (starFSM no_aab) "a"
True
*Main> accept2 (starFSM no_aab) "aa"
True
*Main> accept2 (starFSM no_aab) "aaa"
True
*Main> accept2 (starFSM no_aab) "aaaa"
True
*Main> accept2 (starFSM no_aab) "aaaaa"
True
-}
---------------- Bonus Features (for testing and experimenting) ------------

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

instance (Show RegExp) where    -- use precedence to minimize parentheses
  showsPrec d Empty         = showString "@"
  showsPrec d (Let c)    = showString [c]
  showsPrec d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                              showsPrec 6 r1 .
                              showString "+" .
                              showsPrec 6 r2
  showsPrec d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                              showsPrec 7 r1 .
                              showsPrec 7 r2
  showsPrec d (Star r1)     = showsPrec 9 r1 .     -- prec(Star) = 8
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

-- Use constructions above to get reduced machine associated with regex
-- Warning: it can take a lot of time/memory to compute these for "big" regex's
-- We will see much better ways later in the course
re2fsm :: RegExp -> FSM Int
re2fsm Empty = emptyFSM
re2fsm (Let c) = letterFSM c
re2fsm (Union r1 r2) = reduce $ unionFSM (re2fsm r1) (re2fsm r2)
re2fsm (Cat r1 r2) = reduce $ catFSM (re2fsm r1) (re2fsm r2)
re2fsm (Star r1) = reduce $ starFSM (re2fsm r1)