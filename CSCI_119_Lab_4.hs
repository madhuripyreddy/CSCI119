-- CSci 119, Lab 4

import Data.List (sort, stripPrefix) -- for your solution to Lab 3
import Control.Monad (replicateM)    -- for strings function at the end


-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Length-Ordered Lists over "character type" a (aka "strings")
-- Invariant: In LOL n xs, n == length xs
data LOL a = LOL Int [a] deriving (Eq,Ord)

instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs

-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is sorted with no duplicates
type Lang a = [LOL a]

-- Smart constructor for (finite) languages
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

---- Regular expressions, along with input and output
data RegExp = Empty                -- Empty language
            | Let Char             -- Single letter language
            | Union RegExp RegExp  -- Union
            | Cat RegExp RegExp    -- Concatenation
            | Star RegExp          -- Kleene star
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

-- Quick and dirty postfix RegExp parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = go w [] where
  go [] [r]              = r
  go ('+':xs) (r2:r1:rs) = go xs (Union r1 r2:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat r1 r2:rs)
  go ('*':xs) (r:rs)     = go xs (Star r:rs)
  go ('@':xs) rs         = go xs (Empty:rs)
  go (x:xs) rs           = go xs (Let x:rs)


---------------- Your solution to Lab 3 ----------------

-- Include part of your solution to Lab 3 here for testing purposes.
-- After a few days, I will release my solution for you to use. Don't
-- duplicate the code just given above.
cart :: [a] -> [b] -> [(a,b)]
cart xs [] = []
cart [] ys = []
cart x y = [(a,b) | a <- x, b <- y]

power :: [a] -> [[a]]
power [] = [[]]
power [x] = [[], [x]]
power (x:xs) =  []: map(x:) z ++ tail z
    where 
    z = power xs 
    
dot :: LOL a -> LOL a -> LOL a
dot (LOL y ys) (LOL z zs) = LOL (y + z) (ys ++ zs)
    
rev :: LOL a -> LOL a 
rev (LOL y ys) = LOL y (reverse ys)

merge :: Ord a => Lang a -> Lang a -> Lang a
merge [] ys = ys
merge xs [] = xs 
merge (x:xs) (y:ys)
  | x < y     = x: merge xs (y:ys)
  | x == y    = x: merge xs ys
  | otherwise = y: merge (x:xs) ys
    
cat :: Ord a => Lang a -> Lang a -> Lang a
cat [] zs = []
cat ys [] = []
cat (y:ys) (z:zs) = dot y z : merge (cat ys (z:zs)) (cat [y] zs)

kstar :: Ord a => Lang a -> Lang a
kstar [] = [eps]
kstar (LOL 0 []:xr) = kstar xr 
kstar xs = eps : cat xs (kstar xs)

leftq :: Ord a => LOL a -> Lang a -> Lang a
leftq (LOL r ts) [] = lang []
leftq (LOL r ts) (z:zs) 
  | Nothing  == stripPrefix ts q  = leftq (LOL r ts)zs
  | otherwise = lol f: leftq (LOL r ts)zs
  where
    (LOL m q) = z 
    Just f = stripPrefix ts q
    
lang_of :: RegExp -> Lang Char
lang_of (Empty) = []
lang_of (Let c) = [lol[c]]
lang_of (Cat r1 r2) = cat (lang_of r1) (lang_of r2)
lang_of (Union r1 r2) = merge (lang_of r1) (lang_of r2)
lang_of (Star r1) =  kstar(lang_of r1) 

onestr :: String -> RegExp
onestr [] = Star Empty
onestr xs = if ((length xs)>1) then ((Cat (Let (head xs)) (onestr (tail xs)))) else (Let (head xs))

finite :: [String] -> RegExp
finite l = if ((length l)>1) then ((Union (onestr (head l)) (finite (tail l)))) else (onestr (head l))

---------------- Part 1 ----------------

-- Membership for languages that satisfy the invariant (sorted, no duplicates),
-- even if they are infinite. Only look at the contents of a string when it is
-- necessary to do so, and stop as soon as you know the answer.
memb :: Ord a => LOL a -> Lang a -> Bool
memb  _ [] = False
memb x (y:ys) = case compare x y of 
                LT -> False
                EQ -> True
                GT -> memb x ys

-- Implement the seven recursive predications/operations on RegExp given in
-- Section 3.3 of the notes; call them empty, unitary, byp, inf, rever, lq,
-- and nep. Each should begin with a type declaration. Include several tests
-- for each function.
empty:: RegExp -> Bool 
empty (Empty) = True
empty (Let c) = c == 'a'
empty (Union r1 r2) = empty(r1) && empty(r2)
empty (Cat r1 r2) = empty(r1) || empty(r2)
empty (Star r) = empty r

unitarity :: RegExp -> Bool
unitarity (Empty) = False
unitarity (Let a) = False
unitarity (Union r1 r2) = (unitarity r1 && unitarity r2) || (empty r1 && unitarity r2) || (unitarity r1 && empty r2)
unitarity (Cat r1 r2) = unitarity r1 && unitarity r2
unitarity (Star r1) = empty r1 || unitarity r1

bypassability :: RegExp -> Bool
bypassability (Empty) = False
bypassability (Let a) = False
bypassability (Union r1 r2) = bypassability r1 || bypassability r2
bypassability (Cat r1 r2) = bypassability r1 && bypassability r2
bypassability (Star r1) = True


inf :: RegExp -> Bool
inf (Empty) = False
inf (Let a) = False
inf (Union r1 r2) = inf r1 || inf r2
inf (Cat r1 r2) = (inf r1 && not (empty r2))
                          ||(inf r2 && not (empty r1))
inf (Star r1) = not (empty r1) && not (unitarity r1)

rever :: RegExp -> RegExp
rever (Empty) = Empty
rever (Let a) = Let a
rever (Union r1 r2) = (Union (rever r1) (rever r2))
rever (Cat r1 r2) = (Cat (rever r1) (rever r2))
rever (Star r1) = (Star (rever r1))

lq :: Char -> RegExp -> RegExp
lq s (Empty) = (Empty)
lq s (Let a) = if s == a then (Star (Empty)) else Empty
lq s (Union r1 r2) = (Union (lq s r1) (lq s r2))
lq s (Cat r1 r2) = if (bypassability r1)
                            then
                                  (Union (Cat (lq s r1) r2) (lq s r2))
                            else
                                  (Cat (lq s r1) r2)
lq s (Star r1) = (Cat (lq s r1) (Star r1))

nep :: RegExp -> RegExp
nep (Empty) = Empty
nep (Let r) = Let r
nep (Union r1 r2) = Union (nep(r1)) (nep(r2))
nep (Cat r1 r2) = if (bypassability(r1)) then (Union (Cat (nep(r1)) r2) (nep(r2))) else (Cat (nep r1) r2)
nep (Star r) = Cat (nep(r)) (Star r)

{- Part 1 Testing
*Main> memb (LOL 1 "a") [(LOL 2 "ab"), (LOL 3 "aba"), (LOL 4 "abab")]
False
*Main> memb (LOL 3 "aaa") [(LOL 3 "bbb"), (LOL 4 "aaaa"), (LOL 5 "aaaaa")]
False
*Main> memb (LOL 2 "aa") [(LOL 2 "aa"), (LOL 3 "bba"), (LOL 4 "abba")]
True
*Main> empty Empty
True
*Main> empty (Let 'c')
False
*Main> empty (Let 'a')
True
*Main> empty (Union Empty Empty)
True
*Main> empty (Union ab Empty)
False
*Main> empty (Union Empty bb1)
True
*Main> empty (Union ab bb1)
False
*Main> empty (Union ttla bb1)
True
*Main> empty (Cat Empty Empty)
True
*Main> empty (Cat bb1 Empty)
True
*Main> empty (Cat Empty ttla)
True
*Main> empty (Cat ttla bb1)
True
*Main> empty (Star Empty)
True
*Main> empty (Star ab)
False
*Main> empty (Star bb1)
True
*Main> empty (Star ttla)
True
*Main> unitarity (Empty)
False
*Main> unitarity (Let 'a')
False
*Main> unitarity (Union Empty Empty)
False
*Main> unitarity (Union ab Empty)
False
*Main> unitarity (Union Empty bb1)
False
*Main> unitarity (Union ab bb1)
False
*Main> unitarity (Cat Empty Empty)
False
*Main> unitarity (Cat Empty bb1)
False
*Main> unitarity (Cat ttla Empty)
False
*Main> unitarity (Cat ttla bb1)
False
*Main> unitarity (Star Empty)
True
*Main> unitarity (Star ttla)
True
*Main> unitarity (Star ena)
True
*Main> bypassability Empty
False
*Main> bypassability (Let 'c')
False
*Main> bypassability (Let 'a')
False
*Main> bypassability (Union Empty Empty)
False
*Main> bypassability (Union Empty bb1)
False
*Main> bypassability (Union ena Empty)
True
*Main> bypassability (Union ena bb1)
True
*Main> bypassability (Cat Empty Empty)
False
*Main> bypassability (Cat Empty ttla)
False
*Main> bypassability (Cat bb1 Empty)
False
*Main> bypassability (Cat bb1 ttla)
False
*Main> bypassability (Star Empty)
True
*Main> bypassability (Star ttla)
True
*Main> bypassability (Star Empty)
True
*Main> bypassability (Star ttla)
True
*Main> inf Empty
False
*Main> inf (Let 'a')
False
*Main> inf (Let 'c')
False
*Main> inf (Union Empty Empty)
False
*Main> inf (Union ttla Empty)
False
*Main> inf (Union Empty bb1)
False
*Main> inf (Union ttla bb1)
False
*Main> inf (Cat Empty Empty)
False
*Main> inf (Cat Empty ena)
False
*Main> inf (Cat bb1 Empty)
False
*Main> inf (Cat bb1 ena)
False
*Main> inf (Star Empty)
False
*Main> inf (Star ena)
False
*Main> rever (Empty)
Empty
*Main> rever (Let 'c')
Let 'c'
*Main> rever (Let 'a')
Let 'a'
*Main> rever (Union Empty Empty)
Union Empty Empty
*Main> rever (Union bb1 Empty)
Union (Cat (Cat (Cat (Star (Union (Let 'a') (Cat (Let 'b') (Let 'a')))) (Let 'b')) (Let 'b')) (Star (Union (Let 'a') 
(Cat (Let 'a') (Let 'b'))))) Empty
*Main> rever (Union Empty ab)
Union Empty (Star (Union (Cat (Let 'a') (Let 'a')) (Cat (Let 'b') (Let 'b'))))
*Main> rever (Union bb1 ab)
Union (Cat (Cat (Cat (Star (Union (Let 'a') (Cat (Let 'b') (Let 'a')))) (Let 'b')) (Let 'b')) (Star (Union (Let 'a') (Cat (Let 'a') 
(Let 'b'))))) (Star (Union (Cat (Let 'a') (Let 'a')) (Cat (Let 'b') (Let 'b'))))
*Main> rever (Cat Empty Empty)
Cat Empty Empty
*Main> rever (Cat ab Empty)
Cat (Star (Union (Cat (Let 'a') (Let 'a')) (Cat (Let 'b') (Let 'b')))) Empty
*Main> rever (Cat ena Empty)
Cat (Cat (Star (Cat (Cat (Cat (Star (Let 'b')) (Let 'a')) (Star (Let 'b'))) (Let 'a'))) (Star (Let 'b'))) Empty
*Main> rever (Cat Empty ena)
Cat Empty (Cat (Star (Cat (Cat (Cat (Star (Let 'b')) (Let 'a')) (Star (Let 'b'))) (Let 'a'))) (Star (Let 'b')))
*Main> rever (Cat ab ena)
Cat (Star (Union (Cat (Let 'a') (Let 'a')) (Cat (Let 'b') (Let 'b')))) (Cat (Star (Cat (Cat (Cat (Star (Let 'b')) (Let 'a')) 
(Star (Let 'b'))) (Let 'a'))) (Star (Let 'b')))
*Main> rever (Star Empty)
Star Empty
*Main> rever (Star ab)
Star (Star (Union (Cat (Let 'a') (Let 'a')) (Cat (Let 'b') (Let 'b'))))
*Main> rever (Star ena)
Star (Cat (Star (Cat (Cat (Cat (Star (Let 'b')) (Let 'a')) (Star (Let 'b'))) (Let 'a'))) (Star (Let 'b')))
*Main> lq 's' Empty
Empty
*Main> lq 's' (Let 'a')
Empty
*Main> lq 's' (Let 'c')
Empty
*Main> lq 's' (Union Empty Empty)
Union Empty Empty
*Main> lq 's' (Union Empty ena)
Union Empty (Union (Cat (Cat (Cat (Cat (Union (Cat (Cat Empty (Star (Let 'b'))) (Let 'a')) Empty) (Star (Let 'b')))
(Let 'a')) (Star (Cat (Cat (Cat (Star (Let 'b')) (Let 'a')) (Star (Let 'b'))) (Let 'a')))) 
(Star (Let 'b'))) (Cat Empty (Star (Let 'b'))))
*Main> lq 's' (Union bb1 Empty)
Union (Cat (Cat (Union (Cat (Cat (Union Empty (Cat Empty (Let 'a'))) (Star (Union (Let 'a') (Cat (Let 'b') (Let 'a'))))) (Let 'b')) Empty) (Let 'b')) 
(Star (Union (Let 'a') (Cat (Let 'a') (Let 'b'))))) Empty
*Main> lq 's' (Union bb1 ena)
Union (Cat (Cat (Union (Cat (Cat (Union Empty (Cat Empty (Let 'a'))) (Star (Union (Let 'a') (Cat (Let 'b') (Let 'a'))))) 
(Let 'b')) Empty) (Let 'b')) (Star (Union (Let 'a') (Cat (Let 'a') (Let 'b'))))) 
(Union (Cat (Cat (Cat (Cat (Union (Cat (Cat Empty (Star (Let 'b'))) (Let 'a')) Empty) (Star (Let 'b'))) (Let 'a')) 
(Star (Cat (Cat (Cat (Star (Let 'b')) (Let 'a')) (Star (Let 'b'))) (Let 'a')))) (Star (Let 'b'))) (Cat Empty (Star (Let 'b'))))
*Main> lq 's' (Cat Empty Empty)
Cat Empty Empty
*Main> lq 's' (Cat bb1 Empty)
Cat (Cat (Cat (Union (Cat (Cat (Union Empty (Cat Empty (Let 'a'))) (Star (Union (Let 'a') (Cat (Let 'b') 
(Let 'a'))))) (Let 'b')) Empty) (Let 'b')) (Star (Union (Let 'a') (Cat (Let 'a') (Let 'b'))))) Empty
*Main> lq 's' (Cat ab Empty)
Union (Cat (Cat (Union (Cat Empty (Let 'a')) (Cat Empty (Let 'b'))) (Star (Union (Cat (Let 'a') (Let 'a')) (Cat (Let 'b') (Let 'b'))))) Empty) 
*Main> lq 's' (Cat ab bb1)
Union (Cat (Cat (Union (Cat Empty (Let 'a')) (Cat Empty (Let 'b'))) (Star (Union (Cat (Let 'a') (Let 'a')) (Cat (Let 'b') (Let 'b'))))) 
(Cat (Cat (Cat (Star (Union (Let 'a') (Cat (Let 'b') (Let 'a')))) (Let 'b')) (Let 'b')) (Star (Union (Let 'a') (Cat (Let 'a') (Let 'b'))))))
 (Cat (Cat (Union (Cat (Cat (Union Empty (Cat Empty (Let 'a'))) (Star (Union (Let 'a') (Cat (Let 'b') (Let 'a'))))) (Let 'b')) Empty) 
 (Let 'b')) (Star (Union (Let 'a') (Cat (Let 'a') (Let 'b')))))
*Main> lq 's' (Star Empty)
Cat Empty (Star Empty)
*Main> lq 's' (Star bb1)
Cat (Cat (Cat (Union (Cat (Cat (Union Empty (Cat Empty (Let 'a'))) (Star (Union (Let 'a') (Cat (Let 'b') (Let 'a'))))) (Let 'b')) Empty) (Let 'b')) 
(Star (Union (Let 'a') (Cat (Let 'a') (Let 'b'))))) (Star (Cat (Cat (Cat (Star (Union (Let 'a') (Cat (Let 'b') (Let 'a')))) 
(Let 'b')) (Let 'b')) (Star (Union (Let 'a') (Cat (Let 'a') (Let 'b'))))))
*Main> nep (Empty)
Empty
*Main> nep (Union bb1 ab)
Union (Cat (Cat (Union (Cat (Cat (Union (Let 'a') (Cat (Let 'b') (Let 'a'))) (Star (Union (Let 'a') 
(Cat (Let 'b') (Let 'a'))))) (Let 'b')) (Let 'b')) (Let 'b')) (Star (Union (Let 'a') (Cat (Let 'a') (Let 'b'))))) 
(Cat (Union (Cat (Let 'a') (Let 'a')) (Cat (Let 'b') (Let 'b'))) (Star (Union (Cat (Let 'a') (Let 'a')) (Cat (Let 'b') 
(Let 'b')))))
*Main> nep (Cat Empty Empty)
Cat Empty Empty
*Main> nep (Cat ena Empty)
Union (Cat (Union (Cat (Cat (Cat (Cat (Union (Cat (Cat (Let 'b') (Star (Let 'b'))) 
(Let 'a')) (Let 'a')) (Star (Let 'b'))) (Let 'a')) (Star (Cat (Cat (Cat (Star (Let 'b')) 
(Let 'a')) (Star (Let 'b'))) (Let 'a')))) (Star (Let 'b'))) (Cat (Let 'b') (Star (Let 'b')))) 
Empty) Empty
*Main> nep (Cat ab Empty)
Union (Cat (Cat (Union (Cat (Let 'a') (Let 'a')) (Cat (Let 'b') (Let 'b'))) (Star (Union (Cat (Let 'a') (Let 'a')) 
(Cat (Let 'b') (Let 'b'))))) Empty) Empty
*Main> nep (Cat ab ena)
Union (Cat (Cat (Union (Cat (Let 'a') (Let 'a')) (Cat (Let 'b') (Let 'b'))) (Star (Union (Cat (Let 'a') (Let 'a')) (Cat (Let 'b') (Let 'b'))))) 
(Cat (Star (Cat (Cat (Cat (Star (Let 'b')) (Let 'a')) (Star (Let 'b'))) (Let 'a'))) (Star (Let 'b')))) 
(Union (Cat (Cat (Cat (Cat (Union (Cat (Cat (Let 'b') (Star (Let 'b'))) (Let 'a')) (Let 'a')) (Star (Let 'b'))) (Let 'a')) 
(Star (Cat (Cat (Cat (Star (Let 'b')) (Let 'a')) (Star (Let 'b'))) (Let 'a')))) 
(Star (Let 'b'))) (Cat (Let 'b') (Star (Let 'b'))))
*Main> nep (Star Empty)
Cat Empty (Star Empty)
*Main> nep (Star ena)
Cat (Union (Cat (Cat (Cat (Cat (Union (Cat (Cat (Let 'b') (Star (Let 'b'))) (Let 'a')) (Let 'a')) 
(Star (Let 'b'))) (Let 'a')) (Star (Cat (Cat (Cat (Star (Let 'b')) (Let 'a')) (Star (Let 'b'))) (Let 'a')))) 
(Star (Let 'b'))) (Cat (Let 'b') (Star (Let 'b')))) (Star (Cat (Star (Cat (Cat (Cat (Star (Let 'b')) (Let 'a')) 
(Star (Let 'b'))) (Let 'a'))) (Star (Let 'b'))))
-}

---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes.
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a], [a])]
splits [] = [([], [])]
splits (x:xs) = let ys = splits xs 
                in ([], x:xs) : map f(splits xs) where
                f(xs, ys) = (x:xs, ys)


match1 :: RegExp -> String -> Bool
match1 (Empty) w = False
match1 (Let a) "" = False 
match1 (Let a) (b:w) = a == b && w == []
match1 (Union r1 r2) w = (match1 r1 w) || (match1 r2 w)
match1 (Cat r1 r2) w = or [ (match1 r1 w1) && (match1 r2 w2)
                        | (w1, w2) <- (splits w) ]
match1 (Star r1) w = (w == "") || or [ w1 /= "" && (match1 r1 w1)
                  && (match1 (Star r1) w2) | (w1, w2) <- (splits w) ]


match2 :: RegExp -> String -> Bool
match2 rs w = match2' [rs] w False where
--  match2' :: [RegExp] -> String -> Bool -> Bool
  match2' [] w c = (w=="")
  match2' (Empty:rs) w c = False
  match2' ((Let r):rs) w c = or[ match2' rs w2 False | w0 <- (splits w), w1 <- [fst w0], w1==[r], w2 <- [snd w0] ]
  match2' ((Union r1 r2):rs) w c = (match2' (r1:rs) w c) || (match2' (r2:rs) w c)
  match2' ((Cat r1 r2):rs) w c = (match2' (r1:r2:rs) w c) || ((c==True) && (bypassability(r1)) && (match2' (r2:rs) w True))
  match2' ((Star r):rs) w c = ((c==False) && (match2' rs w False)) || (match2' (r:(Star r):rs) w True)


{- Part 2 Testing
*Main> splits "bcd"
[("","bcd"),("b","cd"),("bc","d"),("bcd","")]
*Main> splits "deftge"
[("","deftge"),("d","eftge"),("de","ftge"),("def","tge"),("deft","ge"),("deftg","e"),("deftge","")]
*Main> splits "bbdetg"
[("","bbdetg"),("b","bdetg"),("bb","detg"),("bbd","etg"),("bbde","tg"),("bbdet","g"),("bbdetg","")]
*Main> splits "abcdefg"
[("","abcdefg"),("a","bcdefg"),("ab","cdefg"),("abc","defg"),("abcd","efg"),("abcde","fg"),("abcdef","g"),("abcdefg","")]
*Main> match1 (ab) "b"
False
*Main> match1 (bb1) "bb"
True
*Main> match1 (ena) "aa"
True
*Main> match1 (ttla) "a"
False
*Main> match1 (ab) "a"
False
*Main> match1 (ab) "b"
False
*Main> match1 (ena) "d"
False
*Main> match1 (ena) "a"
False
*Main> match1 (bb1) "bb"
True
*Main> match1 (ena) "aa"
True
*Main> match1 (ttla) "a"
False
*Main> match1 (Union ena ena) "aa"
True
*Main> match1 (Union ttla ena) "b"
True
*Main> match1 (Union Empty Empty) "a"
False
*Main> match1 (Union ena ena) "aa"
True
*Main> match1 (Union ttla ena) "b"
True
*Main> match1 (Union Empty Empty) "a"
False
*Main> match1 (Cat ena ena) "aa"
True
*Main> match1 (Cat bb1 bb1) "b"
False
*Main> match1 (Star Empty) "a"
False
*Main> match1 (Star ena) "aa"
True
*Main> match2 (ena) "aa"
True
*Main> match2 (ttla) "bb"
False
*Main> match2 (Union ena ena) "aa"
True
*Main> match2 (Union Empty bb1) "bb"
True
*Main> match2 (Union ttla Empty) "aa"
False
*Main> match2 (Cat ab Empty) "aa"
False
*Main> match2 (Cat ena Empty) "bb"
False
*Main> match2 (Star Empty) "a"
False
*Main> match2 (Star bb1) "b"
False
*Main> match2 (Star bb1) "bb"
True
-}

-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get). 

sigma = ['a', 'b']                -- Alphabet used in all examples below

ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once


-- For your tests, you may also find the following helpful. For example,
-- you can generate all strings of length 10 (or 20) or less and then test
-- to see whether match1 r w == memb (lol w) (lang_of r) for each such w.

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]

