-- CSci 119, Lab 3
-- See http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-List.html
import Data.List (sort, stripPrefix)


---------------- General list functions

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Cartesian product, preserves normalization
cart :: [a] -> [b] -> [(a,b)]
cart xs [] = []
cart [] ys = []
cart x y = [(a,b) | a <- x, b <- y]

-- Powerset, preserves normalization. Examples:
-- power [] = [[]]
-- power [1] = [[],[1]]
-- power [1,2] = [[],[1],[1,2],[2]]
-- power [1,2,3] = [[],[1],[1,2],[1,2,3],[1,3],[2],[2,3],[3]]
power :: [a] -> [[a]]
power [] = [[]]
power [x] = [[], [x]]
power (x:xs) =  []: map(x:) z ++ tail z
    where 
    z = power xs 

  
---------------- Length-ordered lists

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

-- Concatenation of LOLs, preserves invariant
dot :: LOL a -> LOL a -> LOL a
dot (LOL y ys) (LOL z zs) = LOL (y + z) (ys ++ zs)

-- Reverse of LOLs, preserves invariant
rev :: LOL a -> LOL a 
rev (LOL y ys) = LOL y (reverse ys)

---------------- Languages

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is ordered with no duplicates
type Lang a = [LOL a]


-- Constructor for languages
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

-- Merge of langages (aka "union")
merge :: Ord a => Lang a -> Lang a -> Lang a
merge [] ys = ys
merge xs [] = xs 
merge (x:xs) (y:ys)
  | x < y     = x: merge xs (y:ys)
  | x == y    = x: merge xs ys
  | otherwise = y: merge (x:xs) ys

-- Concatenation of languages
cat :: Ord a => Lang a -> Lang a -> Lang a
cat [] zs = []
cat ys [] = []
cat (y:ys) (z:zs) = dot y z : merge (cat ys (z:zs)) (cat [y] zs)

-- Kleene star of languages
kstar :: Ord a => Lang a -> Lang a
kstar [] = [eps]
kstar (LOL 0 []:xr) = kstar xr 
kstar xs = eps : cat xs (kstar xs)

-- Left quotient of a language by an LOL (cf. Definition 2.16)
-- Hint: Use the stripPrefix function

leftq :: Ord a => LOL a -> Lang a -> Lang a
leftq (LOL r ts) [] = lang []
leftq (LOL r ts) (z:zs) 
  | Nothing  == stripPrefix ts q  = leftq (LOL r ts)zs
  | otherwise = lol f: leftq (LOL r ts)zs
  where
    (LOL m q) = z 
    Just f = stripPrefix ts q

---- Regular expressions and the languages they denote 
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


-- The language associated to a regular expression, i.e., [[r]]

lang_of :: RegExp -> Lang Char
lang_of (Empty) = []
lang_of (Let c) = [lol[c]]
lang_of (Cat r1 r2) = cat (lang_of r1) (lang_of r2)
lang_of (Union r1 r2) = merge (lang_of r1) (lang_of r2)
lang_of (Star r1) =  kstar(lang_of r1) 


-- The one-string and finite languages of Theorem 3.2. It should be the case
-- that, for any string w, lang_of (onestr w) == [w], and for any (finite) list
-- of (distinct) strings l, lang_of (finite l) == l.
onestr :: String -> RegExp
onestr [] = Star Empty
onestr xs = if ((length xs)>1) then ((Cat (Let (head xs)) (onestr (tail xs)))) else (Let (head xs))


finite :: [String] -> RegExp
finite l = if ((length l)>1) then ((Union (onestr (head l)) (finite (tail l)))) else (onestr (head l))


-- Test all of the above operations extensively!    
{- 
*Main> norm [[2,3], [2,3,4], [4], [4]]
[[2,3],[2,3,4],[4]]
*Main> norm [[2,3,4], [2,3]]
[[2,3],[2,3,4]]
*Main> cart [5,6] [7,8]
[(5,7),(5,8),(6,7),(6,8)]
*Main> cart [1,5] [6,8]
[(1,6),(1,8),(5,6),(5,8)]
*Main> power []
[[]]
*Main> power [2]
[[],[2]]
*Main> power [2,3]
[[],[2],[2,3],[3]]
*Main> eps
[]
*Main> lol "baab"
"baab"
*Main> lol "bbaabbbe"
"bbaabbbe"
*Main> dot (LOL 2 "aa") (LOL 3 "bab")
"aabab"
*Main> dot (LOL 4 "aaaa") (LOL 5 "bbbbb")
"aaaabbbbb"
*Main> reverse "abb"
"bba"
*Main> reverse "bbbaa"
"aabbb"
*Main> rev $ lol "bba"
"abb"
*Main> rev $ lol "bab"
"bab"
*Main> (LOL 4 "abba") < (LOL 5 "abbab")
True
*Main> (LOL 2 "ab") < (LOL 1 "b")
False
*Main> merge (lang ["ab", "ab"]) (lang ["b", "bb"])
["b","ab","bb"]
*Main> merge (lang ["ba", "bb"]) (lang ["b", "ab"])
["b","ab","ba","bb"]
*Main> cat (lang ["ab", "ab"]) (lang ["b", "bb"])
["abb","abbb"]
*Main> cat (lang ["ba", "ba"]) (lang ["b", "bbb"])
["bab","babbb"]
*Main> take 3 $ kstar (lang ["b", "ab"])
["","b","ab"]
*Main> take 6 $ kstar (lang ["b", "aaa"])
["","b","bb","aaa","bbb","aaab"]
*Main> stripPrefix "bb" "abab"
Nothing
*Main> stripPrefix "ba" "baba"
Just "ba"
*Main> leftq (LOL 2 "aa") (lang ["a", "bb"])
[]
*Main> leftq (LOL 1 "b") (lang ["a", "bb"])
["b"]
*Main> toRE "ba.bc.+"
Union (Cat (Let 'b') (Let 'a')) (Cat (Let 'b') (Let 'c'))
*Main>  lang_of $ toRE "ab.bc.."
["abbc"]
*Main> lang_of $ toRE "ba.bd.."
["babd"]
*Main> onestr "bac"
Cat (Let 'b') (Cat (Let 'a') (Let 'c'))
*Main> onestr "bbc"
Cat (Let 'b') (Cat (Let 'b') (Let 'c'))
*Main> finite ["bab", "d"]
Union (Cat (Let 'b') (Cat (Let 'a') (Let 'b'))) (Let 'd')
*Main> finite ["dac", "b"]
Union (Cat (Let 'd') (Cat (Let 'a') (Let 'c'))) (Let 'b')
-}