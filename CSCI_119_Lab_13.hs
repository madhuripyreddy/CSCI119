import Data.List (foldl')
import Data.Char (isUpper)

-- CFG G = (Start, Follows, Nullable)
type CFG = (Char, Char -> Char -> [String], Char -> Bool)
                
accept :: CFG -> [Char] -> Bool
accept (s,d,e) = elem [] . foldl' (\xs c -> concatMap (lq c) xs) (close [s]) where  
  close [] = [""]
  close c@(x:xs) |(isUpper x) && (e x == True) = [c] ++ close xs
                 |otherwise = [c]
  lq a [] = []
  lq a (x:xs) | isUpper x = map (++ xs) $ concat $ map (close) (d x a)          -- nonterminal
              | otherwise = if a == x then [xs] else []  -- terminal
  
-- Balanced parentheses (not including the empty string)
-- original: S --> () | (S) | SS
-- in TNF:   S --> () | ()S | (S) | (S)S
  
bp :: CFG
bp = ('S', d, e) where
  d 'S' '(' = ["S)", "S)S"]
  d 'S' ')' = []
  e 'S' = True ;

-- {a^i b^j c^{i+j} | i >= 0, j > 0}
-- original: S --> aSc | T
--           T --> bTc | bc
-- in TNF:   S --> aSc | bTc | bc
--           T --> bTc | bc
  
pl = ('S', d, e) where
  d 'S' 'a' = ["Sc"]  ;  d 'S' 'b' = ["Tc","c"]  ;  d 'S' 'c' = []
  d 'T' 'a' = []      ;  d 'T' 'b' = ["Tc","c"]  ;  d 'T' 'c' = []
  e 'T' = True ;
  
--G5
--G5 - even amount of a’s and b’s
-- original: S --> aSb | bSa | SS | ε
-- in TNF: S --> aaSb | baSa | aaSS | True

g5 :: CFG
g5 = ('S', d, e) where
  d 'S' 'a' = ["bS", "aS", "b", "aSbS", "bSaS"]; d 'S' 'b' = ["bS", "aS", "a", "aSbS", "bSaS"];  
  e 'S' = True ;

--G6 
--G6 - accepts every string except empty
-- original:  S --> bS | Sa | aSb | ε 
-- in TNF: S --> abS | bSa | aSba 

g6 :: CFG
g6 = ('S',d,e) where
   d 'S' 'a' = ["bS", "bSa", "aSba", "a", "b", "aSb", "aS", ""]; d 'S' 'b' = ["bS", "bSa", "aSba", "a", "b", "aSb", "aS", ""];
   e 'S' = True ; 
   
--G2
--original: R -> F | F+R
--          F -> S | FS
--          S -> A | S*
--          A -> 0 | 1 | a1 | .. | an | (R) 
-- in TNF: R -> aaF | aaF+aaR
--         F -> aaS | aaFS
--         S -> aaA | aS*
--         A -> a0 | a1 | aa1

g2 :: CFG
g2 = ('R', d, e) where 
    d 'R' 'a' = ["aF", "bF", "baF", "aaF", "ba", "ab", ""] ; d 'R' 'b' = ["bF", "bR", "ba", "ab", ""] ;
    d 'F' 'a' = ["aS", "bS", ""] ; d 'F' 'b' = ["bFS", "aFS", "baFS", "aaFS", ""]
    d 'S' 'a' = ["aA", "bA", "", "abA", "bbA"] ; d 'S' 'b' = ["bS*", "aS*", "", "a", "b", "ba", "ab"] ;
    d 'A' 'a' = ["", "a", "b", "ba", "ab", "bAa", "aAa"] ;
    e 'R' = True ;
 
--Tests 
{-
*Main> accept bp ")"
False
*Main> accept bp ")"
False
*Main> accept g5 "a"
False
*Main> accept g5 "b"
False
*Main> accept g5 "aa"
False
*Main> accept g5 "ba"
True
*Main> accept g5 "bb"
False
*Main> accept g5 "bab"
False
*Main> accept g5 "aba"
False
*Main> accept g5 "ab"
True
*Main> accept g5 "abba"
True
*Main> accept g5 "bba"
False
*Main> accept g5 "bbb"
False
*Main> accept g5 "bbbb"
False
*Main> accept g5 "bababa"
True
*Main> accept g5 "bbbaaa"
False
*Main> accept g5 "aaaa"
False
*Main> accept g5 "bbbbbaaaaa"
False
*Main> accept g5 "abba"
True
*Main> accept g5 "baab"
True
*Main> accept g6 ""
True
*Main> accept g6 "b"
True
*Main> accept g6 "a"
True
*Main> accept g6 "bb"
True
*Main> accept g6 "ab"
True
*Main> accept g6 "ba"
True
*Main> accept g6 "bb"
True
*Main> accept g6 "baab"
True
*Main> accept g6 "aabab"
True
*Main> accept g6 "abbbbaaa"
True
*Main> accept g6 "aaaa"
True
*Main> accept g2 "aa"
False
*Main> accept g2 "aba"
True
*Main> accept g2 "bba"
True
*Main> accept g2 "baba"
False
*Main> accept g2 "ba"
False
*Main> accept g2 "a"
True
*Main> accept g2 ""
True
*Main> accept g2 "bababab"
False
*Main> accept g2 "bbbbbba"
True
*Main> accept g2 "aaaababababa"
True
*Main> accept g2 "bbab"
False
-}

   
