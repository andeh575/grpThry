Name:		Andrew Graham

Date:		11 February 2014
Purpose:	An attempt at finding the smallest set of 
		symmetries

> import Data.List
> import Data.Char

> data  Rule 	= Rule [[Char]] [[Char]]	
> 	deriving (Show)

> leftRule 	       :: Rule -> [[Char]]
> leftRule (Rule l r)	= l

> rightRule 	       :: Rule -> [[Char]]
> rightRule (Rule l r) 	= r

> makeRule 	       :: [[Char]] -> [[Char]] -> Rule
> makeRule l r 	 	= Rule l r

> dSix :: [Rule]
> dSix  = [	(Rule ["R","R","R"] [""]),
> 		(Rule ["F","F"]	[""]),
>		(Rule ["R","F","R","F"] [""]),
>		(Rule ["F","R","F","R"] [""]),
>		(Rule ["F'"] ["F"]),
>		(Rule ["R'"] ["R","R"]) ]

> dSixEx :: [Rule]
> dSixEx  = dSix ++ 	[(Rule ["R","F"] ["F","R","R"]),
>			 (Rule ["F","R"] ["R","R","F"]) ]	

> display      :: [[Char]] -> String
> display str 	= filter (/=' ')  $ unwords $ str

----------------------------------------------------------------------------
Worker Functions for Manipulating Data
----------------------------------------------------------------------------

> reduce 	       	       :: [[Char]] -> [Rule] -> [[Char]]
> reduce str rules  		= reduce' str rules 
>	where reduce' xs (r:rs) = 
>		case reduceOnce xs r of
>		Nothing	       -> reduce' (words $ eqRebuild (Just (xs, [""])) [""]) rs 
>		Just (ys)      -> reduce' ys rules
>	      reduce' xs [] 	= xs

> reduceOnce	       :: [[Char]] -> Rule -> Maybe [[Char]]
> reduceOnce xs rule 	= prePost
>	where prePost 	= case splitString xs (leftRule rule) of
>			  	Nothing -> Nothing
>			  	Just (is,js) -> Just (words $ eqRebuild (Just (is,js)) (rightRule rule))

Uses:

	reduce ["a","b","b","b","c"] (Rule ["b","b","b"] ["z"])
		=> "azc"

It is important to note that ["b","b"] is different than
["bb"] - so far as the parsing is concerned, these represent
two unique symmetries.

Extract some specified string, ys, from the overall
string, xs, and return the parts before and after ys - 
we'll use this function to help find equivalences and 
replace them with some rule.

> splitString 	       :: Eq a => [a] -> [a] -> Maybe ([a],[a])
> splitString xs ys	= split xs ys []

> split 	       :: Eq a => [a] -> [a] -> [a] -> Maybe ([a],[a])
> split [] ys ls 	= Nothing
> split (x:xs) ys ls 	= if ys `isPrefixOf` (x:xs)
>			  then Just (reverse ls, drop (length ys) (x:xs))
>			  else split xs ys (x:ls)

Uses:	
	splitString [1..10] [2..5] 
			=> Just ([1],[6,7,8,9,10])

	splitString ["a","b","c"] ["b"] 
			= > Just (["a"],["c"])

The next thing we'll need to be able to do, is replace the
extracted piece with some other equivalence and then put
the entire string back together. So, we began with some
string:

			"pre":"ys":"post"

We ran the splitString function to arrive at:

			("pre","post")

Now we want to replace ys with some equivalence zs and put
the string back together:

			"pre":"zs":"post"

This implementation only works for string input - so we are
forced to use symbolic representation instead of numerical.
This is a limitation on the splitString function which can
work for any type [a]. 

> eqRebuild 		     :: Maybe ([[Char]], [[Char]]) -> [[Char]] -> [Char]
> eqRebuild (Just (xs,ys)) zs = unwords (xs ++ zs ++ ys) 

---------------------------------------------------------------------------
Knuth-Bendix Algorithm 
---------------------------------------------------------------------------

Make these work with Rule [[Char]] [[Char]]

 knuthBendixVar rules = knuthBendix' rules pairs
	where
	    pairs = [((Rule x y),(Rule l r))|(Rule x y)<- rules,(Rule l r)<- rules,(Rule x y)/=(Rule l r)]
	    knuthBendix' rules [] = rules
	    knuthBendix' rules ( ((Rule li ri),(Rule lj rj)) : ps) = 
		  case findOverlap li lj of
		  Nothing 	-> knuthBendix' rules ps
		  Just (a,b,c) 	-> case ordPair (reduce (ri++c) rules) (reduce (a++rj) rules) of
			Nothing    -> knuthBendixVar rules ps
			Just rule' -> let rules' = reduce rule' rules 
					  ps'=ps++[(rule',rule)|rule<-rules']++[(rule,rule')|rule<-rules']
				      in knuthBendix' (rule':rules') ps'
	    reduce rule@(l,r) rules = filter (\(l',r')->not(isInfixOf l l')) rules

 ordPair x y =
	case shortlex x y of
	LT -> Just (y,x)
	EQ -> Nothing
	GT -> Just (x,y)

 shortlex x y = compare (length x, x) (length y, y)

 findOverlap xs ys = findOverlap' [] xs ys 
	where	findOverlap' as [] cs	 = Nothing
		findOverlap' as (b:bs) cs =
			if (b:bs) `isPrefixOf` cs
			then Just (reverse as, b:bs, drop (length (b:bs)) cs)
			else findOverlap' (b:as) bs cs

---------------------------------------------------------------------------
Basic Functions/Properties of Groups
---------------------------------------------------------------------------

In order to begin into geometric group theory, it 
will be necessary to define a basic set of functions that
clearly define the operations that we expect groups to
obey.

Those basic functions/Properties will be:
	1) Identity:		ae    = a 
				ea    = a

	2) Inverse:		aa'   = e = ""
				a'a   = e = ""

	3) Distribution:	(ab)' = b'a'

> identity 	       :: [[Char]]
> identity 		= ["e"]

> applyIdentity        :: [[Char]] -> [[Char]]
> applyIdentity	str	= identity ++ str

> inverse 	       :: [[Char]] -> [[Char]]
> inverse str		= map (++"'") str  

> applyInverse 	       :: [[Char]] -> [[Char]] 
> applyInverse str	= ["("] ++ str ++ [")'"] 

> distInverse 	       :: [[Char]] -> [[Char]]
> distInverse str	= reverse (inverse strip)  
>	where strip  	= filter (/=")'")  $ filter (/="(") str

> exp		       :: [[Char]]->[[Char]]
> exp str		= words $ intersperse ' ' $ unwords str

--------------------------------------------------------------------------
Inverse Tester
--------------------------------------------------------------------------
This function tests to see whether or not two strings, x and y, are
inverses of each other by testing xy' against a set of rules to try and 
find e.

> invTest 	       :: [[Char]] -> [[Char]] -> [Rule] -> [[Char]]
> invTest s1 s2 rules	= reduce subTest rules
>	where subTest	= s1 ++ distInverse (applyInverse (s2))

--------------------------------------------------------------------------
Equivalence Tester
--------------------------------------------------------------------------
This function tests to see whether or not two strings, x and y, are
equivalent to each other by testing x(y)^(order(x)-1) against a set of 
rules and trying to find e.

> eqTest	       :: [[Char]] -> [[Char]] -> [Rule] -> [[Char]]
> eqTest s1 s2 rules	= reduce subTest rules
>	where 	subTest	= s1 ++ s2Pow
>		subStr	= (take ((orderStr s1 rules) - 1) (repeat s2)) 
>	      	s2Pow	= words $ unwords $ map unwords $ subStr

------------------------------------------------------------------------
Order of Elements
------------------------------------------------------------------------
Calculates the order of an element if provided a rule 
that proves it's of finite order:

> orderRule 	       :: Rule -> Int
> orderRule rule	= case rightRule rule of
>		  	  [""] 	-> length $ leftRule rule 
>		  	  xs	-> 0

Attempts to determine if there is a rule that desribes the order of
some string. If true, then provide that order:

> orderStr			  :: [[Char]] -> [Rule] -> Int
> orderStr str rules 		   = orderStr' str rules
>	where orderStr' str (r:rs) = case lRuleMatch str r of
>			  	     False -> (orderStr' str rs)
>			  	     True  -> orderRule r
>	      orderStr' str []	   = 0
			  

Determine whether or not some rule is composed entirely of the given
string. If True then there exists some rule that contains a multiple
of the string -> the string has some finite order.

> lRuleMatch	       :: [[Char]] -> Rule -> Bool
> lRuleMatch str rule 	= lRule == leftRule rule 
>	where 	lRule	= [c|c<-cs, s == c]
>		cs	= leftRule rule
>		s	= unwords str
 
-----------------------------------------------------------------------
Cardinality of G
-----------------------------------------------------------------------
Determines the cardinality, or the number of elements in
a given group:

But how do I guarantee that it is the MINIMUM set? What if
I run the set of rules over itself... ? 



