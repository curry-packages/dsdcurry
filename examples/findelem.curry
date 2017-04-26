{-

The problem is to tell whether an element is in a set.
The specification represents the set as a list.
An efficient implementation represents the set as
a binary search tree.

-}

find'spec :: Int -> [Int] -> Bool
find'spec x s = elem x s

elem x (y:ys) = x == y || elem x ys
elem _ []     = False

{-
Applying our transformation tool, we obtain an executable
definition of the function find.

In order to obtain a more efficient search method,
we implement sets as binary ordered trees.
-}

data Tree = Leaf | Branch Int Tree Tree

-- We define a search function on binary ordered trees:
findT :: Int -> Tree -> Bool
findT _ Leaf = False
findT x (Branch y l r) 
   | x < y = findT x l
   | x > y = findT x r
   | otherwise = True

-- To use the specification of our initial find operation,
-- we have to specify the semantics of binary ordered trees
-- by mapping them into lists:
semT :: Tree -> [Int]
semT Leaf = []
semT (Branch x l r) = semT l ++ [x] ++ semT r

-- Now we define a specification of our tree search operations
-- by mapping the result into the specification of the initial find:

findT'spec x s = find'spec x (semT s)

--> Example:
--> findT 3 (Branch 2 Leaf (Branch 3 Leaf Leaf))

--> If the tree has a wrong structure, the postcondition fails:
--> findT 3 (Branch 4 Leaf (Branch 3 Leaf Leaf))

--------------------------------------------------------------------------
-- Now can also define an insert operation by providing a postcondition
-- as a weak specification:
insert'post :: Int -> [Int] -> [Int] -> Bool
insert'post x s xs | permute (if elem x s then s else x:s) =:= xs = True
 where
  permute []     = []
  permute (y:ys) = ndinsert y (permute ys)

  ndinsert z ys     = z:ys
  ndinsert z (y:ys) = y : ndinsert z ys

-- Run the transformation tool and obtain an implementation of insert.
-- However, this returns all permutations of the list (unless one uses
-- the option "-pcs").
-- Therefore, we implement a deterministic insert on trees (without balancing):
insertT x Leaf = Branch x Leaf Leaf
insertT x (Branch y l r) 
   | x < y = Branch y (insertT x l) r
   | x > y = Branch y l (insertT x r)
   | otherwise = Branch y l r

-- ...and define its postcondition by mapping trees to lists:
insertT'post x s xs = insert'post x (semT s) (semT xs)

--> Examples:
--> insertT 1 (insertT 4 (Branch 2 Leaf (Branch 3 Leaf Leaf)))
--> findT 5 (foldr insertT Leaf [3,1,5,4,2])
