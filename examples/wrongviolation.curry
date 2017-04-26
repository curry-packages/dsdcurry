-- This examples shows that lazy assertion checking might miss
-- a violation of a precondition:

f'pre (x,y) = x>y && y>0

f'post (_,_) r = r>0

f :: (Int,Int) -> Int
f (x,_) = x

main = f (0,id 0) --> strict: precondition, lazy: postcondition violated!
