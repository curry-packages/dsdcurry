-- Example for a postcondition with a nondeterministic definition:
por True _ = True
por _ True = True
por False False = False

f'post _ (x,y) = por x y

f :: Bool -> (Bool,Bool)
f x = (x,x)

main = f True

-- The checking of the postcondition might result in a nondeterministic
-- evaluation of the main operation.
-- One can avoid this effect by using the transformation option "-e".
-- 
-- In general, the transformation option "-e" requires an advanced
-- (lazy!) implementation of set functions. In PAKCS, this works only for
-- violation detection of the values to be considered are finite
-- and there are only finitely many values.
