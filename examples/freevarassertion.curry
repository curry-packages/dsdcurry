-- Example for an assertion that might instantiates program arguments
-- if evaluated in a strict manner.

f'pre True = True
f'pre False = False

f :: Bool -> Bool
f x = x

main = f x where x free

-- If we evaluate this assertion strictly, it instantiates the free
-- variable and reports a violation. Nothing is reported if it is
-- lazily checked.
