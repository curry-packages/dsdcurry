nats'spec n = n : nats'spec (n+1)

nats n = n : n+1 : nats (n+2)

-- observation function for postcondtion of nats:
nats'post'observe (x:y:_) = (x,y)

main = take 4 (nats 0)