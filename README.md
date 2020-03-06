# lCirc

A Stochastic Monad over the generators and relations of morphisms in LCirc, 
the category of circuit morphisms and measurement objects, constructed by cospans of labelled graphs.


# Semantic Function
  -- 
> blackbox ::  
  Ok3 (:--) i v o,
  AffineLagrangian s
  =>((), i) :-- (e, v) :- ((), o) -> s
