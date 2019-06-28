
-- Booleans
data Bool = True | False

-- Lists
data List (a :: *) = Cons a (List a) | Nil

-- Equality class
class () => Eq (a :: *) where { eq :: a -> a -> Bool }

-- Eq instance for Bool
instance () => Eq Bool where {
  eq = \x. \y. case x of
               { True  -> case y of
                          { True  -> True
                          ; False -> False }
               ; False -> case y of
                          { True  -> False
                          ; False -> True }
               }
}

-- Logical "and" function
let and = \x. \y. case x of
                  { True  -> y
                  ; False -> False }

-- Eq instance for Lists
instance (Eq a) => Eq (List (a :: *)) where {
  eq = \xss. \yss. case xss of
                   { Cons x xs -> case yss of
                                  { Cons y ys -> and (eq x y) (eq xs ys)
                                  ; Nil       -> False }
                   ; Nil       -> case yss of
                                  { Cons y ys -> False
                                  ; Nil       -> True }
                   }
}

-- Version 1: Simple, Explicitly annotated
let cmp1 :: forall (a :: *). Eq a => a -> a -> Bool
         = \x. \y. eq x y

-- Version 2: Simple, no type-annotation
let cmp2 = \x. \y. eq x y

-- Version 3: Needs bidirectional instances
let cmp3 :: forall (a :: *). Eq (List a) => a -> a -> Bool
         = \x. \y. eq x y

-- Program / a top-level expression
\a. eq a a
