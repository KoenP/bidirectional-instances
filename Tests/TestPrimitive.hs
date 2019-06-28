
-- Bool datatype
data Bool = True | False

-- List datatype
data List (a :: *) = Cons a (List a) | Nil

-- Natural numbers
data Nat = Succ Nat | Zero

-- Maybe datatype
data Maybe (a:: *) = Just a | Nothing

-- Eq class
class () => Eq (a :: *) where {
  eq :: a -> a -> Bool
}

-- Ord class
class (Eq a) => Ord (a :: *) where {
  lessOrEqualThan :: a -> a -> Bool
}

-- Functor class
class () => Functor (f :: * -> *) where {
  fmap :: forall (a :: *). forall (b :: *). (a -> b) -> f a -> f b
}

-- Eq instance for Bool
instance () => Eq Bool where {
  eq = \a. \b. case a of
                 { True  -> case b of
                              { True  -> True
                              ; False -> False }
                 ; False -> case b of
                              { True  -> False
                              ; False -> True }
                 }
}

-- Eq instance for natural numbers
instance () => Eq Nat where {
  eq = \a. \b. case a of
                 { Zero  -> case b of
                              { Zero  -> True
                              ; Succ b' -> False }
                 ; Succ a' -> case b of
                              { Zero  -> False
                              ; Succ b' -> eq a' b' }
                 }
}

-- Ord instance for natural numbers
instance () => Ord Nat where {
  lessOrEqualThan = \a. \b. case a of
                 { Zero  -> case b of
                              { Zero  -> True
                              ; Succ b' -> True }
                 ; Succ a' -> case b of
                              { Zero  -> False
                              ; Succ b' -> lessOrEqualThan a' b' }
                 }
}

-- Eq instance for lists
instance (Eq a) => Eq (List (a :: *)) where {
  eq = \a. \b. case a of {
    Nil -> case b of {
      Nil -> True;
      Cons qsdf asdf -> False
    };
    Cons a' as -> case b of {
      Nil -> False;
      Cons b' bs -> case eq a' b' of {
        False -> False;
        True -> eq as bs
      }
    }
  }
}

-- Functor instance for lists
instance () => Functor List where {
  fmap = \f. \l. case l of {
    Nil -> Nil;
    Cons x xs -> Cons (f x) (fmap f xs)
  }
}

-- Main program (top-level expression)
let {id = \x. x } in
\a. \b . eq (fmap id a) b
