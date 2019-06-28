
-- Booleans
data Bool = True | False

-- Lists
data List (a :: *) = Cons a (List a) | Nil

class () => D (a :: *) where {
  fd :: a -> a
}

class (D a) => A (a :: *) where {
  fa :: a -> a
}

class () => B (a :: *) where {
  fb :: a -> a
}

class (A a, B a) => C (a :: *) where {
  fc :: a -> a
}

class () => E (a :: *) where {
  fe :: a -> a
}

instance () => E Bool where {
  fe = \a. a
}

instance () => D Bool where {
  fd = \a. a
}

instance () => A Bool where {
  fa = \a. (fd a)
}

instance () => B Bool where {
  fb = \a. a
}

instance () => C Bool where {
  fc = \a. (fd (fb ( fa a )))
}

instance (D a) => D (List (a :: *)) where {
  fd = \l. case l of
           { Nil       -> Nil
           ; Cons x ls -> Cons (fd x) (fd ls) }
}

instance (A a) => A (List (a :: *)) where {
  fa = \l. case l of
           { Nil       -> Nil
           ; Cons x ls -> Cons (fa x) (fa ls) }
}

\a. fc (fb a)
