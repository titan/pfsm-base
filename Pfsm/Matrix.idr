module Pfsm.Matrix

import Data.Vect

public export
data Matrix : (r: Nat) -> (c: Nat) -> (a: Type) -> Type where
  MkMatrix : Vect r (Vect c a) -> Matrix r c a

export
create : (r: Nat) -> (c: Nat) -> a -> Matrix r c a
create r c d = MkMatrix (replicate r (replicate c d))

export
replaceAt : Fin r -> Fin c -> a -> Matrix r c a -> Matrix r c a 
replaceAt FZ     finc d (MkMatrix (x :: xs)) = MkMatrix ((replaceAt finc d x) :: xs)
replaceAt (FS k) finc d (MkMatrix (x :: xs)) = case replaceAt k finc d (MkMatrix xs) of
                                                  MkMatrix xs' => MkMatrix (x :: xs')
