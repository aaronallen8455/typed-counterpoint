module Counterpoint

import Data.Vect

public export
Octave : Type
Octave = Nat

BrokenRule : Type
BrokenRule = String

Note : Type
Note = Nat

public export
A : Octave -> Note
A  o = o * 12
public export
Bb : Octave -> Note
Bb o = 1 + o * 12
public export
B : Octave -> Note
B  o = 2 + o * 12
public export
C : Octave -> Note
C  o = 3 + o * 12
public export
Db : Octave -> Note
Db o = 4 + o * 12
public export
D : Octave -> Note
D  o = 5 + o * 12
public export
Eb : Octave -> Note
Eb o = 6 + o * 12
public export
E : Octave -> Note
E  o = 7 + o * 12
public export
F : Octave -> Note
F  o = 8 + o * 12
public export
Gb : Octave -> Note
Gb o = 9 + o * 12
public export
G : Octave -> Note
G  o = 10 + o * 12
public export
Ab : Octave -> Note
Ab o = 11 + o * 12

public export
delta : Note -> Note -> Int
delta a b = abs (cast a - cast b) `mod` 12

data Result : Type where
  Perfection : Result
  Failure : List BrokenRule -> Result

public export
combineResult : Result -> Result -> Result
combineResult (Failure xs) Perfection = Failure xs
combineResult Perfection (Failure xs) = Failure xs
combineResult (Failure (x::xs)) (Failure ys) =
  case combineResult (Failure xs) (Failure ys) of
       Perfection => Failure [x]
       Failure fs => Failure $ x :: fs
combineResult (Failure []) (Failure ys) = Failure ys
combineResult _ _ = Perfection

Semigroup Result where
  (<+>) = combineResult

public export
consonantInterval : (n : Nat) -> List (Vect n Note) -> Result
consonantInterval (S n) (xs :: _) = go (S n) xs where
  checkInterval : (n : Nat) -> Note -> Vect n Note -> Result
  checkInterval 0 _ [] = Perfection
  checkInterval (S n) x (y :: xs) =
    if delta x y `elem` (the (List Int) [0, 3, 4, 5, 7, 8, 9])
       then checkInterval n x xs
       else Failure ["Not a consonant interval"]
  go : (n : Nat) -> Vect n Note -> Result
  go 0 [] = Perfection
  go (S n) (x :: xs) = checkInterval n x xs <+> go n xs
consonantInterval _ [] = Perfection
consonantInterval 0 _ = Perfection

public export
parallel5ths : (n : Nat) -> List (Vect n Note) -> Result
parallel5ths (S n) ((x::xs) :: (y::ys) :: _) = go n x y xs ys
  where
    checkNotes : Note -> Note -> Note -> Note -> Result
    checkNotes x1 y1 x2 y2 =
      if delta x1 x2 == 7 && delta y1 y2 == 7
         then Failure ["Consecutive perfect fifths"]
         else Perfection

    go : (n : Nat) -> Note -> Note -> Vect n Note -> Vect n Note -> Result
    go (S n) x1 y1 (x2 :: xs) (y2 :: ys) =
      checkNotes x1 y1 x2 y2
        <+> go n x1 y1 xs ys
        <+> go n x2 y2 xs ys
    go _ _ _ _ _ = Perfection
parallel5ths _ _ = Perfection

public export
parallelOctaves : (n : Nat) -> List (Vect n Note) -> Result
parallelOctaves (S n) ((x::xs) :: (y::ys) :: _) = go n x y xs ys
  where
    checkNotes : Note -> Note -> Note -> Note -> Result
    checkNotes x1 y1 x2 y2 =
      if delta x1 x2 == 0 && delta y1 y2 == 0
         then if x1 == x2 && y1 == y2
              then Failure ["Consecutive unisons"]
              else if x1 == x2 || y1 == y2
                   then Perfection
                   else Failure ["Consecutive octaves"]
         else Perfection

    go : (n : Nat) -> Note -> Note -> Vect n Note -> Vect n Note -> Result
    go (S n) x1 y1 (x2 :: xs) (y2 :: ys) =
      checkNotes x1 y1 x2 y2
        <+> go n x1 y1 xs ys
        <+> go n x2 y2 xs ys
    go _ _ _ _ _ = Perfection
parallelOctaves _ _ = Perfection

public export
allRules : (n : Nat) -> List (Vect n Note) -> Result
allRules n ns = consonantInterval n ns
            <+> parallel5ths n ns
            <+> parallelOctaves n ns

public export
data CounterPoint : (n : Nat) -> List (Vect n Note) -> Result -> Type where
  Start : CounterPoint n [] Perfection
  (|>) : CounterPoint n ns rs -> (notes : Vect n Note)
      -> CounterPoint n (notes :: ns) (allRules n (notes :: ns) <+> rs)
infixl 4 |>

public export
data SomeCounterPoint : Type where
  MkSCP : CounterPoint n ns Perfection -> SomeCounterPoint

