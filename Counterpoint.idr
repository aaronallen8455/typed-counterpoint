module Counterpoint

import Data.Vect

public export
Octave : Type
Octave = Nat

BrokenRule : Type
BrokenRule = String

Note : Type
Note = Nat

parameters (o : Octave)
  public export
  A : Note
  A = o * 12
  public export
  Bb : Note
  Bb = 1 + o * 12
  public export
  B : Note
  B = 2 + o * 12
  public export
  C : Note
  C = 3 + o * 12
  public export
  Db : Note
  Db = 4 + o * 12
  public export
  D : Note
  D = 5 + o * 12
  public export
  Eb : Note
  Eb = 6 + o * 12
  public export
  E : Note
  E = 7 + o * 12
  public export
  F : Note
  F = 8 + o * 12
  public export
  Gb : Note
  Gb = 9 + o * 12
  public export
  G : Note
  G = 10 + o * 12
  public export
  Ab : Note
  Ab = 11 + o * 12

public export
delta : Note -> Note -> Int
delta a b = (cast a - cast b) `mod` 12

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
consonantIntervals : {n : Nat} -> List (Vect n Note) -> Result
consonantIntervals (xs :: _) = go xs where
  checkInterval : {n : Nat} -> Note -> Vect n Note -> Result
  checkInterval _ [] = Perfection
  checkInterval x (y :: xs) =
    if abs (delta x y) `elem` (the (List Int) [0, 3, 4, 5, 7, 8, 9])
       then checkInterval x xs
       else Failure ["Not a consonant interval"]
  go : {n : Nat} -> Vect n Note -> Result
  go [] = Perfection
  go (x :: xs) = checkInterval x xs <+> go xs
consonantIntervals [] = Perfection
consonantIntervals _ = Perfection

public export
delinquent5ths : {n : Nat} -> List (Vect n Note) -> Result
delinquent5ths ((x::xs) :: (y::ys) :: _) = go x y xs ys
  where
    checkNotes : Note -> Note -> Note -> Note -> Result
    checkNotes x1 y1 x2 y2 =
      if delta x2 x1 == 7
      then if delta y2 y1 == 7
           then Failure ["Consecutive perfect fifths"]
           else if compare x1 x2 == compare y1 y2
                then Failure ["Direct perfect fifth"]
                else Perfection
      else Perfection

    go : {n : Nat} -> Note -> Note -> Vect n Note -> Vect n Note -> Result
    go x1 y1 (x2 :: xs) (y2 :: ys) =
      if x1 == y1 && x2 == y2
         then Perfection
         else checkNotes x1 y1 x2 y2
          <+> go x1 y1 xs ys
          <+> go x2 y2 xs ys
    go _ _ _ _ = Perfection
delinquent5ths _ = Perfection

public export
delinquentOctaves : {n : Nat} -> List (Vect n Note) -> Result
delinquentOctaves ((x::xs) :: (y::ys) :: _) = go x y xs ys
  where
    checkNotes : Note -> Note -> Note -> Note -> Result
    checkNotes x1 y1 x2 y2 =
      if delta x1 x2 == 0
         then if delta y1 y2 == 0
              then if x1 == x2 && y1 == y2
                   then Failure ["Consecutive unisons"]
                   else Failure ["Consecutive octaves"]
              else if compare x1 x2 == compare y1 y2
                   then Failure ["Direct octave"]
                   else Perfection
         else Perfection

    go : {n : Nat} -> Note -> Note -> Vect n Note -> Vect n Note -> Result
    go x1 y1 (x2 :: xs) (y2 :: ys) =
      if x1 == y1 && x2 == y2
         then Perfection
         else checkNotes x1 y1 x2 y2
          <+> go x1 y1 xs ys
          <+> go x2 y2 xs ys
    go _ _ _ _ = Perfection
delinquentOctaves _ = Perfection

public export
voiceCrossing : {n : Nat} -> List (Vect n Note) -> Result
voiceCrossing ((x::xs) :: _) = go x xs where
  go : {n : Nat} -> Note -> Vect n Note -> Result
  go x (y::xs) = if x <= y
                 then go y xs
                 else Failure ["Voice crossing"]
  go _ _ = Perfection
voiceCrossing _ = Perfection

public export
allRules : {n : Nat} -> List (Vect n Note) -> Result
allRules ns = consonantIntervals ns
          <+> delinquent5ths ns
          <+> delinquentOctaves ns
          <+> voiceCrossing ns

public export
data CounterPoint : List (Vect n Note) -> Result -> Type where
  Start : CounterPoint [] Perfection
  (|>) : CounterPoint ns rs -> (notes : Vect n Note)
      -> CounterPoint (notes :: ns) (allRules (notes :: ns) <+> rs)
infixl 4 |>

public export
data SomeCounterPoint : Type where
  MkSCP : CounterPoint ns Perfection -> SomeCounterPoint

