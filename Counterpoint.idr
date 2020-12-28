module Counterpoint

import Data.Vect

Octave : Type
Octave = Nat

BrokenRule : Type
BrokenRule = String

Note : Type
Note = Nat

data NoteName : Type where
  A  : NoteName
  Bb : NoteName
  B  : NoteName
  C  : NoteName
  Db : NoteName
  D  : NoteName
  Eb : NoteName
  E  : NoteName
  F  : NoteName
  Gb : NoteName
  G  : NoteName
  Ab : NoteName

noteVal : NoteName -> Nat
noteVal A  = 0
noteVal Bb = 1
noteVal B  = 2
noteVal C  = 3
noteVal Db = 4
noteVal D  = 5
noteVal Eb = 6
noteVal E  = 7
noteVal F  = 8
noteVal Gb = 9
noteVal G  = 10
noteVal Ab = 11

(^) : NoteName -> Nat -> Note
(^) n o = noteVal n + 12 * o
infixl 5 ^

delta : Note -> Note -> Int
delta a b = abs (cast a - cast b) `mod` 12

data Result : Type where
  Perfection : Result
  Failure : List BrokenRule -> Result

combineResult : Result -> Result -> Result
combineResult (Failure xs) Perfection = Failure xs
combineResult Perfection (Failure xs) = Failure xs
combineResult (Failure (x::xs)) (Failure ys) =
  case combineResult (Failure xs) (Failure ys) of
       Perfection => Failure [x]
       Failure fs => Failure $ x :: fs
combineResult (Failure []) (Failure ys) = Failure ys
combineResult _ _ = Perfection
infixl 3 `combineResult`

Semigroup Result where
  (<+>) = combineResult

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

allRules : (n : Nat) -> List (Vect n Note) -> Result
allRules n ns = consonantInterval n ns
            <+> parallel5ths n ns
            <+> parallelOctaves n ns

data CounterPoint : (n : Nat) -> List (Vect n Note) -> Result -> Type where
  Start : CounterPoint n [] Perfection
  (:-) :  CounterPoint n ns rs -> (notes : Vect n Note)
       -> CounterPoint n (notes :: ns) (allRules n (notes :: ns) <+> rs)
infixl 4 :-

data SomeCounterPoint : Type where
  MkSCP : CounterPoint n ns Perfection -> SomeCounterPoint

twoVoices : SomeCounterPoint
twoVoices = MkSCP $
           Start
           :- [A ^ 5, E ^ 5]
           :- [B ^ 5, Gb ^ 5]
           :- [B ^ 5, C ^ 2]
           :- [A ^ 6, A ^ 8]
           :- [B ^ 6, B ^ 7]

threeVoices : SomeCounterPoint
threeVoices = MkSCP $
              Start
              :- [C ^ 3 , E ^ 3, G ^ 3]
              :- [A ^ 3 , C ^ 3, F ^ 3]
              :- [Ab ^ 2, C ^ 3, F ^ 3]
              :- [G ^ 2 , C ^ 3, E ^ 3]

