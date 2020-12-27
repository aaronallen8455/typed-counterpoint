module Counterpoint

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
noteVal A = 0
noteVal Bb = 1
noteVal B = 2
noteVal C = 3
noteVal Db = 4
noteVal D = 5
noteVal Eb = 6
noteVal E = 7
noteVal F = 8
noteVal Gb = 9
noteVal G = 10
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
combineResult Perfection Perfection = Perfection
combineResult (Failure xs) Perfection = Failure xs
combineResult Perfection (Failure xs) = Failure xs
combineResult (Failure xs) (Failure ys) = Failure $ xs ++ ys
infixl 3 `combineResult`

consonantInterval : List (Note, Note) -> Result
consonantInterval ((a, b) :: xs) =
  if delta a b `elem` [0, 3, 4, 5, 7, 8, 9]
     then Perfection
     else Failure ["Not a consonant interval"]
consonantInterval _ = Perfection

parallel5ths : List (Note, Note) -> Result
parallel5ths ((a2, b2) :: (a1, b1) :: xs) =
  if delta a2 b2 == 7 && delta a1 b1 == 7
     then Failure ["Consecutive perfect 5ths"]
     else Perfection
parallel5ths _ = Perfection

parallelOctaves : List (Note, Note) -> Result
parallelOctaves ((a2, b2) :: (a1, b1) :: xs) =
  if delta a2 b2 == 0 && delta a1 b1 == 0 && a2 /= b2 && a1 /= b1
     then Failure ["Consecutive octaves"]
     else Perfection
parallelOctaves _ = Perfection

allRules : List (Note, Note) -> Result
allRules ns = consonantInterval ns `combineResult` parallel5ths ns
                                   `combineResult` parallelOctaves ns

data CounterPoint : List (Note, Note) -> Result -> Type where
  Start : CounterPoint [] Perfection
  Notes : (a : Note) -> (b : Note) -> CounterPoint ns rs
       -> CounterPoint ((a, b) :: ns) (allRules ((a, b) :: ns) `combineResult` rs)

(:-) : (a : Note) -> (b : Note) -> (CounterPoint ns rs -> CounterPoint ((a, b) :: ns) (allRules ((a, b) :: ns) `combineResult` rs))
(:-) a b = Notes a b
infixl 4 :-

data SomeCounterPoint : Type where
  MkSCP : CounterPoint ns Perfection -> SomeCounterPoint

(>>>) : a -> (a -> b) -> b
(>>>) a f = f a
infixl 3 >>>

shit : SomeCounterPoint
shit = MkSCP $ Start
           >>> A ^ 5 :- E ^ 5
           >>> B ^ 5 :- Gb ^ 5
           >>> B ^ 5 :- C ^ 2
           >>> A ^ 6 :- A ^ 8
           >>> B ^ 6 :- B ^ 7

