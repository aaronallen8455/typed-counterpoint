module MyCompositions

import Data.Vect
import Counterpoint

-- this one has some mistakes...
twoVoices : SomeCounterPoint
twoVoices = MkSCP $
            Start
            |> [A 5, E 5]
            |> [B 5, Gb 5]
            |> [B 5, C 2]
            |> [A 6, A 8]
            |> [B 6, B 7]

-- this one is perfect!
threeVoices : SomeCounterPoint
threeVoices = MkSCP $
              Start
              |> [C 3 , E 3, G 3]
              |> [A 3 , C 3, F 3]
              |> [Ab 2, C 3, F 3]
              |> [G 2 , C 3, E 3]

