{-  To to:
- to add the other analytic functions defined through Taylor series
- to make the Taylor series generate convergent  sequences of intervals
- complete the Duals definitions 

Possible improvements:
- extensively used the class mechanisms
  - make CReal instances of Order, Floating
  - define immediately Intervals, DualIntevals, CReals, Duals,
    paramentric on some basic types
- start with an efficient library representation of the interals

-}

-- {-# LANGUAGE DataKinds #-}
-- {-# LANGUAGE ScopedTypeVariables #-}
-- import Numeric.Rounded
-- import Data.Proxy


module Main
-- module IntervalArithmetic
  where
import Data.Bits
import Math.NumberTheory.Logarithms


--------------------------------------------
-- Partial reals represented as
-- generalized dyadic intervals 
------------------------------------------

data Interval = I !Integer !Integer !Int
  deriving (Eq)
-- (I l g e) represents the interval [l*2^e, (l+g)*2^e]

maxValue = maxBound `div` 2
-- maxValue = 1000

bottomInterval = I (-1) 2 maxValue
isBottom (I _ _ e) = e == maxValue

multExp2 a n = shift a n

toI i = I i 0 0

halfI = I 1 0 (-1)
unitI = I (-1) 2 0

multExp2I (I l g e) n = I l g (e+n)

addI (I l1 g1 e1) (I l2 g2 e2) | e2 < e1   = I (l1 `multExp2` (e1-e2) + l2)
                                               (g1 `multExp2` (e1-e2) + g2) e2
addI (I l1 g1 e1) (I l2 g2 e2) | otherwise = I (l1 + l2 `multExp2` (e2-e1))
                                               (g1 + g2 `multExp2` (e2-e1)) e1
                                             
negI (I l g e) = I (-l-g) g e

multI (I l1 g1 e1) (I l2 g2 e2) =
  let { ll = l1*l2; lg1 = l2*g1; lg2 = l1*g2; gg = lg1 + lg2 + g1*g2 }
  in let minI = 0 `min` lg1 `min` lg2 `min` gg
         maxI = 0 `max` lg1 `max` lg2 `max` gg
     in I (ll + minI) (maxI - minI) (e1+e2)
                           
divIN (I l g e) n =
  let ln = max 0 (maxGBits + integerLog2 n -
                  (if g == 0 then (- maxPrecision) else integerLog2 g))
  in  I  ((l `multExp2` ln) `div` n )
         ((g `multExp2` ln) `div` n +2)
         (e - ln)

-- the maxPrecision used for rational, in future works, 
-- it should be replace by a parameter depending on the level of computation
maxPrecision = 100



divI2 (I l g e) = I l g (e-1)

invI (I l g e) = 
  let den = (l+g)*l
      in if den > 0
         then divIN (I l g e) den
         else error "division by zero"

minI (I l1 g1 e1) (I l2 g2 e2) | e2 <= e1 =
  let l1n = l1 `multExp2` (e1-e2)
      g1n = g1 `multExp2` (e1-e2)
  in if l1n + g1n <= l2
     then (I l1 g1 e1)
     else
       let lb = l1n `min` l2
           ub = (l1n + g1n) `min` (l2 + g2)
       in I lb (ub - lb) e2
                               | otherwise =
  minI (I l2 g2 e2) (I l1 g1 e1)

maxI x y = negI (minI (negI x) (negI y))

meetI (I l1 g1 e1) (I l2 g2 e2) | e2 <= e1 =
  let l1n = l1 `multExp2` (e1-e2)
      g1n = g1 `multExp2` (e1-e2)
      lb = l1n `min` l2
      ub = (l1n + g1n) `max` (l2 + g2)
  in I lb (ub - lb) e2
                                | otherwise =
  meetI (I l2 g2 e2) (I l1 g1 e1)

projI (I l g e) =
  if e < 0
  then
    let lb =  (-(1 `multExp2` (-e))) `max` l `min` (1 `multExp2` (-e))
        in I lb
           (0 `max` (g + l - lb) `min` (1 `multExp2` (-e) - lb))
           e
  else
    let lb =  (-1) `max` (l `multExp2` e) `min` 1
        in I lb
           (0 `max` ((g + l) `multExp2` e - lb) `min` (1 - lb))
           0

-- round an interval to avoid too many almost useless digits

roundI (I l g e) =
  let gExtraBits = integerLog2 (g+1) - maxGBits
  in if gExtraBits > 0 then I (l `multExp2` (- gExtraBits))
                              (g `multExp2` (- gExtraBits) + 2)
                              (e + gExtraBits)
     else (I l g e)

-- a max number of digit to be used for the gap in a normalised form
maxGBits = 24

---------------------------------------------------
-- Partial Duals 
---------------------------------------------------

data DualInterval = !Interval :+& !Interval
  deriving (Eq, Show)

toDI i = toI 1 :+& toI 0

multExp2DI (xa :+& xi) n =  multExp2I xa n :+&  multExp2I xi n

oneDI  = toDI 1
halfDI = oneDI `multExp2DI` 1

unitDI = unitI :+& 0

addDI (xa :+& xi) (ya :+& yi) = (xa + ya) :+& (xi + yi)

negDI (xa :+& xi)  = negI xa :+& negI xi

multDI (xa :+& xi) (ya :+& yi) = multI xa ya :+& addI (multI xa yi) (multI xi ya)

divDIN (xa :+& xi) n = divIN xa n :+& divIN xi n

divDI2 (xa :+& xi)  = multExp2DI (xa :+& xi) (-1)

-----------------
-- the following two definitions need to be completed

invDI (xa :+& xi) = oneDI

maxDI (I m1 g1 e1 :+& xi) (I m2 g2 e2  :+& yi) =
  if (e2 <= e1)
  then
    let m1n = m1 `multExp2` (e1-e2)
        g1n = g1 `multExp2` (e1-e2)
        in if m1n - g1n > m2 + g2
           then (I m1 g1 e1  :+& xi)
           else if  m1n + g1n < m2 - g2
                then (I m2 g2 e2  :+& yi)
                else
                  let ml = (m1n - g1n) `max` (m2 - g2)
                      mu = (m1n + g1n) `max` (m2 + g2)
                      in I ((mu + ml    ) `multExp2` (-1))
                            ((mu - ml + 1) `multExp2` (-1)) e2
                         :+& meetI xi yi 
  else maxDI (I m2 g2 e2  :+& yi) (I m1 g1 e1 :+& xi)


--------------------------------------------------
-- module Reals
--   where
-- import IntervalAritmetic
-------------------------------------------------

newtype CReal = R (Int -> Interval)
unR (R x) = x
-- in the case, but not in the present implementation,
-- one implements  real numbers as Cauchy sequences, r should be such
-- if unR r n = I man gap exp then  2^-n > gap * 2^-exp

embedValue i        = R (\n -> i)
embedUnary  f r     = R (\n -> (roundI (f (unR r n))))
embedBinary f r1 r2 = R (\n -> (roundI (f (unR r1 n) (unR r2 n))))

toR i = embedValue (toI i)
unitR = embedValue unitI
oneR  = toR 1
halrR = embedValue halfI
addR  = embedBinary addI
negR  = embedUnary negI
multR = embedBinary multI
invR  = embedUnary invI
maxR  = embedBinary maxI
minR  = embedBinary minI
projR = embedUnary projI
meetR = embedBinary meetI
roundR = embedUnary roundI

--  divRN r d = R (\n -> divIN (unR r n) d )
divRN r d = embedUnary (\ i -> divIN i d ) r

divR2 = embedUnary divI2

------------------------
-- Class Instances
--------------------

instance Num Interval where
  (+) = addI
  (*) = multI
  a - b = a + negI b
  fromInteger = toI
  abs x = maxI x (-x)
  signum _ = error "No signum!"

instance Num CReal where
  (+) = addR
  (*) = multR
  a - b = a + negR b
  fromInteger = toR
  abs x = maxR x (-x)
  signum _ = error "No signum!"

instance Fractional CReal where
  x / y = x * invR y
  fromRational _ = error "fromRational not yet implemented."

instance Show Interval
  where
--    showsPrec _ (I m g e) st = '(' : shows m ("+-" ++ (shows g (")*2^" ++ (shows e st))))
--    show (I l g e)  = '[' : show l ++ ", " ++ show g ++ ", " ++ show e ++ "]"
    show x = '[' : show lb ++ ", " ++ show (lb + gap) ++ "]"
      where
      I l g e = roundI x 
      lb =  (fromIntegral l) * 2**(fromIntegral e)
      gap = (fromIntegral g) * 2**(fromIntegral e)

instance Show CReal where
  show (R x) = (show (x 0)) ++ (show (x 1)) ++ (show (x 4)) ++ (show (x 16))  ++ (show (x 64)) 


------------------------------
-- Computable Duals
------------------------
newtype CDual = D (Int -> DualInterval)
unD (D x) = x 

embedValueD i = D (\n -> i)
embedUnaryD f r = D (\n -> f (unD r n))
embedBinaryD f r1 r2 = D (\n -> f (unD r1 n) (unD r2 n))

toD i = embedValueD (toDI i)
unitD = embedValueD unitDI
oneD  = toD 1
halfD = embedValueD  halfDI
addD  = embedBinaryD addDI
negD  = embedUnaryD  negDI
multD = embedBinaryD multDI
invD  = embedUnaryD  invDI
maxD  = embedBinaryD maxDI
divDN r d n = divDIN (r n) d 
divD2 = embedUnaryD  divDI2

-------------------------------------------------
-- Functionals: integration, supremum, fixed-point
-------------------------------------------------

integrationR f = R (\n -> integrationAux f (n, n))
  where
    integrationAux f (0, n) = unR (f unitR) n
    integrationAux f (m, n) = divI2 (integrationAux (\x -> f (divR2 x)) (m-1, n)) + divI2 (integrationAux (\x -> f (divR2 (x + 1))) (m-1, n))

supremumR f = R (\n -> supremumAux f (n, n))
  where
    supremumAux f (0, n) = unR (f unitR) n
    supremumAux f (m, n) = supremumAux (\x -> f (divR2 x)) (m-1, n) `maxI` supremumAux (\x -> f (divR2 (x + 1))) (m-1, n)

fastIntegrationR f = R(\n -> addList (map (\i -> unR (f (R (\m -> i))) n) (splitUnitInterval n)) `multExp2I` (-n-2))
  where 
    splitUnitInterval n = [ I i 1 (-n) | i <- [0..2^n-1]]
    addList xs = addListAux xs 0
      where
        addListAux [] acc = acc
        addListAux (x:xs) acc = seq (x + acc) (addListAux xs (x + acc))

-- integrationD f n = integrationAux f (n, n)
--   where
--     integrationAux f (0, n) = f unitD n
--     integrationAux f (m, n) = divDI2 (integrationAux (f . divD2) (m-1, n)) `addDI`
--                               divDI2 (integrationAux (f . divD2 . (addD oneD)) (m-1, n))

-- newHalfD = integrationD id
-- test = integrationD (\x -> maxD x (addD oneD (negD x)))

class FixedPoint a where 
  down       :: a -> a
  fixedPoint :: (a -> a) -> a
  fixedPoint f = f (down (fixedPoint f))

instance FixedPoint CReal where 
  down (R x) = R( downf x)
    where
      downf x 0 = bottomInterval
      downf x n = x (n-1)

instance (FixedPoint a) => FixedPoint (a -> b) where 
   down f x = f (down x)

---------------------------------------------------------
-- Taylor series 
-------------------------------


powerSeries x = powerSeriesAux x 1
  where powerSeriesAux x y = y : powerSeriesAux x (y*x)

factorialSeries = factorialSeriesAux 0 1
  where factorialSeriesAux n nf = nf : factorialSeriesAux (n+1) (nf * (n+1))

seriesFromFunction f = map f [0..]
                                      
taylorSeries f x = zipWith divIN (zipWith (*) (seriesFromFunction f) (powerSeries x)) factorialSeries

addSeries (x:xs) = addSeriesAux x xs where
  addSeriesAux y (x:xs) = y : addSeriesAux (y+x) xs

functionFromFH f h (R r) =  R (\n -> (addSeries (taylorSeries f (r n))) !! n +
                               (h n (meetI 0 (r n)) * ((powerSeries (r n))!! (n+1)) `divIN` (factorialSeries !! (n+1))))


----------
-- Alternative incomplete definition of Taylor series
-------------------------

fact n = product [1 .. n]

power 0 x = 1
power n x = power (n-1) x
                   
taylorI f x = taylorIAux f x 1 0 where   
  taylorIAux f x xn n = (f n * xn) `divIN` fact n :
    taylorIAux f x (x * xn) (n+1)
-- build the Taylor series f(0), ...,  f(n)/n! x^n 

functionFromFGG f g (R r) =  R (\n -> (addSeries (taylorI f (r n))) !! n)
--  +  (g (meetI 0 (r n)) * power n (r n)) `divIN` (fact n))

--------------------------
-- Some analytic functions 
--------------------------

fCos n = case  n `rem` 4 of
           0 -> 1 
           2 -> -1 
           _ -> 0

hCos _ x = x - x

cosR = functionFromFH fCos hCos

-------------
-- some tests
-------------

newHalf = integrationR id
fastNewHalf = fastIntegrationR id

testFunction x = (1 + projR x) / 3
halfFixed = fixedPoint testFunction

one = cosR 0
almostMinusOne = cosR 3

main =
  do
    s <- getLine
    n <- return (read s)
--    print (unR newHalf n)
    print (unR fastNewHalf n)
