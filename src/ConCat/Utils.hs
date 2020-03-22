{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module ConCat.Utils where

import GHC.TypeLits ()

import ConCat.Misc ((:*))
import ConCat.AltCat (id, (:**:)(..),Ok2,U2,toCcc)
import ConCat.Orphans ()
import ConCat.Rebox ()
import ConCat.ADFun (andDerF)
import ConCat.RAD (andDerR, andGradR)
import ConCat.Circuit (GenBuses,(:>))
import ConCat.Syntactic (Syn,render)
import ConCat.RunCircuit (run)


import Prelude hiding ((.), id)
type EC = Syn :**: (:>)

type GO a b = (GenBuses a, Ok2 (:>) a b)

runSyn :: Syn a b -> IO ()
runSyn syn = putStrLn ('\n' : render syn)
{-# INLINE runSyn #-}

runSynCirc :: GO a b => String -> EC a b -> IO ()
runSynCirc nm (syn :**: circ) = runSyn syn >> runCirc nm circ
{-# INLINE runSynCirc #-}

runCirc :: GO a b => String -> (a :> b) -> IO ()
runCirc nm circ = run nm [] circ
{-# INLINE runCirc #-}

runSynCircDers :: (GO a b, Num b) => String -> (a -> b) -> IO ()
runSynCircDers nm f =
  do runSynCirc nm               $ toCcc $ id       $ f
     runSynCirc (nm ++ "-adf")   $ toCcc $ andDerF  $ f
     runSynCirc (nm ++ "-adr")   $ toCcc $ andDerR  $ f
     runSynCirc (nm ++ "-gradr") $ toCcc $ andGradR $ f
{-# INLINE runSynCircDers #-}
