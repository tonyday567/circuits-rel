{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Cellular oracles: the five checks of the cellular arc
-- (loom/cellular.md), certifying "Circuit.Cellular" against paper 197
-- section 7.  Every check is exhaustive over a finite instance and
-- names the counterexample its named mutation would produce.
--
-- Instance choice is part of the honesty: the group machinery is
-- general, but on abelian instances (Z, Z/n) the multiplication-order
-- hazard of paper Lemma 7.1 is invisible (cd = dc).  Check 1 therefore
-- spends S_3, where F_2[S_3] is noncommutative and the swap mutation
-- has counterexamples.  Checks 3 and 4 are torus laws; their haddocks
-- say what is vacuous there and where the live content is.
module Axioma.Cellular
  ( cellularTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Cellular
import Circuit.Rel (FinObj, FinRel (..), compFinRel)
import Control.Monad (when)
import Data.Bits (testBit)
import Data.List (nub, sort, transpose)
import GHC.TypeNats (KnownNat)

-- | Run all five checks.
cellularTopic :: Verbosity -> IO [Bool]
cellularTopic verbosity = do
  when (verbosity == Axioms) $
    putStrLn "Cellular oracles: homomorphism, centrality, idempotent image, projection, corpus"
  sequence
    [ checkV verbosity "check 1: T_c . T_d = T_{cd} and T_1 = id, exhaustively on F_2[Z/3] and F_2[S_3]" checkHomomorphism,
      checkV verbosity "check 1 mutation: cd /= dc on S_3 and the swapped law T_c . T_d = T_{dc} fails" checkHomomorphismSwapFails,
      checkV verbosity "check 2: centrality, torus-exhaustive over table and linear CA" checkCentrality,
      checkV verbosity "check 2 mutation: the off-by-one wraparound shift breaks centrality somewhere" checkCentralityOffByOneFails,
      checkV verbosity "check 3: im(T_e) = fix(T_e) for e = 1+t+t^2, FinRel equality vs brute enumeration" checkIdempotentImage,
      checkV verbosity "check 4: ab = 1 forces ba = 1 on the torus ring (direct finiteness, exact)" checkDirectFinite,
      checkV verbosity "check 4: projection law T_{ba}^2 = T_{ba} via FinRel composition, with controls" checkProjection
    ]

-- * check 1: the homomorphism law

-- | Every pair (c, d) of the 8-element algebra F_2[Z/3], composed on
-- every one of the 8 torus configurations: T_c ∘ T_d = T_{cd}
-- (paper Lemma 7.1, eq. 7.2), plus T_1 = id.
checkHomomorphism :: Bool
checkHomomorphism =
  homAt (torsElems @3) (torusConfigs @3) (torusSites @3)
    && checkHomomorphismS3

-- | The nonabelian corner: every pair of the 64-element algebra
-- F_2[S_3] on all 64 configurations.  S_3 is where the paper's "the
-- product is cd, not dc" is live machinery rather than a convention
-- note.
checkHomomorphismS3 :: Bool
checkHomomorphismS3 = homAt s3Elems s3Configs allPerms3

-- | One homomorphism sweep, generic in the finite group: elements from
-- the powerset of the group, configurations as subsets, comparison at
-- every group element.
homAt :: (Group g) => [LinCA g] -> [Config g Bool] -> [g] -> Bool
homAt elems configs sites =
  and
    [ convolve c (convolve d x) p == convolve (lmul c d) x p
    | c <- elems,
      d <- elems,
      x <- configs,
      p <- sites
    ]
    && and [convolve lone x p == x p | x <- configs, p <- sites]

-- | The named mutation must have teeth: with s = (1 2) and t the
-- 3-cycle, st ≠ ts in S_3, and there is a configuration where
-- T_c ∘ T_d ≠ T_{dc} — so a 'lmul' with swapped order goes red.  The
-- witness pair is found by search; if the search comes up empty the
-- mutation would be silent and the check fails.
checkHomomorphismSwapFails :: Bool
checkHomomorphismSwapFails =
  case [ (c, d, x, p)
       | c <- two,
         d <- two,
         c /= d,
         lmul c d /= lmul d c,
         x <- s3Configs,
         p <- allPerms3,
         convolve c (convolve d x) p /= convolve (lmul d c) x p
       ] of
    [] -> False
    _ -> True
  where
    two = [linCA [perm3 (0, 2, 1)], linCA [perm3 (1, 2, 0)]]

-- * check 2: centrality

-- | τ ∘ shift_h = shift_h ∘ τ, exhaustively: the table CA rule 30 and
-- the linear CA 1 + t^2 on Z/5 (all 32 configurations, all 5 shifts),
-- and rule 30 on S_3 (all 64 configurations, all 6 shifts) — the
-- nonlinear table rules catch a centrality that only holds for
-- convolution-shaped maps.
checkCentrality :: Bool
checkCentrality =
  centAt (runCA rule30Z5) (torusConfigs @5) (torusSites @5)
    && centAt linZ5 (torusConfigs @5) (torusSites @5)
    && centAt (runCA rule30S3) s3Configs allPerms3
  where
    rule30Z5 = elemRuleCA @5 30
    linZ5 = convolve (linCA [mkMod 0, mkMod 2])
    rule30S3 = elemRuleCAS3 30

-- | The off-by-one wraparound mutation: a shift that reduces the site
-- index mod n-1 instead of mod n is no longer a group action, and
-- centrality must break.  If it did not break anywhere, the centrality
-- check above would be polite to a broken shift.
checkCentralityOffByOneFails :: Bool
checkCentralityOffByOneFails =
  not
    ( and
        [ runCA rule30off (shiftOff h x) p == shiftOff h (runCA rule30off x) p
        | x <- torusConfigs @5,
          h <- [0 .. 4],
          p <- torusSites @5
        ]
    )
  where
    rule30off = elemRuleCA @5 30
    shiftOff h x (Mod i) = x (Mod ((i + h) `mod` 4))

-- | One centrality sweep at a CA given as a configuration map.
centAt :: (Group g) => (Config g Bool -> Config g Bool) -> [Config g Bool] -> [g] -> Bool
centAt tau configs sites =
  and
    [ tau (shift h x) p == shift h (tau x) p
    | h <- sites,
      x <- configs,
      p <- sites
    ]

-- * check 3: the idempotent image characterization

-- | For e = 1 + t + t^2 in F_2[Z/3] (nontrivial idempotent: the ring
-- is F_2 x GF(4) and e picks the second factor), im(T_e) = fix(T_e) —
-- the torus instance of paper Proposition 7.2's image characterization,
-- which on a finite ring cannot come from a one-sided inverse (check 4
-- shows why: ba = 1 always).  Two independent mechanisms:
--
--   (a) FinRel: both subspaces of F_2^3 are encoded as FinRel relations
--       from the unit object and compared by 'Circuit.Rel's canonical
--       rref equality — the extracted module is the comparison oracle.
--   (b) brute enumeration: images and fixed points computed config by
--       config.
--
-- Both must agree, and both must land on the nondegenerate answer
-- span(1,1,1): a rank-1 projection, neither zero nor the identity —
-- that is the reasoning from the hint, verified rather than trusted.
checkIdempotentImage :: Bool
checkIdempotentImage =
  finRelAgrees && enumAgrees && nontrivial && ringIdem && negativeControl
  where
    e = linCA [mkMod 0, mkMod 1, mkMod 2] :: LinCA (Mod 3)
    m = matrixOf e
    imBasis = rrefRows (transpose m)
    fixBasis = nullspaceGF2 3 (plusI m)
    ones = [True, True, True]
    finRelAgrees = subRel imBasis == subRel fixBasis
    enumAgrees = imageSet == fixSet
    nontrivial = imageSet == sort [[ones, replicate 3 False] !! 0, replicate 3 False]
    ringIdem = lmul e e == e
    negativeControl =
      let c = linCA [mkMod 0, mkMod 1] :: LinCA (Mod 3)
          mc = matrixOf c
       in subRel (rrefRows (transpose mc)) /= subRel (nullspaceGF2 3 (plusI mc))
    imageSet =
      sort
        . nub
        $ [ configVec (convolve e x)
          | v <- allConfigs @3 [False, True],
            let x = vecConfig v :: Config (Mod 3) Bool
          ]
    fixSet =
      sort
        [ v
        | v <- allConfigs @3 [False, True],
          let x = vecConfig v :: Config (Mod 3) Bool,
          all (\p -> convolve e x p == x p) (torusSites @3)
        ]

-- * check 4: the projection law on tori

-- | Direct finiteness, exact and exhaustive: for every a, b in
-- F_2[Z/3] with ab = 1, also ba = 1.  Finite rings are directly
-- finite, so on tori the paper's ba ≠ 1 escape (and the whole of
-- Proposition 7.2's nonsurjectivity conclusion) is vacuous — the
-- honest content here is the multiplication machinery: 'lmul' must
-- produce genuine units with two-sided inverses.
checkDirectFinite :: Bool
checkDirectFinite =
  not (null unitPairs)
    && all (\(a, b) -> lmul b a == lone) unitPairs
  where
    elems = torsElems @3
    unitPairs = [(a, b) | a <- elems, b <- elems, lmul a b == lone]

-- | The flagship law in its honest torus home.  For every unit pair
-- (a, b), T_{ba} is a projection — T_{ba} ∘ T_{ba} = T_{ba} — checked
-- by composing the FinRel rendering of the maps with
-- 'Circuit.Rel.compFinRel', against the ring product.  Because ba = 1
-- on tori (check 4's direct finiteness), the clause is exact but
-- shallow; the non-vacuous clause is the idempotent: T_e ∘ T_e = T_e
-- through the same FinRel-composition mechanism, with the negative
-- control T_c ∘ T_c ≠ T_c for c = 1 + t.  The named mutation for this
-- check — swapping the multiplication order — cannot go red on any
-- finite instance (ab = ba = 1 for units); the teeth live in check 1's
-- S_3 corner and in the controls here.
checkProjection :: Bool
checkProjection =
  and [compFinRel (fin ba) (fin ba) == fin ba | ba <- unitBas]
    && compFinRel (fin e) (fin e) == fin e
    && compFinRel (fin c) (fin c) /= fin c
    && and [compFinRel (fin c') (fin d') == fin (lmul c' d') | c' <- torsElems @3, d' <- torsElems @3]
  where
    unitBas =
      [ lmul b a
      | a <- torsElems @3,
        b <- torsElems @3,
        lmul a b == lone
      ]
    e = linCA [mkMod 0, mkMod 1, mkMod 2] :: LinCA (Mod 3)
    c = linCA [mkMod 0, mkMod 1] :: LinCA (Mod 3)
    fin = linToFinRel @3

-- * shared enumeration helpers

-- | Every element of F_2[G] for a finite group listing: all subsets of
-- the support, char-2.
groupElems :: (Group g) => [g] -> [LinCA g]
groupElems gs = map linCA (powerset gs)

torsElems :: forall n. (KnownNat n) => [LinCA (Mod n)]
torsElems = groupElems (torusSites @n)

torusSites :: forall n. (KnownNat n) => [Mod n]
torusSites = [mkMod i | i <- [0 .. nOfMod @n - 1]]

torusConfigs :: forall n. (KnownNat n) => [Config (Mod n) Bool]
torusConfigs = [vecConfig v | v <- allConfigs @n [False, True]]

s3Elems :: [LinCA Perm3]
s3Elems = groupElems allPerms3

s3Configs :: [Config Perm3 Bool]
s3Configs = [\g -> g `elem` sub | sub <- powerset allPerms3]

powerset :: [a] -> [[a]]
powerset = foldr (\x acc -> acc ++ map (x :) acc) [[]]

-- | Elementary CA rule r on the n-torus as a table CA, neighborhood
-- {-1, 0, 1} in left-center-right order.
elemRuleCA :: forall n. (KnownNat n) => Int -> CA (Mod n) Bool
elemRuleCA r =
  CA
    [mkMod (-1), mkMod 0, mkMod 1]
    (\case [l, c, c'] -> tab l c c'; _ -> error "window")
  where
    tab l c c' = testBit r (4 * bit l + 2 * bit c + bit c')
      where
        bit b = if b then 1 else 0

-- | The same table on S_3 along a chosen 3-element memory: the
-- transposition s = (1 2) and the 3-cycle t generate; read the window
-- at (1, s, t).  Centrality holds for any memory — that is the point
-- of the check — and S_3 makes the shifts noncommuting.
elemRuleCAS3 :: Int -> CA Perm3 Bool
elemRuleCAS3 r =
  CA
    [gid, perm3 (0, 2, 1), perm3 (1, 2, 0)]
    (\case [l, c, c'] -> tab l c c'; _ -> error "window")
  where
    tab l c c' = testBit r (4 * bit l + 2 * bit c + bit c')
      where
        bit b = if b then 1 else 0

-- | Encode a subspace of F_2^3 (basis rows) as a FinRel from the unit
-- object, so 'Circuit.Rel's canonical rref equality decides subspace
-- equality.
subRel :: [[Bool]] -> FinRel () (FinObj 3)
subRel rows = FinRel 0 3 rows

-- | The FinRel rendering of a linear CA on the 3-torus: row space of
-- [I | M], the graph relation of the map.
linToFinRel :: forall n. (KnownNat n) => LinCA (Mod n) -> FinRel (FinObj n) (FinObj n)
linToFinRel c = FinRel n n [unit i ++ row | (i, row) <- zip [0 ..] (matrixOf c)]
  where
    n = nOfMod @n
    unit i = [j == i | j <- [0 .. n - 1]]

-- | M + I over F_2.
plusI :: [[Bool]] -> [[Bool]]
plusI m = [zipWith (/=) row [j == i | j <- [0 .. n - 1]] | (i, row) <- zip [0 ..] m]
  where
    n = length m
