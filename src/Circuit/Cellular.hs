{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Cellular automata over groups: the shift-central-map encoding of
-- paper 197 (Sept 2026) section 7, in the circuits idiom.
--
-- A configuration is a map from the group to a finite alphabet
-- ('Config' g a = g -> a).  A cellular automaton is a finite memory
-- M ⊂ G plus a local rule reading the window @(x(gu))_{u ∈ M}@ at every
-- site g — the right-neighbor convention of the paper, which fixes the
-- convolution product as cd, not dc (paper Lemma 7.1's warning).  A
-- linear CA is a finite-support element of the group algebra acting by
-- convolution: @(T_c x)(g) = Σ_u c_u · x(gu)@, where coefficients live
-- in F_2 (so a 'LinCA' is just its support: an xor-closed list of group
-- elements).
--
-- The group machinery is written generally ('Group' g) and instantiated
-- at the additive group 'Integer' (the full shift on Z), the cyclic
-- groups 'Mod' n (tori, where enumeration is exact), and the symmetric
-- group 'Perm3' = S_3 (the nonabelian corner: F_2[S_3] has cd ≠ dc, so
-- the multiplication-order hazard is live there, not on the abelian
-- instances).
--
-- The oracle suite living on this module is "Axioma.Cellular": the
-- homomorphism law, shift-centrality, the idempotent image
-- characterization, the projection law, and the 256-rule corpus.  Named
-- witnesses below pin the local conventions; every law that quantifies
-- over a finite space is checked exhaustively there, not here.
module Circuit.Cellular
  ( -- * Configurations
    Config,

    -- * Groups
    Group (..),
    Integer,
    Mod (..),
    mkMod,
    Perm3,
    perm3,
    allPerms3,

    -- * Shifts
    shift,

    -- * Cellular automata
    CA (..),
    runCA,

    -- * Linear CA (finite-support F_2[G] elements)
    LinCA,
    linCA,
    lsupp,
    lone,
    lmul,
    convolve,

    -- * Tori
    configVec,
    vecConfig,
    allConfigs,
    nOfMod,

    -- * F_2 matrices
    matrixOf,
    applyMat,
    rankGF2,
    nullspaceGF2,
    rrefRows,
  )
where

import Data.List (delete)
import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat, Nat, natVal)
import Prelude

-- | A configuration of the full shift: the cofree reading of the Cayley
-- graph.  Kept as a bare function per the stage-1 decision: the
-- centrality law is a pointwise equation between functions, and no
-- comonad law is needed to state it.
type Config g a = g -> a

-- | Groups, minimal: identity, multiplication, inverse.  The paper's
-- convolution convention right-multiplies the site, so instances must
-- satisfy @(g \`gmul\` u) \`gmul\` v = g \`gmul\` (u \`gmul\` v)@ — associativity
-- is the only law 'convolve' spends, and centrality spends nothing at
-- all (it holds for any right action).
class (Eq g) => Group g where
  gid :: g
  gmul :: g -> g -> g
  ginv :: g -> g

-- | The additive group of 'Integer': the full shift over Z.
instance Group Integer where
  gid = 0
  gmul = (+)
  ginv = negate

-- | The cyclic group Z/nZ, residues 0..n-1: the torus quotient.
newtype Mod (n :: Nat) = Mod Int
  deriving (Eq, Show)

-- | Canonical residue constructor: reduces into @[0, n-1]@.
mkMod :: forall n. (KnownNat n) => Int -> Mod n
mkMod i = Mod (i `mod` fromIntegral (natVal (Proxy @n)))

instance (KnownNat n) => Group (Mod n) where
  gid = Mod 0
  gmul (Mod a) (Mod b) = mkMod (a + b)
  ginv (Mod a) = mkMod (negate a)

-- | The symmetric group S_3 as permutations of {0,1,2}, stored as the
-- triple of images.  'gmul' p q is composition p ∘ q (q applied first),
-- matching the paper's uv = "u after v" reading of the group product in
-- (cd)_w = Σ_{uv=w} c_u d_v.
newtype Perm3 = Perm3 (Int, Int, Int)
  deriving (Eq, Show)

-- | Build a permutation from its action on 0, 1, 2.  Partial: the triple
-- must be a genuine permutation (each of 0,1,2 exactly once).
perm3 :: (Int, Int, Int) -> Perm3
perm3 t@(a, b, c)
  | sorted == [0, 1, 2] = Perm3 t
  | otherwise = error ("perm3: not a permutation: " ++ show t)
  where
    sorted = [min a (min b c), a + b + c - min a (min b c) - max a (max b c), max a (max b c)]

-- | The six elements of S_3, in a fixed enumeration order used by the
-- exhaustive checks.
allPerms3 :: [Perm3]
allPerms3 =
  [ perm3 (0, 1, 2),
    perm3 (0, 2, 1),
    perm3 (1, 0, 2),
    perm3 (1, 2, 0),
    perm3 (2, 0, 1),
    perm3 (2, 1, 0)
  ]

-- | Translate a configuration by h, as the left action of the group on
-- the full shift: @(shift h x)(g) = x(h^-1·g)@.  With the right-neighbor
-- window convention of 'runCA' and 'convolve', this is the unique
-- translation making centrality unconditional: on nonabelian groups a
-- right-multiplication shift would pick up commutators (checked
-- exhaustively on S_3 in "Axioma.Cellular", check 2).
--
-- >>> shift 2 (\i -> i * i) 5
-- 9
--
-- Centrality of the rule-90 element t + t^-1 on Z, observed on a window
-- of the 5-periodic configuration x(g) = [g mod 5 == 0]: both sides
-- reduce to x(g-1) ⊕ x(g-3), so an off-by-one in 'shift' goes red:
--
-- >>> let c90 = linCA [1, -1] :: LinCA Integer
-- >>> let x g = g `mod` 5 == 0
-- >>> [convolve c90 (shift 2 x) g | g <- [0 .. 7]] == [shift 2 (convolve c90 x) g | g <- [0 .. 7]]
-- True
shift :: (Group g) => g -> Config g a -> Config g a
shift h x g = x (gmul (ginv h) g)

instance Group Perm3 where
  gid = perm3 (0, 1, 2)
  gmul p q =
    Perm3 (img p (img q 0), img p (img q 1), img p (img q 2))
    where
      img :: Perm3 -> Int -> Int
      img (Perm3 (a, b, c)) i = case i of
        0 -> a
        1 -> b
        _ -> c
  ginv p = case [q | q <- allPerms3, gmul p q == gid] of
    (q : _) -> q
    [] -> error "ginv: S_3 inverse not found"

-- | A cellular automaton: finite memory M ⊂ G and a local rule on the
-- window, in memory order.
data CA g a = CA
  { memory :: [g],
    localRule :: [a] -> a
  }

-- | Run a CA on a configuration: @(runCA ca x)(g) = ϕ((x(gu))_{u ∈ M})@.
--
-- Rule 30 on the 3-torus as a table CA: one live cell maps to three
-- live cells — the leftward growth that makes rule 30 left-permutive
-- (Axioma.Cellular, check 5):
--
-- >>> let rule30torus = CA [mkMod 2, mkMod 0, mkMod 1] (\w -> case w of { [l, c, r] -> l /= (c || r); _ -> error "window" }) :: CA (Mod 3) Bool
-- >>> configVec (runCA rule30torus (vecConfig [True, False, False]))
-- [True,True,True]
runCA :: (Group g) => CA g a -> Config g a -> Config g a
runCA ca x g = localRule ca [x (gmul g u) | u <- memory ca]

-- | A finite-support element of F_2[G]: stored as its support (the list
-- of group elements with coefficient 1), xor-closed.  'lmul' is
-- convolution of supports; doubling an element cancels it, as char-2
-- demands.
newtype LinCA g = LinCA [g]
  deriving (Eq, Show)

-- | Smart constructor: xor-combine repeated elements so the support has
-- no duplicates.
linCA :: (Eq g) => [g] -> LinCA g
linCA = LinCA . foldr insert []

-- | The support list.
lsupp :: LinCA g -> [g]
lsupp (LinCA us) = us

-- | The unit 1 = δ_{1_G}: convolution with it is the identity (paper
-- Lemma 7.1, T_1 = id).
lone :: (Group g) => LinCA g
lone = LinCA [gid]

-- | Product in F_2[G]: @(cd)_w = Σ_{uv=w} c_u d_v@, addition mod 2.  The
-- order is cd, not dc, for the right-neighbor convention — on S_3 the
-- two differ, which is what makes the order a named mutation there.
--
-- On S_3 with s = (1 2) and t the 3-cycle (0 1 2): st is the
-- transposition (0 2) while ts is the transposition (0 1) — the
-- multiplication order is visible in the support, so a swapped 'lmul'
-- fails this witness:
--
-- >>> let s = perm3 (0, 2, 1); t = perm3 (1, 2, 0)
-- >>> lsupp (lmul (linCA [s]) (linCA [t])) == [perm3 (2, 1, 0)]
-- True
-- >>> lsupp (lmul (linCA [t]) (linCA [s])) == [perm3 (1, 0, 2)]
-- True
lmul :: (Group g) => LinCA g -> LinCA g -> LinCA g
lmul (LinCA us) (LinCA vs) = LinCA (foldr insert [] [gmul u v | u <- us, v <- vs])

-- | Convolution action on configurations: @(T_c x)(g) = Σ_u c_u·x(gu)@,
-- addition in F_2.  Faithful: c ↦ T_c is determined by its coefficients
-- (paper eq. 7.3, (T_c δ_h)(1_G) = c_h).
--
-- The convention witness: with c = 1 + t^2 on Z and δ_0 the unit
-- configuration at 0, (T_c δ_0)(g) = c_{g^-1}, so T_c δ_0 is supported
-- at g = -2 and g = -1 — a left-neighbor convention would put the
-- support at g = 1 and g = 2:
--
-- >>> let c = linCA [1, 2] :: LinCA Integer
-- >>> let delta0 g = g == 0
-- >>> [convolve c delta0 g | g <- [-2 .. 1]]
-- [True,True,False,False]
--
-- Lemma 7.1 on Z, composition against product: T_c ∘ T_d = T_{cd} at
-- three sites of a two-point configuration (cd = t + t^3, the doubling
-- at t^2 cancelling mod 2):
--
-- >>> let d = linCA [0, 1] :: LinCA Integer
-- >>> let x g = g == 2 || g == 5
-- >>> [convolve c (convolve d x) g | g <- [-1 .. 1]] == [convolve (lmul c d) x g | g <- [-1 .. 1]]
-- True
convolve :: (Group g) => LinCA g -> Config g Bool -> Config g Bool
convolve (LinCA us) x g = foldr (/=) False [x (gmul g u) | u <- us]

-- xor-insert: toggling membership of an element in a support list.
insert :: (Eq g) => g -> [g] -> [g]
insert u us
  | u `elem` us = filter (/= u) us
  | otherwise = u : us

-- * Tori

-- | The order of the cyclic group: number of sites on the torus.
nOfMod :: forall n. (KnownNat n) => Int
nOfMod = fromIntegral (natVal (Proxy @n))

-- | Read a torus configuration as a list of site values, sites in
-- canonical order @[0, 1, .., n-1]@.
configVec :: forall n a. (KnownNat n) => Config (Mod n) a -> [a]
configVec x = [x (mkMod i) | i <- [0 .. nOfMod @n - 1]]

-- | The point configuration agreeing with a list on sites @[0, n-1]@.
-- Partial: the list must have exactly n entries.
vecConfig :: forall n a. [a] -> Config (Mod n) a
vecConfig v = \(Mod i) -> go i v
  where
    go i xs = case xs of
      [] -> error "vecConfig: wrong length"
      (x : rest)
        | i == 0 -> x
        | otherwise -> go (i - 1) rest

-- | Every configuration on a torus of order n over a finite alphabet
-- listing, as site-value lists.  For n = 12 over Bool this is 4096
-- configurations — the exact enumeration the axioma checks spend.
allConfigs :: forall n a. (KnownNat n) => [a] -> [[a]]
allConfigs alphabet = go (nOfMod @n)
  where
    go 0 = [[]]
    go k = [x : rest | x <- alphabet, rest <- go (k - 1)]

-- * F_2 matrices

-- | The matrix of a linear CA on a torus, in the site basis: row i is
-- the image of the unit configuration at site i, so
-- @(applyMat (matrixOf c) (configVec x)) == configVec (convolve c x)@.
--
-- The idempotent e = 1 + t + t^2 in F_2[Z/3] (e^2 = e, since the
-- doubling terms cancel: t^2 + t^4 = t^2 + t); its matrix has rank 1
-- and its nullspace at I + M_e is the fixed space — the anchors of
-- "Axioma.Cellular" check 3:
--
-- >>> let e = linCA [mkMod 0, mkMod 1, mkMod 2] :: LinCA (Mod 3)
-- >>> lmul e e == e
-- True
-- >>> rankGF2 (matrixOf e)
-- 1
-- >>> configVec (convolve e (vecConfig [True, False, False]))
-- [True,True,True]
-- >>> applyMat (matrixOf e) [True, False, False]
-- [True,True,True]
matrixOf :: forall n. (KnownNat n) => LinCA (Mod n) -> [[Bool]]
matrixOf c =
  [ [coeff (delta i j) | j <- [0 .. n - 1]]
  | i <- [0 .. n - 1]
  ]
  where
    n = nOfMod @n
    delta i j = mkMod (j - i)
    coeff u = u `elem` lsupp c

-- | Apply a Bool-matrix to a Bool-vector: addition is xor.
applyMat :: [[Bool]] -> [Bool] -> [Bool]
applyMat m v = [foldr (/=) False (zipWith (&&) row v) | row <- m]

-- | Row rank over F_2, by Gaussian elimination.  Rank is the size
-- oracle behind the idempotent image characterization
-- (im(T_e) = fix(T_e), checked in "Axioma.Cellular"): both spaces must
-- have the same rank, and the FinRel comparison there must agree.
rankGF2 :: [[Bool]] -> Int
rankGF2 = length . rrefRows

-- | Basis of the nullspace of a matrix with the given width, as row
-- vectors.  A vector v is in the nullspace iff
-- @applyMat m v == replicate (length v) False@.
--
-- On F_2[Z/3], 1 + t has matrix I + P with one-dimensional nullspace
-- spanned by the all-ones vector:
--
-- >>> let m = matrixOf (linCA [mkMod 0, mkMod 1] :: LinCA (Mod 3))
-- >>> nullspaceGF2 3 m
-- [[True,True,True]]
-- >>> applyMat m [True, True, True]
-- [False,False,False]
nullspaceGF2 :: Int -> [[Bool]] -> [[Bool]]
nullspaceGF2 width m =
  let rrefm = rrefRows m
      pivRows = [(firstOne row, row) | row <- rrefm, or row]
      pivots = map fst pivRows
      free = filter (`notElem` pivots) [0 .. width - 1]
   in [solve f pivRows | f <- free]
  where
    -- Back-substitution over the RREF rows in decreasing pivot order:
    -- the pivot value is the dot product with the accumulator, whose
    -- pivot slot is still False, so the row's own pivot coefficient
    -- contributes nothing.
    solve f pivRows =
      let base = [i == f | i <- [0 .. width - 1]]
       in foldl subst base (reverse pivRows)
    subst acc (p, row) =
      let v = foldr (/=) False (zipWith (&&) row acc)
       in take p acc ++ [v] ++ drop (p + 1) acc

-- | Reduced row echelon form over F_2: full elimination (each pivot
-- column is cleared above and below), zero rows dropped.  Gauss-Jordan
-- forward pass — when a pivot is chosen at column c, the column is
-- cleared from every remaining pool row and from every pivot already
-- collected; a pool row always has zeros at earlier pivot columns, so
-- collected pivots keep their leading columns and the accumulator is
-- RREF at every step.
rrefRows :: [[Bool]] -> [[Bool]]
rrefRows m0 = reverse (forward 0 (filter or m0) [])
  where
    w = case m0 of
      [] -> 0
      (r : _) -> length r
    forward c pool acc
      | c >= w = acc
      | otherwise = case [r | r <- pool, safeAt False c r] of
          [] -> forward (c + 1) pool acc
          (piv : _) ->
            -- Only rows with a 1 in the pivot column are cleared;
            -- adding the pivot row to a row with 0 there would
            -- introduce a 1 into an already-settled column.  'delete'
            -- removes a single occurrence of the pivot row, so an
            -- identical twin survives to be eliminated (it reduces to
            -- zero and drops out).
            let clear r = if safeAt False c r then zipWith (/=) r piv else r
                pool' = [clear r | r <- delete piv pool, or r]
                acc' = map clear acc ++ [piv]
             in forward (c + 1) pool' acc'

-- | Total indexing with a default.
safeAt :: a -> Int -> [a] -> a
safeAt d i xs = case drop i xs of
  (y : _) -> y
  [] -> d

-- | Index of the first True in a nonempty row.
firstOne :: [Bool] -> Int
firstOne row = case [i | (i, x) <- zip [0 ..] row, x] of
  (i : _) -> i
  [] -> error "firstOne: row has no True"

-- $setup
-- >>> :set -XDataKinds -XTypeApplications
