{-# LANGUAGE TupleSections #-}

module HashTree where
import Hashable32
    

data Tree a =
    Leaf { treeHash :: Hash, value :: a }
    | Twig { treeHash :: Hash, son :: Tree a }
    | Node { treeHash :: Hash, lson :: Tree a, rson :: Tree a }
    deriving Show

leaf :: Hashable a => a -> Tree a
leaf a = Leaf (hash a) a


twig :: Hashable a => Tree a -> Tree a
twig s = Twig newHash s
    where newHash = combine (treeHash s) (treeHash s)


node :: Hashable a => Tree a -> Tree a -> Tree a
node l r = Node newHash l r
    where newHash = combine (treeHash l) (treeHash r)


buildTree :: Hashable a => [a] -> Tree a
buildTree [] = error "Empty list"
buildTree list = let
        buildLeafs :: Hashable a => [a] -> [Tree a]
        buildLeafs = map leaf
        
        buildNextLevel :: Hashable a => [Tree a] -> [Tree a]
        buildNextLevel [] = []
        buildNextLevel [h] = [twig h]
        buildNextLevel (h1:h2:tail) = node h1 h2 : buildNextLevel tail

        buildFromLeafs :: Hashable a => [Tree a] -> [Tree a]
        buildFromLeafs [h] = [h]
        buildFromLeafs l = buildFromLeafs $ buildNextLevel l

        ret:_ = buildFromLeafs $ buildLeafs list
    in ret


drawTree :: Show a => Tree a -> String
drawTree tree = let
        drawSingleNode :: Show a => Tree a -> String -> String
        drawSingleNode (Leaf h v) = (showHash h ++) . (" " ++) . shows v
        drawSingleNode (Twig h _ ) = (showHash h ++) . (" +" ++)
        drawSingleNode (Node h _ _) = (showHash h ++) . (" -" ++)

        drawNextSpaces :: Int -> String -> String
        drawNextSpaces 0 = id
        drawNextSpaces n = drawNextSpaces (n - 1) . (' ':) . (' ':)

        drawSpaces :: Int -> String -> String
        drawSpaces 0 = id
        drawSpaces n = ('\n':) . drawNextSpaces n

        drawTreeContinuously :: Show a => Tree a -> Int -> String -> String
        drawTreeContinuously t@(Leaf _ _) n = drawSpaces n . drawSingleNode t
        drawTreeContinuously t@(Twig _ son) n = drawSpaces n . drawSingleNode t . drawTreeContinuously son (n + 1)
        drawTreeContinuously t@(Node _ lson rson) n = drawSpaces n . drawSingleNode t . drawTreeContinuously lson (n + 1) . drawTreeContinuously rson (n + 1)
    in drawTreeContinuously tree 0 "\n"



type MerklePath = [Either Hash Hash]
data MerkleProof a = MerkleProof a MerklePath


showMerklePath :: MerklePath -> String
showMerklePath path = let
        showMerklePathContinuously :: MerklePath -> String -> String
        showMerklePathContinuously [] = id
        showMerklePathContinuously ((Left h):t) = ("<" ++) . ((showHash h) ++) . showMerklePathContinuously t
        showMerklePathContinuously ((Right h):t) = (">" ++) . ((showHash h) ++) . showMerklePathContinuously t
    in showMerklePathContinuously path ""



instance Show a => Show (MerkleProof a) where
    showsPrec 0 (MerkleProof value path) = ("MerkleProof " ++) . showsPrec 11 value . (" " ++) . ((showMerklePath path) ++)
    showsPrec _ proof = ('(':) . showsPrec 0 proof . (')':)



buildProof :: Hashable a => a -> Tree a -> Maybe (MerkleProof a)
buildProof a (Leaf _ v)
    | (hash a) == (hash v) = Just (MerkleProof a [])
    | otherwise = Nothing
buildProof a (Twig _ s) = let
        buildWithoutMaybe :: Tree a -> MerkleProof a -> MerkleProof a
        buildWithoutMaybe son (MerkleProof value furtherPath) = MerkleProof value (Left (treeHash son):furtherPath)
    in buildWithoutMaybe s <$> buildProof a s
buildProof a (Node _ l r) = let
        brotherAndProof :: b -> b -> Maybe a -> Maybe a -> Maybe (Either b b, a)
        brotherAndProof _ rb lp@(Just x) _ = Just (Left rb, x)
        brotherAndProof lb _ _ rp = (Right lb, ) <$> rp

        mapEither :: (a -> b) -> Either a a -> Either b b
        mapEither f (Left a) = Left (f a)
        mapEither f (Right a) = Right (f a)

        buildWithoutMaybe :: (Either (Tree a) (Tree a), MerkleProof a) -> MerkleProof a
        buildWithoutMaybe (brother, (MerkleProof value furtherPath)) = MerkleProof value ((mapEither treeHash brother) : furtherPath)
    in buildWithoutMaybe <$> brotherAndProof l r (buildProof a l) (buildProof a r)


merklePaths :: Hashable a => a -> Tree a -> [MerklePath]
merklePaths a t = let
        merklePathsContinuously :: Hashable a => a -> Tree a -> MerklePath -> [MerklePath] -> [MerklePath]
        merklePathsContinuously wanted (Leaf _ v) reversePath
            | (hash wanted) == (hash v) = ((reverse reversePath) :)
            | otherwise = id
        merklePathsContinuously wanted (Twig _ s) reversePath = merklePathsContinuously wanted s ((Left (treeHash s)) : reversePath)
        merklePathsContinuously wanted (Node _ l r) reversePath = merklePathsContinuously wanted l ((Left (treeHash r)) : reversePath) .
            merklePathsContinuously wanted r ((Right (treeHash l)) : reversePath)
    in merklePathsContinuously a t [] []


verifyProof :: Hashable a => Hash -> MerkleProof a -> Bool
verifyProof h (MerkleProof v path) = let
        combineSons :: Either Hash Hash -> Hash -> Hash
        combineSons (Left r) l = combine l r
        combineSons (Right l) r = combine l r
    in h == foldr combineSons (hash v) path