module MultiMap where
import qualified Data.Map                      as Map

-- Some helpers for multimaps
type MultiMap k v = Map.Map k [v]

insert :: Ord k => k -> v -> MultiMap k v -> MultiMap k v
insert k v m = case Map.lookup k m of
    Just vs -> Map.insert k (v : vs) m
    Nothing -> Map.insert k [v] m

delete :: Ord k => k -> MultiMap k a -> MultiMap k a
delete k m = case Map.lookup k m of
    Just (v : vs) -> Map.insert k vs m
    _             -> Map.delete k m

lookup :: Ord k => k -> MultiMap k a -> Maybe a
lookup k m = case Map.lookup k m of
    Just (v : vs) -> Just v
    _             -> Nothing

empty :: MultiMap k a
empty = Map.empty
