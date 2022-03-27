-- This is a Sudoku solver that is run from the command line.  It is written in Haskell, and it is
-- quite fast, solving most puzzles in one or two milliseconds.
--
-- The basic outline of how it works is as follows: It takes in the puzzle and populates an
-- 81-element vector with the known values with zeros for the unknown ones.  It will then try to
-- iteratively deduce elements of the puzzle by first figuring out the possible options for each
-- empty square based on the number used in the associated rows, columns, and blocks.  For many
-- puzzles, doing this over and over will solve the puzzle entirely.  If we reach a point where no
-- more deductions are possible, we add a step to weed out options based on several circumstances.
-- We continue trying to deduce square digits until we are either done or have reached a point where
-- no more deductions are possible.  At this point, we solve the remaining empty squares using a
-- depth-first search.  Before starting this process, we dynamically order the remaining empty
-- squares so that we optimize looking at those likely to have the fewest options first in the the
-- process.
--
-- Copyright - Truman Collins
-- April 2015 - October 2015
-- February 2019 -
--

-- The following packages are needed to compile this:
-- cabal install clock
-- cabal install vector
-- cabal install parallel
-- cabal install data-ordlist

{-# LANGUAGE BangPatterns #-}

import Data.Char
import Data.Int
import Data.Bits
import Data.List
import qualified Data.List.Ordered as LO
import Data.Maybe
import Data.Foldable (foldlM)
import System.Console.GetOpt
import System.IO (hFlush, stdout)
import System.Clock
import System.Mem
import System.Exit
import Text.Printf
import qualified Data.Array.Unboxed as UA
import qualified Data.ByteString.Char8 as BC
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import qualified Data.Map.Strict as M
import System.Environment (getArgs, getProgName)
import Control.Monad
import Control.Parallel
import Control.Parallel.Strategies
--import Debug.Trace

version :: String
version = "1.2"

-- Size constants for 9x9 board.

cellCount, rcbCount, maxRCBInd, minCellVal, maxCellVal, vecSizeForOpts :: Int
cellCount = 81
rcbCount = 9
maxRCBInd = 8
minCellVal = 1
maxCellVal = 9
vecSizeForOpts = 10

-- Helper function for time calculations.

computeElapsedTime :: TimeSpec -> TimeSpec -> Double
computeElapsedTime startTime endTime
  = (convertTimeToDouble endTime) - (convertTimeToDouble startTime)
  where
    convertTimeToDouble :: TimeSpec -> Double
    convertTimeToDouble tm = (fromIntegral (sec tm)) + (fromIntegral (nsec tm)) / 1.0e9

-- Types used for the Sudoku solver.  Use 8 bit and 16 bit integers when possible to reduce the
-- amount of copying needed when updating vectors.

type SKBoardElement = Int8
type SKBoard = UV.Vector SKBoardElement
type SKUsed = Int16
type SKUsedVec = UV.Vector SKUsed
type SKConvert = Int
type SKConvertVec = UV.Vector SKConvert
type SKOptions = (Int, [SKBoardElement])
type SKSquaresOptionsPair = ([Int], [SKBoardElement])
type SKOptionsPair = (Int, (SKBoardElement, SKBoardElement))
type SKCellAssignment = (Int, SKBoardElement)
type SKCellAssignmentList = [SKCellAssignment]
type SKOptionsList = [SKOptions]
type SKOptionsToRemove = [SKSquaresOptionsPair]
type OptionCounts = V.Vector Int
type RCBOptionCounts = V.Vector OptionCounts
type MapPairs = M.Map (Int, Int) (Int, [Int])
type MapTriples = M.Map (Int, Int, Int) (Int, [Int])
type MapAccumulator = ([([Int], [Int])], [([Int], [Int])])
type MapRCBAndValKey = (SKBoardElement, SKConvert)
type MapRCBAndValEntry = (Int, [Int])
type MapRCBAndVal = M.Map MapRCBAndValKey MapRCBAndValEntry
data RCB_t = Row | Col | Block deriving Eq

-- Holds the state of a board including bits set indicating the digits used in each row, column, and
-- block as well as the remaining empty square indices.

data BoardState = BoardState {
    d_board        :: SKBoard
  , d_usedInRow    :: SKUsedVec
  , d_usedInCol    :: SKUsedVec
  , d_usedInBlock  :: SKUsedVec
  , d_emptySquares :: [Int]
} deriving Show

-- Maximum length of a debug line in the output.

maxDebugLineLen :: Int
maxDebugLineLen = 84

-- Generate all pairs of the list with the first element always being before the second in the list.

pairsOrdered :: [a] -> [(a, a)]
pairsOrdered [] = []
pairsOrdered (_ : []) = []
pairsOrdered (x : xs) = (map (\y -> (x, y)) xs) ++ (pairsOrdered xs)

-- Use these vectors to quickly convert from a square index in the board to the index of the row,
-- column, or block that it is in.  Rows, columns, and blocks are numbered from 0 to 8.

skIndexToRow :: SKConvertVec
skIndexToRow   = UV.fromList (concatMap (\x -> replicate 9 x) [0..8])
skIndexToCol :: SKConvertVec
skIndexToCol   = UV.fromList [x `rem` 9 | x <- [0..80]]
skIndexToBlock :: SKConvertVec
skIndexToBlock = UV.fromList (concatMap (replicate 3) (concat (concatMap (replicate 3)
                                       [[0,1,2],[3,4,5],[6,7,8]])))

-- Array mapping from block index (0-8) to the corresponding list of board indices (0-80)

blockIndexToBoardIndices :: UA.Array Int [Int]
blockIndexToBoardIndices = UA.array (0,8) [(0,[0,1,2,9,10,11,18,19,20]),
                                           (1,[3,4,5,12,13,14,21,22,23]),
                                           (2,[6,7,8,15,16,17,24,25,26]),
                                           (3,[27,28,29,36,37,38,45,46,47]),
                                           (4,[30,31,32,39,40,41,48,49,50]),
                                           (5,[33,34,35,42,43,44,51,52,53]),
                                           (6,[54,55,56,63,64,65,72,73,74]),
                                           (7,[57,58,59,66,67,68,75,76,77]),
                                           (8,[60,61,62,69,70,71,78,79,80])]

-- Array mapping from board index to block row index and to block column index.

boardIndexToBlockRowIndex :: UV.Vector Int
boardIndexToBlockRowIndex
  = UV.fromList [0,0,0,3,3,3,6,6,6,1,1,1,4,4,4,7,7,7,2,2,2,5,5,5,8,8,8,
                 9,9,9,12,12,12,15,15,15,10,10,10,13,13,13,16,16,16,11,11,11,14,14,14,17,17,17,
                 18,18,18,21,21,21,24,24,24,19,19,19,22,22,22,25,25,25,20,20,20,23,23,23,26,26,26]
boardIndexToBlockColIndex :: UV.Vector Int
boardIndexToBlockColIndex = UV.fromList (concat [(concat (replicate 3 [0..8])),
                                                 (concat (replicate 3 [9..17])),
                                                 (concat (replicate 3 [18..26]))])

-- These arrays hold, for each block row and block column index, the list of board indices that are
-- in that row or column, respectively, but not in the block.

inLineSquaresWithBlockRow :: UA.Array Int [Int]
inLineSquaresWithBlockRow = UA.array (0,26) (map blockRowIndexToOthersInRow [0..26])
inLineSquaresWithBlockCol :: UA.Array Int [Int]
inLineSquaresWithBlockCol = UA.array (0,26) (map blockColIndexToOthersInCol [0..26])

blockRowIndexToOthersInRow :: Int -> (Int, [Int])
blockRowIndexToOthersInRow brIndex = (brIndex, boardIndicesInRowButNotBlockRow)
  where
    boardIndicesInRowButNotBlockRow
      = filter (\x -> fullRowIndex == (skIndexToRow UV.! x)
                      && (boardIndexToBlockRowIndex UV.! x) /= brIndex) [0..80]
    fullRowIndex
      = skIndexToRow UV.!
        (fromJust (find (\x -> (boardIndexToBlockRowIndex UV.! x) == brIndex) [0..80]))

blockColIndexToOthersInCol :: Int -> (Int, [Int])
blockColIndexToOthersInCol brIndex = (brIndex, boardIndicesInColButNotBlockCol)
  where
    boardIndicesInColButNotBlockCol
      = filter (\x -> fullColIndex == (skIndexToCol UV.! x)
                      && (boardIndexToBlockColIndex UV.! x) /= brIndex) [0..80]
    fullColIndex
      = skIndexToCol UV.!
        (fromJust (find (\x -> (boardIndexToBlockColIndex UV.! x) == brIndex) [0..80]))

-- These arrays hold, for each block row and block column index, the list of board indices that are
-- in the block but not this mini-row or column.

otherBlockSquaresThanMiniRow :: UA.Array Int [Int]
otherBlockSquaresThanMiniRow
  = UA.array (0,26) [(0,[9,10,11,18,19,20]),(1,[0,1,2,18,19,20]),(2,[0,1,2,9,10,11]),
                     (3,[12,13,14,21,22,23]),(4,[3,4,5,21,22,23]),(5,[3,4,5,12,13,14]),
                     (6,[15,16,17,24,25,26]),(7,[6,7,8,24,25,26]),(8,[6,7,8,15,16,17]),
                     (9,[36,37,38,45,46,47]),(10,[27,28,29,45,46,47]),(11,[27,28,29,36,37,38]),
                     (12,[39,40,41,48,49,50]),(13,[30,31,32,48,49,50]),(14,[30,31,32,39,40,41]),
                     (15,[42,43,44,51,52,53]),(16,[33,34,35,51,52,53]),(17,[33,34,35,42,43,44]),
                     (18,[63,64,65,72,73,74]),(19,[54,55,56,72,73,74]),(20,[54,55,56,63,64,65]),
                     (21,[66,67,68,75,76,77]),(22,[57,58,59,75,76,77]),(23,[57,58,59,66,67,68]),
                     (24,[69,70,71,78,79,80]),(25,[60,61,62,78,79,80]),(26,[60,61,62,69,70,71])]
otherBlockSquaresThanMiniCol :: UA.Array Int [Int]
otherBlockSquaresThanMiniCol
  = UA.array (0,26) [(0,[1,2,10,11,19,20]),(1,[0,2,9,11,18,20]),(2,[0,1,9,10,18,19]),
                     (3,[4,5,13,14,22,23]),(4,[3,5,12,14,21,23]),(5,[3,4,12,13,21,22]),
                     (6,[7,8,16,17,25,26]),(7,[6,8,15,17,24,26]),(8,[6,7,15,16,24,25]),
                     (9,[28,29,37,38,46,47]),(10,[27,29,36,38,45,47]),(11,[27,28,36,37,45,46]),
                     (12,[31,32,40,41,49,50]),(13,[30,32,39,41,48,50]),(14,[30,31,39,40,48,49]),
                     (15,[34,35,43,44,52,53]),(16,[33,35,42,44,51,53]),(17,[33,34,42,43,51,52]),
                     (18,[55,56,64,65,73,74]),(19,[54,56,63,65,72,74]),(20,[54,55,63,64,72,73]),
                     (21,[58,59,67,68,76,77]),(22,[57,59,66,68,75,77]),(23,[57,58,66,67,75,76]),
                     (24,[61,62,70,71,79,80]),(25,[60,62,69,71,78,80]),(26,[60,61,69,70,78,79])]

-- Used to calculate the above two arrays.
--otherBlockSquaresThanMiniRow = UA.array (0,26) $ map blockRowIndToOthersInBlock [0..26]
--otherBlockSquaresThanMiniCol = UA.array (0,26) $ map blockColIndToOthersInBlock [0..26]
--blockRowIndToOthersInBlock :: Int -> (Int, [Int])
--blockRowIndToOthersInBlock blockRowIndex = (blockRowIndex, otherIndicesInBlock)
--  where
--    otherRowIndicesInBlock = blockRCIndexToOthersInBlock UA.! blockRowIndex
--    blockIndex = skIndexToBlock UV.! boardIndexInThisRow
--    boardIndexInThisRow = fromJust
--                          $ find (\x -> (boardIndexToBlockRowIndex UV.! x) == blockRowIndex) [0..80]
--    otherIndicesInBlock = filter (\x -> let blkRowInd = (boardIndexToBlockRowIndex UV.! x)
--                                        in elem blkRowInd otherRowIndicesInBlock) [0..80]
--
--blockColIndToOthersInBlock :: Int -> (Int, [Int])
--blockColIndToOthersInBlock blockColIndex = (blockColIndex, otherIndicesInBlock)
--  where
--    otherColIndicesInBlock = blockRCIndexToOthersInBlock UA.! blockColIndex
--    blockIndex = skIndexToBlock UV.! boardIndexInThisCol
--    boardIndexInThisCol = fromJust
--                          $ find (\x -> (boardIndexToBlockColIndex UV.! x) == blockColIndex) [0..80]
--    otherIndicesInBlock = filter (\x -> let blkColInd = (boardIndexToBlockColIndex UV.! x)
--                                        in elem blkColInd otherColIndicesInBlock) [0..80]
--

-- Used to identify block row or columns that have options repeated two or three times.

maskTwoOrThreeCounts :: Int
maskTwoOrThreeCounts = foldl' (\acc x -> acc .|. (shiftL 0x1 (2 * x + 1))) 0 [1..9]

-- Mapping from a row or column index for block rows or columns to the other rows
-- or columns in that block.

blockRCIndexToOthersInBlock :: UA.Array Int [Int]
blockRCIndexToOthersInBlock = UA.array (0,26) [(0,[1,2]),(1,[0,2]),(2,[0,1]),
                                               (3,[4,5]),(4,[3,5]),(5,[3,4]),
                                               (6,[7,8]),(7,[6,8]),(8,[6,7]),
                                               (9,[10,11]),(10,[9,11]),(11,[9,10]),
                                               (12,[13,14]),(13,[12,14]),(14,[12,13]),
                                               (15,[16,17]),(16,[15,17]),(17,[15,16]),
                                               (18,[19,20]),(19,[18,20]),(20,[18,19]),
                                               (21,[22,23]),(22,[21,23]),(23,[21,22]),
                                               (24,[25,26]),(25,[24,26]),(26,[24,25])]

-- Mapping from a row or column index for block rows or columns to the other rows or columns in-line
-- with it.

blockRCIndexToInLineRows :: UA.Array Int [Int]
blockRCIndexToInLineRows
    = UA.array (0,26) [(0,[3,6]),(1,[4,7]),(2,[5,8]),(3,[0,6]),(4,[1,7]),(5,[2,8]),(6,[0,3]),(7,[1,4]),
                       (8,[2,5]),(9,[12,15]),(10,[13,16]),(11,[14,17]),(12,[9,15]),(13,[10,16]),
                       (14,[11,17]),(15,[9,12]),(16,[10,13]),(17,[11,14]),(18,[21,24]),(19,[22,25]),
                       (20,[23,26]),(21,[18,24]),(22,[19,25]),(23,[20,26]),(24,[18,21]),(25,[19,22]),
                       (26,[20,23])]
blockRCIndexToInLineCols :: UA.Array Int [Int]
blockRCIndexToInLineCols
    = UA.array (0,26) [(0,[9,18]),(1,[10,19]),(2,[11,20]),(3,[12,21]),(4,[13,22]),(5,[14,23]),
                       (6,[15,24]),(7,[16,25]),(8,[17,26]),(9,[0,18]),(10,[1,19]),(11,[2,20]),
                       (12,[3,21]),(13,[4,22]),(14,[5,23]),(15,[6,24]),(16,[7,25]),(17,[8,26]),
                       (18,[0,9]),(19,[1,10]),(20,[2,11]),(21,[3,12]),(22,[4,13]),(23,[5,14]),
                       (24,[6,15]),(25,[7,16]),(26,[8,17])]

-- Used to calculate the above two arrays.
--blockRCIndexToInLineRows = UA.array (0,26) (map blockRowIndToOthersInRow [0..26])
--blockRCIndexToInLineCols = UA.array (0,26) (map blockColIndToOthersInCol [0..26])
--blockRowIndToOthersInRow :: Int -> (Int, [Int])
--blockRowIndToOthersInRow blockRowIndex = (blockRowIndex, otherMiniRowsInLine)
--  where
--    otherMiniRowsInLine = ((map head) . group . sort)
--                          $ foldl' (\acc x -> let rowInd = skIndexToRow UV.! x
--                                                  miniRowInd = boardIndexToBlockRowIndex UV.! x
--                                              in if rowInd == rowIndex && miniRowInd /= blockRowIndex
--                                                 then miniRowInd : acc else acc) [] [0..80]
--    rowIndex = skIndexToRow UV.! boardIndexInThisMiniRow
--    boardIndexInThisMiniRow = fromJust
--                              $ find (\x -> (boardIndexToBlockRowIndex UV.! x) == blockRowIndex) [0..80]
--
--blockColIndToOthersInCol :: Int -> (Int, [Int])
--blockColIndToOthersInCol blockColIndex = (blockColIndex, otherMiniColsInLine)
--  where
--    otherMiniColsInLine = ((map head) . group . sort)
--                          $ foldl' (\acc x -> let colInd = skIndexToCol UV.! x
--                                                  miniColInd = boardIndexToBlockColIndex UV.! x
--                                              in if colInd == colIndex && miniColInd /= blockColIndex
--                                                 then miniColInd : acc else acc) [] [0..80]
--    colIndex = skIndexToCol UV.! boardIndexInThisMiniCol
--    boardIndexInThisMiniCol = fromJust
--                              $ find (\x -> (boardIndexToBlockColIndex UV.! x) == blockColIndex) [0..80]

-- Functions to generate the set of board indices (0-80) corresponding with a row, column, or block
-- index (0-8).

boardIndicesForRow :: Int -> [Int]
boardIndicesForRow rowIndex = [(rowIndex * 9)..((rowIndex + 1) * 9 - 1)]
boardIndicesForCol :: Int -> [Int]
boardIndicesForCol colIndex = [x + colIndex | x <- [0,9..72]]
boardIndicesForBlock :: Int -> [Int]
boardIndicesForBlock blockIndex = blockIndexToBoardIndices UA.! blockIndex

-- Debug data returned from solver.  The d_deduceCounts holds the number of squares determined in
-- the most simple way, the number determined by finding an option listed only once in a row,
-- column, or block, and the third is a 0 if no refining of optiosn is done and 1 otherwise.

data DebugInfo = DebugInfo {
    d_dfsDepth      :: Int
  , d_deduceLoops   :: Int
  , d_deducedCounts :: [(Int, Int, Int, [DebugRemovedByStrategies])]
  } deriving Show

-- Take in a list of options for all empty squares on the board, weed out options that are not
-- possible using several techniques (sub-group exclusion, hidden twin/triplet exclusion, lone
-- twin/triplet exclusion, hidden twin chain exclusion, and lone twin chain exclusion), and return
-- the new list of options.  Also return a boolean indicating whether any options were removed or
-- not.

data DebugRemovedByStrategies = DebugRemovedByStrategies {
      d_optionList            :: SKOptionsList
    , d_weededOptionsList     :: SKOptionsList
    , d_sortedMergedRemoves   :: SKOptionsList
    , d_subgroupExclusionRows :: SKOptionsToRemove
    , d_subgroupExclusionCols :: SKOptionsToRemove
    , d_twinTripRows          :: SKOptionsToRemove
    , d_twinTripCols          :: SKOptionsToRemove
    , d_twinTripBlocks        :: SKOptionsToRemove
    , d_twoChainsRows         :: SKOptionsToRemove
    , d_twoChainsCols         :: SKOptionsToRemove
    , d_twoChainsBlocks       :: SKOptionsToRemove
    , d_twoHiddenChainsRows   :: SKOptionsToRemove
    , d_twoHiddenChainsCols   :: SKOptionsToRemove
    , d_twoHiddenChainsBlocks :: SKOptionsToRemove
    , d_XWingRows             :: SKOptionsToRemove
    , d_XWingCols             :: SKOptionsToRemove
    , d_XWingBlocks           :: SKOptionsToRemove
} deriving Show

-- Used to access the lists of refines done as a group. Add to this list any new refining steps.

listOfDebugRefiningLists :: [(DebugRemovedByStrategies -> SKOptionsToRemove)]
listOfDebugRefiningLists
  = [d_subgroupExclusionRows, d_subgroupExclusionCols, d_twinTripRows, d_twinTripCols,
     d_twinTripBlocks, d_twoChainsRows, d_twoChainsCols, d_twoChainsBlocks,
     d_twoHiddenChainsRows, d_twoHiddenChainsCols, d_twoHiddenChainsBlocks, d_XWingRows,
     d_XWingCols, d_XWingBlocks]

-- Names of the refining option lists used for debug printing. Add to this for any new refining
-- steps.

namesOfRefiningLists :: [String]
namesOfRefiningLists
  = ["SubExclRows", "SubExclCols", "TwinTripRows", "TwinTripCols", "TwinTripBlocks",
     "TwoChainRows", "TwoChainCols", "TwoChainBlocks", "TwoHidChainRows", "TwoHidChainCols",
     "TwoHidChainBlocks", "X-WingRows", "X-WingCols", "X-WingBlocks"]

-- Convert a digit character to the corresponding int (0-9) and convert '.' to 0.

digOrDot2Int :: Char -> Int
digOrDot2Int '.' = 0
digOrDot2Int ch = digitToInt ch

-- Take in a list and return a list of all pairs of elements in the list, with the pairs being in
-- the same order.  For example:
-- listOfAllPairsSameOrder [1,2,3,4] = [(1,2), (1,3), (1,4), (2,3), (2,4), (3,4)]

listOfAllPairsSameOrder :: [a] -> [(a, a)]
listOfAllPairsSameOrder [] = []
listOfAllPairsSameOrder (_ : []) = []
listOfAllPairsSameOrder (x : xs) = (map (\y -> (x, y)) xs) ++ listOfAllPairsSameOrder xs

-- Same for triples.

listOfAllTriplesSameOrder :: [a] -> [(a, a, a)]
listOfAllTriplesSameOrder [] = []
listOfAllTriplesSameOrder (_ : []) = []
listOfAllTriplesSameOrder (_ : _ : []) = []
listOfAllTriplesSameOrder (x : xs) = (map (\(y, z) -> (x, y, z)) (listOfAllPairsSameOrder xs))
                                      ++ (listOfAllTriplesSameOrder xs)

-- Take in a list and return a list of all list pairs of elements in the list, with the list pairs
-- being in the same order.  For example:
-- listOfAllPairsSameOrder [1,2,3,4] = [[1,2], [1,3], [1,4], [2,3], [2,4], [3,4]]

listOfAllListPairsSameOrder :: [a] -> [[a]]
listOfAllListPairsSameOrder [] = []
listOfAllListPairsSameOrder (_ : []) = []
listOfAllListPairsSameOrder (x : xs) = (map (\y -> [x, y]) xs) ++ listOfAllListPairsSameOrder xs

-- Return the list resulting in elements of the second list removed from the first list.  Both
-- incoming lists are assumed to be sorted, and the resulting list will be sorted as well.

removeSecondFromFirstSorted :: (Ord a) => [a] -> [a] -> [a]
removeSecondFromFirstSorted [] _ = []
removeSecondFromFirstSorted list1' [] = list1'
removeSecondFromFirstSorted list1'@(ind1' : xs1') list2'@(ind2' : xs2')
  | ind1' == ind2' = removeSecondFromFirstSorted xs1' xs2'
  | ind1' < ind2'  = ind1' : removeSecondFromFirstSorted xs1' list2'
  | otherwise = removeSecondFromFirstSorted list1' xs2'

-- Used by a fold to expand this list so each set of options is associated with one board index
-- rather than a list of them.

expandList :: SKOptionsList -> SKSquaresOptionsPair -> SKOptionsList
expandList accum (inds, options) = foldl' (\acc x -> (x, options) : acc) accum inds

-- Merge option lists of adjacent entries with the same board index.  Assumes the list is sorted
-- by board index.  Sort the merged option lists.

mergeSameIndices :: [(Int, [SKBoardElement])] -> [(Int, [SKBoardElement])]
mergeSameIndices [] = []
mergeSameIndices ((ind, options) : []) = [(ind, sort options)]
mergeSameIndices ((bdInd1, options1) : (bdInd2, options2) : xs)
  | bdInd1 == bdInd2
    = mergeSameIndices ((bdInd1, (sort $ union options1 options2)) : xs)
  | otherwise
    = (bdInd1, sort options1) : mergeSameIndices ((bdInd2, options2) : xs)

-- This check is for duplicate values in the same row, column, or block.  It will return a quad
-- containing first a boolean indicating if the puzzle was valid, then four lists of pairs of the
-- RCB index and repeated number for any errors found in rows, columns, and blocks.

checkForValidSudokuPuzzle :: BC.ByteString -> (Bool, [(Int, Int)], [(Int, Int)], [(Int, Int)],
                                               (Bool, Int))
checkForValidSudokuPuzzle inputPuzzle
  = (validPuzzle, rowErrors, colErrors, blockErrors, (rightLength, puzzleLength))
  where
    validPuzzle = rightLength && (null rowErrors) && (null colErrors) && (null blockErrors)
    puzzleLength = BC.length inputPuzzle
    rightLength = puzzleLength == cellCount
    (rowErrors, colErrors, blockErrors) = foldl' lookForErrors ([], [], []) [0..8]

    -- Used in a fold to walk through the RCB indices 0-8 accumulating any repeated entries.

    lookForErrors :: ([(Int, Int)], [(Int, Int)], [(Int, Int)]) -> Int
                     -> ([(Int, Int)], [(Int, Int)], [(Int, Int)])
    lookForErrors (inRowErrors, inColErrors, inBlockErrors) rcbIndex
      | (null currRowErrors) && (null currColErrors) && (null currBlockErrors)
        = (inRowErrors, inColErrors, inBlockErrors)
      | otherwise = (newRowErrors, newColErrors, newBlockErrors)
      where
        currRowErrors   = findRepeatedEntries boardIndicesForRow rcbIndex
        currColErrors   = findRepeatedEntries boardIndicesForCol rcbIndex
        currBlockErrors = findRepeatedEntries boardIndicesForBlock rcbIndex
        newRowErrors   = currRowErrors ++ inRowErrors
        newColErrors   = currColErrors ++ inColErrors
        newBlockErrors = currBlockErrors ++ inBlockErrors

    -- Take all of the board elements for this row, column, or block, remove zeros, find those that
    -- have more than one, and return a list of them along with the current RCB index.

    findRepeatedEntries :: (Int -> [Int]) -> Int -> [(Int, Int)]
    findRepeatedEntries relevantBoardIndices rcbIndex = errorList
      where
        errorList = (map (\xs -> (rcbIndex + 1, head xs)) . filter (\xs -> (length xs) > 1)
                     . group . sort . filter (\val -> val /= 0)
                     . map (\index -> digOrDot2Int $ BC.index inputPuzzle index))
                    (relevantBoardIndices rcbIndex)

-- Given a puzzle, generate the list of puzzles with each individual filled square empty in the first
-- puzzle.

genAllPuzzlesWithOneLessFilledSquare :: String -> [String]
genAllPuzzlesWithOneLessFilledSquare origPuzzle = reverse $ genIter origPuzzle [] []
  where
    genIter :: String -> String -> [String] -> [String]
    genIter [] _ foundSoFar = foundSoFar
    genIter (x : xs) cellsSeen foundSoFar
      | x == '0' = genIter xs (x : cellsSeen) foundSoFar
      | otherwise = genIter xs (x : cellsSeen) (((reverse cellsSeen) ++ ('0' : xs)) : foundSoFar)

-- Given a puzzle, try solving each configuration with the value in a filled square removed.  Return
-- the list of these puzzles that have a single solution.  This function is an IO function solely
-- so it can print out each square as it is analyzed.  To do this without lazy evaluation delaying
-- the actual work, we need to use bang patterns.

findSingleSolutionDerivativesIO :: CmdOptions -> Bool -> String -> IO ([String])
findSingleSolutionDerivativesIO cmdOptions parallelSrch puzzle
  = findSingleSolutionDerivatives' ([], []) puzzle
  where
    findSingleSolutionDerivatives' :: ([String], String) -> String -> IO ([String])
    findSingleSolutionDerivatives' (foundSoFar, _) [] = return (foundSoFar)
    findSingleSolutionDerivatives' (foundSoFar, initialPuzzleRev) (x : xs) = do
      putChar x
      hFlush stdout
      findSingleSolutionDerivatives' (newFoundSoFar, (x : initialPuzzleRev)) xs
        where
          !newFoundSoFar = if x == '0' || (not singleSolution)
                           then foundSoFar
                           else (puzzleWithXBlank : foundSoFar)
          puzzleWithXBlank = (reverse initialPuzzleRev) ++ "0" ++ xs
          singleSolution = (not $ null solutions) && (null $ tail solutions)
          (solutions, _) = solveSudoku cmdOptions parallelSrch (BC.pack puzzleWithXBlank)

-- Solve a single Sudoku puzzle, the input being a string of 81 digits representing the puzzle, with
-- 0s for the unknown values.  The output will be a list of strings with all solutions to the
-- puzzle.  Error checking of the input string is expected to be done prior to the calling of this
-- function.

solveSudoku :: CmdOptions -> Bool -> BC.ByteString -> ([BC.ByteString], DebugInfo)
solveSudoku cmdOptions parallelDFS inputPuzzle
  | notSolvable = ([], (DebugInfo dfsDepth deduceLoopCount deductionCounts))
  | otherwise   = (solutions, (DebugInfo dfsDepth deduceLoopCount deductionCounts))
  where

    -- Map the string input into an 81-element vector representing the board.  Populate bit masks
    -- indicating which numbers are used in which rows, columns, and blocks.  Create a list of the
    -- indexes of squares with unknown values.

    startBoard = (UV.generate 81 (\ind -> (fromIntegral $ digOrDot2Int $ BC.index inputPuzzle ind)))
    fullBoardState = generateBoardStateFromBoard startBoard

    -- Go through the starting board and search for unknown values that can only be one choice given
    -- the contents of their row, column, and block.  Set these, recalculate the used bit masks, and
    -- repeat until there are no more unknown values left or we can no longer find any values that
    -- have only one choice.

    (partSolvedBoardState, notSolvable, deduceLoopCount, deductionCounts)
      = lockInDeducableChoices fullBoardState

    -- Once we have filled in all of the squares that are deducable, do a depth-first search on the
    -- rest given the possible values that remain for each empty square.

    preDFSBoardState = optimizeDFSSearchOrder partSolvedBoardState
    dfsDepth = length (d_emptySquares preDFSBoardState)
    solutions = solveSudokuDFS preDFSBoardState dfsDepth []

    -- Try to improve the search order so that squares with fewer options are visited earlier. This
    -- is tricky because to do it right, we need to find the best first square to try, and then find
    -- the best one after that assuming the first square is set, etc.

    optimizeDFSSearchOrder :: BoardState -> BoardState
    optimizeDFSSearchOrder boardState@(BoardState {d_emptySquares = []}) = boardState
    optimizeDFSSearchOrder boardState@(BoardState {d_board = board, d_emptySquares = emptySquares})
      = boardState {d_emptySquares = optOrder}
      where
        optOrder = dynamicallyFindBestOrder emptiesAndCountsRefined []
        (rowCounts, colCounts, blockCounts) = populateCountInRowColBlock board
        emptiesAndCounts = sortBy bigCountsFirst $ map addCounts emptySquares
        emptiesAndCountsRefined = furtherOptimizeOrder emptiesAndCounts

        -- Reorder the group of empty squares with the highest number of counts based on lowest
        -- number of digit options first.  This is really only helpful for the group with the most
        -- counts, as the others will be dynamically reordered so that this step would be a waste of
        -- time.
        -- It's unclear from running some timings whether this makes a difference or now, but I
        -- suspect that when a lot of squares need to be filled by the depth-first search, that
        -- refining the order of the first few squares could make a significant difference.  I think
        -- this is an amortized win.

        furtherOptimizeOrder :: [(Int, Int)] -> [(Int, Int)]
        furtherOptimizeOrder [] = []
        furtherOptimizeOrder fullInList@((_, maxUsedCount) : _) = newOrder
          where
            newOrder = newMaxCountOrder ++ remainder
            newMaxCountOrder = map (\(ind, usedC, _) -> (ind, usedC)) sortedHighestWithChoices
            sortedHighestWithChoices
              = sortBy (\(_, _, valid1) (_, _, valid2) -> compare valid1 valid2) highestWithChoices
            highestWithChoices
              = map (\(ind, usedC) -> let !valCount = (length $ genValidChoices boardState ind)
                                      in (ind, usedC, valCount))
                    highestUsed
            (highestUsed, remainder) = span (\(_, usedC) -> usedC == maxUsedCount) fullInList

        -- Find optimal search order.  We sorted the list of open squares based on the sum of the
        -- filled row, column, and block squares associated with each empty square.  This function
        -- will then walk down the list, putting the head index on the accumulator, and reordering
        -- the remainder of the list based on the current square being filled.

        dynamicallyFindBestOrder :: [(Int, Int)] -> [Int] -> [Int]
        dynamicallyFindBestOrder [] accum = reverse accum
        dynamicallyFindBestOrder ((ind, _) : rest) accum
          = dynamicallyFindBestOrder reorderedRest (ind : accum)
          where
            reorderedRest = sortBy bigCountsFirst $ map bumpCountAppropriately rest
            !(rowIndex, colIndex, blockIndex) = calcRCBIndices ind

            -- Add one for each common row, column, and block with the index just taken off the top
            -- of the list.

            bumpCountAppropriately :: (Int, Int) -> (Int, Int)
            bumpCountAppropriately (ind', count) = (ind', newCount)
              where
                newCount = count + incRow + incCol + incBlock
                incRow   = if rowIndex == rowIndex' then 1 else 0
                incCol   = if colIndex == colIndex' then 1 else 0
                incBlock = if blockIndex == blockIndex' then 1 else 0
                !(rowIndex', colIndex', blockIndex') = calcRCBIndices ind'

        -- Sort pairs based on larger counts first, secondarily the index in normal order.

        bigCountsFirst :: (Int, Int) -> (Int, Int) -> Ordering
        bigCountsFirst (ind1, cnt1) (ind2, cnt2)
          = if cnt2 < cnt1 then LT else (if cnt2 > cnt1 then GT else compare ind1 ind2)

        -- Pair the count of the number of set values in each square's row, column, and block

        addCounts :: Int -> (Int, Int)
        addCounts index = (index, (fromIntegral countAll))
          where
            !countAll       = countRowCol + countBlock
            !countRowCol    = countRow + countCol
            !countRow       = rowCounts UV.! rowIndex
            !countCol       = colCounts UV.! colIndex
            !countBlock     = blockCounts UV.! blockIndex
            !(rowIndex, colIndex, blockIndex) = calcRCBIndices index

        -- Populate vectors for rows, columns, and blocks that are just the counts of squares set.

        populateCountInRowColBlock :: SKBoard -> (SKUsedVec, SKUsedVec, SKUsedVec)
        populateCountInRowColBlock board'
          = (UV.generate 9 (\rowInd -> genCount (boardIndicesForRow rowInd)),
             UV.generate 9 (\colInd -> genCount (boardIndicesForCol colInd)),
             UV.generate 9 (\blockInd -> genCount (boardIndicesForBlock blockInd)))
          where
        
            -- Count the number set in the group.

            genCount :: [Int] -> SKUsed
            genCount indices = foldl' countValues 0 indices

            countValues :: SKUsed -> Int -> SKUsed
            countValues acc boardIndex = let boardValue = board' UV.! boardIndex
                                         in if boardValue /= 0 then acc + 1 else acc

    -- Generate the list of empty squares in the current board.

    genEmpties :: SKBoard -> [Int]
    genEmpties board
      = UV.ifoldl' (\acc ind val -> if val == 0 then ind : acc else acc) [] board

    -- From a square index, look up and return the row, column, and block indices.

    calcRCBIndices :: Int -> (Int, Int, Int)
    calcRCBIndices index
      = (skIndexToRow UV.! index, skIndexToCol UV.! index, skIndexToBlock UV.! index)

    -- Generate a new board state given a board vector, which is the part of the board state that
    -- the other data structures are generated from.

    generateBoardStateFromBoard :: SKBoard -> BoardState
    generateBoardStateFromBoard board
      = let (newUsedRow, newUsedCol, newUsedBlock) = populateUsedInRowColBlock
            newEmpties = genEmpties board
        in BoardState {d_board = board, d_usedInRow = newUsedRow, d_usedInCol = newUsedCol,
                       d_usedInBlock = newUsedBlock, d_emptySquares = newEmpties}
      where

        -- Given a board, set the bits in the row, col, and block vectors to indicate what values
        -- are used in each row, column, and block.

        populateUsedInRowColBlock :: (SKUsedVec, SKUsedVec, SKUsedVec)
        populateUsedInRowColBlock
          = (UV.generate 9 (\rowInd -> orValues (boardIndicesForRow rowInd)),
             UV.generate 9 (\colInd -> orValues (boardIndicesForCol colInd)),
             UV.generate 9 (\blockInd -> orValues (boardIndicesForBlock blockInd)))
          where
        
            -- OR together the board values given by the list of indices.

            orValues :: [Int] -> SKUsed
            orValues indices = foldl' orInValueIfNonZero 0 indices

            -- The first argument is the accumulator and the second is the board index.  If the
            -- value on the board is non-zero, then set the bit corresponding to that value in the
            -- accumulator.

            orInValueIfNonZero :: SKUsed -> Int -> SKUsed
            orInValueIfNonZero acc boardIndex
              = let boardValue = board UV.! boardIndex
                in if boardValue /= 0 then acc .|. (shiftL 0x1 (fromIntegral boardValue)) else acc

    -- Generate new board state given the old board state and a list of (index, digit) pairs.  If
    -- there are no squares to update, return the board passed in.

    generateNewBoardState :: BoardState -> SKCellAssignmentList -> BoardState
    generateNewBoardState board [] = board
    generateNewBoardState BoardState {d_board = board} listOfAssignments
      = let newBoard = board UV.// listOfAssignments in generateBoardStateFromBoard newBoard
      
    -- Lock in the squares where there is only a single possibility that is deducable, and repeat
    -- until there are no more single possibilities.  Return the resulting board state along with
    -- the number of loops done and for each loop, the number of squares set.

    lockInDeducableChoices :: BoardState
                           -> (BoardState, Bool, Int, [(Int, Int, Int, [DebugRemovedByStrategies])])
    lockInDeducableChoices bdState = lockInDeducableChoices' bdState 0 []
      where
        lockInDeducableChoices' :: BoardState -> Int -> [(Int, Int, Int, [DebugRemovedByStrategies])]
                                   -> (BoardState, Bool, Int, [(Int, Int, Int, [DebugRemovedByStrategies])])
        lockInDeducableChoices' boardState loopCount deducedCountAccum
          | deducedCount == 0 || null (d_emptySquares newBoardState)
            = (newBoardState, notSolvablePuzzle, loopCount, reverse deducedCountAccum)
          | otherwise = lockInDeducableChoices' newBoardState newLoopCount newDeducedCountAccum
          where
            !newLoopCount = loopCount + 1
            deducedCount = simpleDeducedCount + rcbDeducedCount
            newDeducedCountAccum
              = (simpleDeducedCount, rcbDeducedCount, refining, debugInfoList) : deducedCountAccum
            (newBoardState, notSolvablePuzzle,
               (simpleDeducedCount, rcbDeducedCount, refining, debugInfoList))
                 = findAndSetDeducedEntries boardState
    
    -- Take in a board state, find the squares that only have one choice possible (this is done in
    -- two steps, the first a very simple deduction and the second a more complicated one). Create a
    -- new board state with these set and return it along with the counts of simple and more complex
    -- deduced values.  Also return a boolean value that is set to true if we can figure out that
    -- there are no possible solutions.  This is true if there are squares found with no options or
    -- if there are no more empty squares but the solution is not valid.  This outer call calls the
    -- inner version, which takes an additional parameter indicating whether to do a refining step
    -- when finding the possible options for each square.  This step is more time consuming than the
    -- other things we do, but it can result in progress deducing board square values.  The way it
    -- works is to do the simpler steps to make progress, and if we do, then return a board with
    -- those deductions set.  If no progress is made, then do it again with the refining step and
    -- see if that results in progress.  Another way to think about it is that we do the simple
    -- deductions iteratively until we either solve the puzzle or get stuck.  If we get stuck, then
    -- try the more time-consuming refining step to see if that gets us farther with deductions.
    -- There is a command-line options to always do the refining step.

    findAndSetDeducedEntries :: BoardState
                                -> (BoardState, Bool, (Int, Int, Int, [DebugRemovedByStrategies]))
    findAndSetDeducedEntries boardState
      | notSolvable' || (totalDeductions > 0 && (not . optAlwaysRefine) cmdOptions) = firstResult
      | otherwise = findAndSetDeducedEntries' boardState True
      where
        firstResult@(_, notSolvable', (simpleDeducedCount, rcbDeducedCount, _, _))
          = findAndSetDeducedEntries' boardState False
        !totalDeductions = simpleDeducedCount + rcbDeducedCount
    
    findAndSetDeducedEntries' :: BoardState -> Bool
                                 -> (BoardState, Bool, (Int, Int, Int, [DebugRemovedByStrategies]))
    findAndSetDeducedEntries' boardState@(BoardState {d_emptySquares = []}) _
      = (boardState, False, (0, 0, 0, []))
    findAndSetDeducedEntries' boardState doRefining
      | squaresWithNoOptions || badSolution = (boardState, True, (0, 0, 0, []))
      | otherwise = (finalBoardState, False,
                       (simpleDeducedCount, rcbDeducedCount, refiningSteps, debugInfoList))
      where

        -- Get all of the possible choices for the empty squares on the board.  This is either done
        -- with the very simplest analysis, or if doRefining is set, with a more sophisticated one.

        (possibleChoices1, squaresWithNoOptions, refiningSteps, debugInfoList)
          = generatePossibleChoicesList boardState doRefining

        -- Get the list of pairs (index, digit) with only the one option.  Count them too.

        (simpleDeductions, simpleDeducedCount) = foldl' singleOptionAccum ([], 0) possibleChoices1

        -- Given a set of options deduced for each empty square, the simplest case is where there is
        -- only one possible value for a square because all other values are used in its row,
        -- column, or block.  These were found in the fold above.  Once these are found, we can look
        -- for the case where in any particular row, column, or block, there is only one empty
        -- square where a particular value occurs.  There may be lots of other options, but they
        -- aren't valid because that one value can only go there.  Find these, then generate a new
        -- board state given the simple one-value deductions above and this new set.  We remove the
        -- simple deductions from the second set so we can accurately report how many squares were
        -- deduced with each technique.

        rcbDeductionsOrig = deduceRCBSingleOptions possibleChoices1
        rcbDeductions   = removeSecondFromFirstSorted rcbDeductionsOrig simpleDeductions
        rcbDeducedCount = length rcbDeductions
        finalBoardState = generateNewBoardState boardState (simpleDeductions ++ rcbDeductions)

        -- It may be possible for a puzzle solution to be deduced where the solution is false.  For
        -- example, if a puzzle has only two empty squares, they both lie in a row, and both of the
        -- columns and blocks they are in are missing a 2, for example.  It may be possible, since
        -- they are deduced in one step for them to be both given a 2, which would be an incorrect
        -- solution. This won't happen if there is a DFS stage to searching for the solution, and it
        -- won't happen for a puzzle that has one or more solutions.  In the case where there are no
        -- more empty squares left after the deduction phase, check the result for legality before
        -- returning it.

        finalEmpties = (d_emptySquares finalBoardState)
        finalBoard   = (d_board finalBoardState)
        (goodSolution, _, _, _, _) = checkForValidSudokuPuzzle (convertBoardToByteString finalBoard)
        badSolution = null finalEmpties && not goodSolution

        -- Function to generate a list of possible choices for each empty square on the board.  This
        -- is done first by taking out all of the used digits in each square's row, column, and
        -- block.  There is an additional step where some of these options can be reduced under
        -- limited circumstances, which will be done if refineList is true.  Return also a boolean
        -- indicating whether there were any squares with no options, in which case this puzzle is
        -- unsolvable.

        generatePossibleChoicesList :: BoardState -> Bool
                                       -> (SKOptionsList, Bool, Int, [DebugRemovedByStrategies])
        generatePossibleChoicesList boardState' refineList
          = (possibleChoices, squaresWithNoOptions', refiningSteps', debugInfoList')
          where

            -- From the list of indexes of unfilled squares, generate a list of pairs with the first
            -- element of the pair being the index of the square, and the second the list of
            -- possible options for that square based on removing any digits used in the relevant
            -- row, column, or block.  This is a simple first cut that can be refined.
            -- NOTE: The simplePossibleChoices list must be in reverse square index order, as that
            -- order is expected by refineChoicesBasedOnTriplesWithinBlock.

            simplePossibleChoices = genListValidChoices boardState'
            (possibleChoices, refiningSteps', debugInfoList')
              = if refineList then refiningResult else (simplePossibleChoices, 0, [])

            -- Now refine these possible choices if asked.  Within a block, if there is a row or
            -- column of three where a certain digit option occurs two or three times, and it
            -- doesn't occur in either of the other two parallel rows or columns of three, then we
            -- know that this digit has to occur in this row (if it only occurs once and isn't in
            -- either of the other two rows or columns, then it will be selected by a later step
            -- anyway because it has to be in that one place).  When we identify this situation,
            -- that digit can be removed from the rest of the row or column outside of this block.
            -- This sometimes makes the difference to be able to figure out a value somewhere else.

            refiningResult = refineChoicesBasedOnBlockLinesUntilNoChanges simplePossibleChoices 1 []

            -- See if any squares have no options.

            squaresWithNoOptions'
              = foldl' (\acc (_, options) -> if acc || null options then True else False) False
                       possibleChoices

            -- Take in the list of options for each empty square on the board, and a counter.  It
            -- will return a new options list that potentially has some options removed because it
            -- can be deduced that they are not possible.  This refining step is done iteratively
            -- until no more reductions are possible.  The new list of options is returned along
            -- with a count of the number of refining steps.

            refineChoicesBasedOnBlockLinesUntilNoChanges
              :: SKOptionsList -> Int -> [DebugRemovedByStrategies]
                 -> (SKOptionsList, Int, [DebugRemovedByStrategies])
            refineChoicesBasedOnBlockLinesUntilNoChanges optionsList count debugInfoList''
              | changeMade
                = refineChoicesBasedOnBlockLinesUntilNoChanges reversedRefinedList (count + 1)
                                                               (debugInfo : debugInfoList'')
              | otherwise = (refinedList, count, reverse debugInfoList'')
              where
                (refinedList, changeMade, debugInfo)
                  = removeImpossibleOptionsFromOptionsList cmdOptions optionsList
                reversedRefinedList = reverse refinedList

        -- Go through the list of (index, option) pairs accumulating the ones with just one option
        -- and count these at the same time.  This function is used in a fold operation.

        singleOptionAccum :: (SKCellAssignmentList, Int) -> SKOptions -> (SKCellAssignmentList, Int)
        singleOptionAccum accum@(accumList, accumCount) (index, options)
          = if (not $ null options) && (null $ tail options)
            then ((index, head options) : accumList, accumCount + 1)
            else accum

        -- Given a board and an options list, deduce the necessary digit for any squares where there
        -- is only one place the digit could be in a row, column, or block.  Return the count of
        -- these as well.

        deduceRCBSingleOptions :: SKOptionsList -> SKCellAssignmentList
        deduceRCBSingleOptions emptySquareOptions = rcbList
          where

            -- From the list of empty square options, generate three lists sorted by the respective
            -- RCB index, that hold triples of the RCB index, the board index, and the list of
            -- possible values for that square, based on the values used in the corresponding row,
            -- column, and block.

            rowOptions    = reconfigureForRCB (UV.unsafeIndex skIndexToRow) emptySquareOptions
            colOptions    = reconfigureForRCB (UV.unsafeIndex skIndexToCol) emptySquareOptions
            blockOptions  = reconfigureForRCB (UV.unsafeIndex skIndexToBlock) emptySquareOptions

            -- Get a list of all of the single options, then weed out duplicates.

            rowSingles    = findRCBOnlyOptions [] rowOptions
            rowColSingles = findRCBOnlyOptions rowSingles colOptions
            allSingles    = findRCBOnlyOptions rowColSingles blockOptions
            rcbList       = map head $ group $ sort allSingles

            -- Function to take a list of the options for each empty square, and reconfigure the
            -- data so it can be analyzed for deducable values.  It takes as a first argument a
            -- function that converts the board index to an RCB index, with the caller specifying
            -- which one of the three is wanted (row, column, block).

            reconfigureForRCB :: (Int -> Int) -> SKOptionsList -> [(Int, [(Int, Int)])]
            reconfigureForRCB rcbIndexFn optionList = convertToVecInit [] $ sortBy compareRCBIndex
                                                      $ map (addRCBIndex rcbIndexFn) optionList
              where

                -- Comparison function for sorting based on row, column, or block index in the first
                -- position of the tuple, and secondly on the board index.

                compareRCBIndex :: (Int, Int, [SKBoardElement]) -> (Int, Int, [SKBoardElement])
                                   -> Ordering
                compareRCBIndex (rcb1, bdInd1, _) (rcb2, bdInd2, _)
                  = if compRCB == EQ then compare bdInd1 bdInd2 else compRCB
                  where !compRCB = compare rcb1 rcb2

                -- Map function to convert an (Int, [SKBoardElement]) pair to (Int, Int,
                -- [SKBoardElement]) where the first member of the resulting tuple is the row,
                -- column, or block index.  The second is the board index.  The list is still the
                -- possible options for that square.

                addRCBIndex :: (Int -> Int) -> SKOptions -> (Int, Int, [SKBoardElement])
                addRCBIndex convFuncRCB (ind, options) = (convFuncRCB ind, ind, options)

                -- Convert a sorted list of triples (rcb, board index, [options]) to a list of:
                -- (rcb, [(option, value)] where value is the board index shifted left by 4 anded
                -- with 0x1.  These will later be used to sum for the rcb based on the option to
                -- find individual options that can only go one place in the row, column, or block.
                -- The first parameter is the accumulator and [] should be passed in when called.
        
                convertToVecInit :: [(Int, [(Int, Int)])] -> [(Int, Int, [SKBoardElement])]
                                    -> [(Int, [(Int, Int)])]
                convertToVecInit accum [] = accum
                convertToVecInit accum ((rcb, bdInd, options) : xs)
                  | null options = convertToVecInit accum xs
                  | null accum || currAccRCB /= rcb
                    = convertToVecInit ((rcb, [(firstOption, value)]) : accum)
                                       inputWithRemovedOption
                  | otherwise
                    = convertToVecInit ((currAccRCB, ((firstOption, value) : currAccPairs)) : accums)
                                       inputWithRemovedOption
                  where
                    currAccRCB = fst $ head accum
                    currAccPairs = snd $ head accum
                    accums = tail accum
                    firstOption = fromIntegral $ head options
                    value = (shiftL bdInd 4) .|. 0x1
                    inputWithRemovedOption = ((rcb, bdInd, tail options) : xs)
        
            -- Add all of the values associated with an RCB index into a vector indexed by the option
            -- number.  When done, if any of the option numbers has only one value, then that is the
            -- only choice, so add it to the list of value to set.

            findRCBOnlyOptions :: [(Int, SKBoardElement)] -> [(Int, [(Int, Int)])]
                                    -> [(Int, SKBoardElement)]
            findRCBOnlyOptions accum [] = accum
            findRCBOnlyOptions accum ((_, initList) : xs) = findRCBOnlyOptions newAccum xs
              where
                newAccum = UV.ifoldl' accumSingleUses accum usedOptionsVec
                usedOptionsVec = UV.accum (+) (UV.replicate 10 0) initList
                accumSingleUses :: [(Int, SKBoardElement)] -> Int -> Int -> [(Int, SKBoardElement)]
                accumSingleUses accum' index value
                  = if singleUse then (bdIndex, (fromIntegral index)) : accum' else accum'
                  where
                    bdIndex = shiftR value 4
                    !singleUse = (value .&. 0xF) == 1

    -- Generate valid choices for a list of squares, returning a list of pairs.

    genListValidChoices :: BoardState -> SKOptionsList
    genListValidChoices boardState@(BoardState {d_emptySquares = empties})
      = map (\ind -> (ind, genValidChoices boardState ind)) empties

    -- Given a board and an index, return a list of the valid values that may be used there.  This
    -- is done by using the combination of used in row, column, and block for the given index.  The
    -- known values are stored as bits in d_usedIn[RCB] with the board, and can be ORed together to
    -- generate a set of bits indicating the known values in the related row, column, and block for
    -- the given square.

    genValidChoices :: BoardState -> Int -> [SKBoardElement]
    genValidChoices (BoardState {d_usedInRow = usedRow, d_usedInCol = usedCol,
                                 d_usedInBlock = usedBlock}) index
      = [x | x <- [1..9], testBit validChoiceBits (fromIntegral x)]
      where
        !validChoiceBits = (complement (usedInRow' .|. usedInCol' .|. usedInBlock'))
        !(rowIndex, colIndex, blockIndex) = calcRCBIndices index
        !usedInRow'   = usedRow UV.! rowIndex
        !usedInCol'   = usedCol UV.! colIndex
        !usedInBlock' = usedBlock UV.! blockIndex

    -- Convert the input vector board into a ByteString.

    convertBoardToByteString :: SKBoard -> BC.ByteString
    convertBoardToByteString board = BC.pack stringSolution
      where
        stringSolution = UV.foldr (\x acc -> (intToDigit (fromIntegral x)) : acc) [] board

    -- Do a depth-first search for solutions given the board state, and list of empty square
    -- indexes.  If there are no more empty square indexes, then we have a solution, so convert it
    -- to a string and return it.  Otherwise, for each empty square try each possible value and
    -- recursively call this function given each of those options.  Concatenate any solutions found
    -- together and return them.

    solveSudokuDFS :: BoardState -> Int -> [BC.ByteString] -> [BC.ByteString]
    solveSudokuDFS (BoardState {d_board = currBoard, d_emptySquares = []}) _ solsSoFar
      = (convertBoardToByteString currBoard) : solsSoFar
    solveSudokuDFS
      boardState@(BoardState {d_board = currBoard, d_usedInRow = usedRow, d_usedInCol = usedCol,
                  d_usedInBlock = usedBlock, d_emptySquares = (index : rest)}) emptyCount solsSoFar
      = result
      where

        -- If we are running with the parallel switch, and finding the solution to just one
        -- puzzle, search the options in parallel.  When using the -r option and searching for
        -- related puzzles with one fewer hint, we do the outside search in parallel with the -p
        -- option, so adding parallelism here under those circumstances slows things down.
        -- For the normal search, this code speeds things up about as much as you would expect
        -- given the number of processors, but when run with the +RTS -s option to report
        -- statistics, there are a huge number of sparks that either are GC'ed or fizzled, and
        -- I don't understand why.  I think it would be better to fix that but don't know how.

        result = resultFromHere `pseq` (resultFromHere ++ solsSoFar)
        resultFromHere = if parallelDFS && (dfsDepth - emptyCount) < 15 && emptyCount > 10
                         then (concat (parMap rdeepseq setCurrAndRecurse validChoices))
                         else (concatMap setCurrAndRecurse validChoices)
        validChoices = genValidChoices boardState index

        -- For a given choice for the current square, recursively call this function with
        -- appropriately set used and board vectors.

        setCurrAndRecurse :: SKBoardElement -> [BC.ByteString]
        setCurrAndRecurse value = solveSudokuDFS newBoardState newEmptyCount []
          where
            !newEmptyCount = emptyCount - 1
            !newBoardState = BoardState {d_board = newBoard, d_usedInRow = newUsedRow,
                                         d_usedInCol = newUsedCol, d_usedInBlock = newUsedBlock,
                                         d_emptySquares = rest}
            !(rowIndex, colIndex, blockIndex) = calcRCBIndices index
            newBoard    = currBoard UV.// [(index, value)]
            newUsedRow  = usedRow UV.// [(rowIndex, newRowVal)]
            newUsedCol  = usedCol UV.// [(colIndex, newColVal)]
            newUsedBlock= usedBlock UV.// [(blockIndex, newBlockVal)]
            !newRowVal   = setBit (UV.unsafeIndex usedRow rowIndex) (fromIntegral value)
            !newColVal   = setBit (UV.unsafeIndex usedCol colIndex) (fromIntegral value)
            !newBlockVal = setBit (UV.unsafeIndex usedBlock blockIndex) (fromIntegral value)

-- Take in a list of options for all empty squares on the board, weed out options that are not
-- possible using several techniques (sub-group exclusion, hidden twin/triplet exclusion, lone
-- twin/triplet exclusion, hidden twin chain exclusion, and lone twin chain exclusion), and return
-- the new list of options.  Also return a boolean indicating whether any options were removed or
-- not.

removeImpossibleOptionsFromOptionsList :: CmdOptions -> SKOptionsList
                                          -> (SKOptionsList, Bool, DebugRemovedByStrategies)
removeImpossibleOptionsFromOptionsList cmdOptions optionList
  = (weededOptionList, changeMade, debugInfo)
  where

    -- From the options list passed in, weed out any unneeded options that were discovered.  Note
    -- whether there were any removed, as that fact is returned and used to decide if another pass
    -- should be done.

    (weededOptionList, changeMade) = weedOutUnneededOptions optionList sortedRemovesMerged ([], False)

    -- We use various techniques to find options that are not possible for particular squares.  Each
    -- of these techniques returns a list of pairs where the first element of the pair is a list of
    -- board indexes (in sorted order), and the second is a list of options (sorted) that can be
    -- removed from those board squares.  The lists from each technique are concatenated together
    -- and expanded, then all merged together with duplicates removed resulting in a list of pairs
    -- with the first element a board square index, and the second a list of the options that can be
    -- removed from it.  Note that the vast majority of these options don't exist in the original
    -- options list anyway.  The list is sorted in reverse order by board index, which matches the
    -- sort order of the options list passed in to this function.

    sortedRemovesMerged = mergeSameIndices sortedRemoves
    sortedRemoves = sortBy (\(ind1, _) (ind2, _) -> compare ind2 ind1) unsortedRemoves
    unsortedRemoves = foldl' expandList [] listToRemoveFromAllStrategies

    -- Here we concatenate all of the lists of entries to remove from each of the strategies tried
    -- in this function.

    -- Generate the lists of puzzle options to remove based on the command line flags. Normally, we
    -- concatenate all of these together, but to allow working on these strategies in isolation, we
    -- can turn them on or off at the command line. The result list here is the list of values
    -- after being turned on or off by these command line options. Admittedly, this is kind of
    -- awkward, but it seemed the best way. Note that the names of the lists in the result are the
    -- same names as go in, but with a 'M' at the end indicating "maybe", as in maybe there or not.

    listToRemoveFromAllStrategies = concat listOfListsToRemoveFromAllStrategies
    listOfListsToRemoveFromAllStrategies@[subgroupExclusionRowsM, subgroupExclusionColsM,
         rowOptsToRemoveTwinTripM, colOptsToRemoveTwinTripM, blockOptsToRemoveTwinTripM,
         rowOptsToRemoveTwoChainsM, colOptsToRemoveTwoChainsM, blockOptsToRemoveTwoChainsM,
         rowOptsToRemoveTwoHiddenChainsM, colOptsToRemoveTwoHiddenChainsM,
         blockOptsToRemoveTwoHiddenChainsM, rowEntriesToRemoveXWingM, colEntriesToRemoveXWingM,
         blockEntriesToRemoveXWingM]
      = zipWith retEmptyOrListBasedOnDebugFlag listOfRefiningOptions
        [subgroupExclusionRows, subgroupExclusionCols, rowOptsToRemoveTwinTrip,
          colOptsToRemoveTwinTrip, blockOptsToRemoveTwinTrip, rowOptsToRemoveTwoChains,
          colOptsToRemoveTwoChains, blockOptsToRemoveTwoChains, rowOptsToRemoveTwoHiddenChains,
          colOptsToRemoveTwoHiddenChains, blockOptsToRemoveTwoHiddenChains, rowEntriesToRemoveXWing,
          colEntriesToRemoveXWing, blockEntriesToRemoveXWing]

    -- Function to run the given command option function on the command options and return the list
    -- passed in if true, and an empty list if not.

    retEmptyOrListBasedOnDebugFlag :: (CmdOptions -> Bool) -> SKOptionsToRemove -> SKOptionsToRemove
    retEmptyOrListBasedOnDebugFlag flagFn toRemoveList
      | flagFn cmdOptions = toRemoveList
      | otherwise = []

    -- Return all of the list of removed options for potential debug reporting.

    debugInfo = DebugRemovedByStrategies (sort optionList) weededOptionList sortedRemovesMerged
                  subgroupExclusionRowsM subgroupExclusionColsM
                  rowOptsToRemoveTwinTripM colOptsToRemoveTwinTripM
                  blockOptsToRemoveTwinTripM rowOptsToRemoveTwoChainsM
                  colOptsToRemoveTwoChainsM blockOptsToRemoveTwoChainsM
                  rowOptsToRemoveTwoHiddenChainsM colOptsToRemoveTwoHiddenChainsM
                  blockOptsToRemoveTwoHiddenChainsM rowEntriesToRemoveXWingM
                  colEntriesToRemoveXWingM blockEntriesToRemoveXWingM

    -- These are the options to be removed from rows or columns where there is an option that occurs
    -- only in one row or column within a block, so it must be one of these and can be removed from
    -- the remainder of the row or column outisde the block.  This also captures the reverse
    -- situation where an option occurs in a row or column in a block, but not in the corresponding
    -- rows or columns connected that are outside the block.  In this case, the option can be
    -- removed from the other rows or columns within the block.

    subgroupExclusionRows = genSubgroupExclusionRemovalList optionList Row
    subgroupExclusionCols = genSubgroupExclusionRemovalList optionList Col

    -- A vector the size of the whole board holding the number of options for each square.

    optionCount :: UV.Vector Int
    optionCount
      = UV.accum (+) (UV.replicate cellCount 0) $ map (\(i, opts) -> (i, length opts)) optionList

    -- Separate the option list based on the 9 rows, columns, and blocks.  These are useful for
    -- later processing.

    sepRowLists   = separateOptionListIntoRCBVector skIndexToRow
    sepColLists   = separateOptionListIntoRCBVector skIndexToCol
    sepBlockLists = separateOptionListIntoRCBVector skIndexToBlock

    -- Function to separate the option list into a vector of option lists indexed by the RCB number,
    -- the vector for which is passed in.

    separateOptionListIntoRCBVector :: SKConvertVec -> V.Vector SKOptionsList
    separateOptionListIntoRCBVector elemIndexToRCBIndexVec
      = V.accum (flip (:)) (V.replicate rcbCount []) $ map addRCBIndexForVectorInd optionList
      where
        addRCBIndexForVectorInd :: SKOptions -> (Int, SKOptions)
        addRCBIndexForVectorInd (ind, opt) = (elemIndexToRCBIndexVec UV.! ind, (ind, opt))

    -- Generate a vector of counts based on the number of times each number option appears in an
    -- option list in the row, column, or block.

    rowOptionCounts, colOptionCounts, blockOptionCounts :: RCBOptionCounts
    rowOptionCounts   = V.map countTotalRCBOptions sepRowLists
    colOptionCounts   = V.map countTotalRCBOptions sepColLists
    blockOptionCounts = V.map countTotalRCBOptions sepBlockLists

    -- Function to count the number of times an option appears in an option list associated with the
    -- given row, column, or block.

    countTotalRCBOptions :: SKOptionsList -> OptionCounts
    countTotalRCBOptions xs = V.accum (+) (V.replicate vecSizeForOpts 0) (prepListForAccum xs)
      where
        prepListForAccum :: SKOptionsList -> [(Int, Int)]
        prepListForAccum options = (map (\x -> ((fromIntegral x), 1)) . concatMap snd) options

    -- RCB lists of options to remove due to chains of exactly two.

    rowOptsToRemoveTwoChains   = genTwoChainRemovalList optionCount rowOptionCounts
                                                        sepRowLists boardIndicesForRow
    colOptsToRemoveTwoChains   = genTwoChainRemovalList optionCount colOptionCounts
                                                        sepColLists boardIndicesForCol
    blockOptsToRemoveTwoChains = genTwoChainRemovalList optionCount blockOptionCounts
                                                        sepBlockLists boardIndicesForBlock

    -- RCB lists of options to remove due to hidden chains where the options occur exactly twice.

    rowOptsToRemoveTwoHiddenChains   = genTwoHiddenChainRemovalList rowOptionCounts sepRowLists
    colOptsToRemoveTwoHiddenChains   = genTwoHiddenChainRemovalList colOptionCounts sepColLists
    blockOptsToRemoveTwoHiddenChains = genTwoHiddenChainRemovalList blockOptionCounts sepBlockLists

    -- These hold lists of pairs of lists.  The first list in a pair is the board
    -- squares to remove from, and the second list holds the options that can be removed
    -- from them.  These must be in sorted order.

    rowOptsToRemoveTwinTrip   = genTwinTripRemovalList Row optionCount
                                                       rowOptionCounts sepRowLists
    colOptsToRemoveTwinTrip   = genTwinTripRemovalList Col optionCount
                                                       colOptionCounts sepColLists
    blockOptsToRemoveTwinTrip = genTwinTripRemovalList Block optionCount
                                                       blockOptionCounts sepBlockLists

    -- The options to remove for the X-Wing pattern.
    -- Generate the X-Wing removal lists separately.

    rowEntriesToRemoveXWing   = genXWingPatternRemovalList optionList Row
    colEntriesToRemoveXWing   = genXWingPatternRemovalList optionList Col
    blockEntriesToRemoveXWing = genXWingPatternRemovalList optionList Block

    -- Both input lists are assumed to be reverse-sorted by board square index.  The first is the
    -- current options list, and the second is a list of options that can be removed.  The third
    -- parameter is a pair used to accumulate the weeding done, and from outside it should be given
    -- an empty list and false.  This function will return the new list and True if anything was
    -- actually weeded out.

    weedOutUnneededOptions :: SKOptionsList -> SKOptionsList -> (SKOptionsList, Bool)
                              -> (SKOptionsList, Bool)
    weedOutUnneededOptions [] _ result = result
    weedOutUnneededOptions list1 [] (accum, changed) = (accum ++ (reverse list1), changed)
    weedOutUnneededOptions list1@((ind1, options1) : xs1)
                           list2@((ind2, options2) : xs2) accResult@(accum, changed)
      | ind1 == ind2 = weedOutUnneededOptions xs1 xs2 (((ind1, weededOptions) : accum), newChanged)
      | ind1 > ind2  = weedOutUnneededOptions xs1 list2 (((ind1, options1) : accum), changed)
      | otherwise = weedOutUnneededOptions list1 xs2 accResult
      where
        weededOptions = removeSecondFromFirstSorted options1 options2
        newChanged = changed || (not (options1 == weededOptions))

genTwoChainRemovalList :: UV.Vector Int -> RCBOptionCounts -> V.Vector SKOptionsList
                          -> (Int -> [Int]) -> SKOptionsToRemove
genTwoChainRemovalList optionCount rcbOptionCounts sepRCBLists boardIndicesForRCB = result
  where

    result = V.ifoldl' (convertToOptsToRemoveExactlyTwoChains boardIndicesForRCB) [] rcbTwoChains

    rcbTwoChains = V.zipWith filterTwoOptions sepRCBLists rcbOptionCounts

    -- Convert from a list of chains to a list of options to remove.

    convertToOptsToRemoveExactlyTwoChains :: (Int -> [Int]) -> SKOptionsToRemove -> Int
                                             -> [SKOptionsList] -> SKOptionsToRemove
    convertToOptsToRemoveExactlyTwoChains _ acc _ [] = acc
    convertToOptsToRemoveExactlyTwoChains bdIndsForRCB acc ind (tripletList : tripletRest)
      = convertToOptsToRemoveExactlyTwoChains bdIndsForRCB newAcc ind tripletRest
      where
        !newAcc = currRemoveOpts : acc
        currRemoveOpts = (LO.minus (bdIndsForRCB ind) (fst currGoodOpts), snd currGoodOpts)
        currGoodOpts = foldl' accumIndsAndOpts ([], []) tripletList

    -- Take in a list of options and the option counts for this RCB, and return a list of option
    -- lists, where each is a set of three board indices paired with two options each that pair
    -- together in a chain.

    filterTwoOptions :: SKOptionsList -> OptionCounts -> [SKOptionsList]
    filterTwoOptions optList optionCounts = pairChains
      where
        pairChains = findPairChains [] (listOfTwoToPair filteredForTwoAndGreater)
        filteredForTwoAndGreater = filter twoWithAllOptsTwoOrGreater optList
        twoWithAllOptsTwoOrGreater :: SKOptions -> Bool
        twoWithAllOptsTwoOrGreater (bdIndex, opts)
          | optionCount UV.! bdIndex /= 2 = False
          | isJust $ find (\x -> (optionCounts V.! (fromIntegral x)) < 2) opts = False
          | otherwise = True

genTwoHiddenChainRemovalList :: RCBOptionCounts -> V.Vector SKOptionsList -> SKOptionsToRemove
genTwoHiddenChainRemovalList rcbOptionCounts sepRCBLists = result
  where

    result = V.ifoldl' convertToOptsToRemoveHiddenTwoChains [] rcbTwoHiddenChains

    -- RCB vector containing squares and option lists where the option lists  are hidden chains of
    -- two.

    rcbTwoHiddenChains = V.zipWith filterTwoOptionsHidden sepRCBLists rcbOptionCounts

    -- Convert from a list of chains to a list of options to remove.

    convertToOptsToRemoveHiddenTwoChains :: SKOptionsToRemove -> Int -> [SKOptionsList]
                                            -> SKOptionsToRemove
    convertToOptsToRemoveHiddenTwoChains acc _ [] = acc
    convertToOptsToRemoveHiddenTwoChains acc ind (tripletList : tripletRest)
      = convertToOptsToRemoveHiddenTwoChains newAcc ind tripletRest
      where
        !newAcc = currRemoveOpts : acc
        currRemoveOpts = (fst currGoodOpts,
                          LO.minus [(fromIntegral minCellVal)..(fromIntegral maxCellVal)]
                                   (snd currGoodOpts))
        currGoodOpts = foldl' accumIndsAndOpts ([], []) tripletList

    filterTwoOptionsHidden :: SKOptionsList -> OptionCounts -> [SKOptionsList]
    filterTwoOptionsHidden optList optionCounts
      | length optionsExactlyTwo < 3  || length optsFilteredForTwo < 3 = []
      | otherwise = pairChains
      where
        pairChains = findPairChains [] ((listOfTwoToPair . combOptionPairs) optsFilteredForTwo)
        optsFilteredForTwo = filterOnlyOptionsOccurringTwice optList
        optionsExactlyTwo = V.ifoldr' (\ind val acc -> if val == 2 then ind : acc else acc)
                                      [] optionCounts
        combOptionPairs :: SKOptionsList -> SKOptionsList
        combOptionPairs [] = []
        combOptionPairs ((bdInd, opts) : xs)
          | length opts < 3 = (bdInd, opts) : convertedRest
          | otherwise = spreadEntries ++ convertedRest
          where
            convertedRest = combOptionPairs xs
            spreadEntries = map (\ys -> (bdInd, ys)) listOfPairs
            listOfPairs = listOfAllListPairsSameOrder opts
        filterOnlyOptionsOccurringTwice :: SKOptionsList -> SKOptionsList
        filterOnlyOptionsOccurringTwice [] = []
        filterOnlyOptionsOccurringTwice ((bdInd, opts) : xs)
          | length newOpts >= 2 = (bdInd, newOpts) : filteredRest
          | otherwise = filteredRest
          where
            filteredRest = filterOnlyOptionsOccurringTwice xs
            newOpts = LO.isect (map fromIntegral optionsExactlyTwo) opts

-- Accumulate the board indices and options into a pair of lists given SKOptions.

accumIndsAndOpts :: ([Int], [SKBoardElement]) -> SKOptions -> ([Int], [SKBoardElement])
accumIndsAndOpts (currBdInds, currOpts) (bdInd, opts) = (newBdInds, newOpts)
  where
    newBdInds = LO.insertSet bdInd currBdInds
    newOpts = foldl' (\acc x -> LO.insertSet x acc) currOpts opts

-- Look for circular chains of pairs, e.g. [2,5], [9,2], [5,9].

findPairChains :: [SKOptionsList] -> [SKOptionsPair] -> [SKOptionsList]
findPairChains acc optList'
  | length optList' < 3 = acc
  | bdX == bdY = downTheLine
  | x1 == y1 = findPairChainOneMatch downTheLine x2 y2 [xs, ys] zs
  | x1 == y2 = findPairChainOneMatch downTheLine x2 y1 [xs, ys] zs
  | x2 == y1 = findPairChainOneMatch downTheLine x1 y2 [xs, ys] zs
  | x2 == y2 = findPairChainOneMatch downTheLine x1 y1 [xs, ys] zs
  | otherwise = downTheLine
  where
    (xs@(bdX, (x1, x2)) : ys@(bdY, (y1, y2)) : zs) = optList'
    downTheLineX = findPairChains acc (xs : zs)
    downTheLine = findPairChains downTheLineX (ys : zs)
    findPairChainOneMatch :: [SKOptionsList] -> SKBoardElement -> SKBoardElement
                          -> [SKOptionsPair] -> [SKOptionsPair] -> [SKOptionsList]
    findPairChainOneMatch acc' _ _ _ [] = acc'
    findPairChainOneMatch acc' match1 match2 partial (zFull@(bdZ, (z1, z2)) : zs')
      | (bdZ /= bdY) && (bdZ /= bdX) && ((match1 == z1 && match2 == z2)
        || (match1 == z2 && match2 == z1)) = ((pairsToLists (zFull : partial)) : acc')
      | otherwise = findPairChainOneMatch acc' match1 match2 partial zs'

    -- Convert a list of pairs of options to an options list.

    pairsToLists :: [SKOptionsPair] -> SKOptionsList
    pairsToLists [] = []
    pairsToLists ((bdInd, (o1, o2)) : rest) = (bdInd, [o1, o2]) : (pairsToLists rest)

-- Convert an options list to a list of pairs.

listOfTwoToPair :: SKOptionsList -> [SKOptionsPair]
listOfTwoToPair [] = []
listOfTwoToPair ((bdInd, opts) : xs)
  = ((bdInd, (head opts, head $ tail opts))) : listOfTwoToPair xs

genTwinTripRemovalList :: RCB_t -> UV.Vector Int -> RCBOptionCounts -> V.Vector SKOptionsList
                          -> SKOptionsToRemove
genTwinTripRemovalList rcbType optionCount rcbOptionCounts sepRCBLists = result
  where

    result = V.foldl' (accumOptsToRemoveTwinTrip skIndexToRCB boardIndicesForRCB) []
                      rcbTwinsTriplets

    -- Use the appropriate data for row, column, or block.

    (skIndexToRCB, boardIndicesForRCB)
      | rcbType == Row   = (skIndexToRow, boardIndicesForRow)
      | rcbType == Col   = (skIndexToCol, boardIndicesForCol)
      | rcbType == Block = (skIndexToBlock, boardIndicesForBlock)
      | otherwise = error "Bad RCB type in genTwinTripRemovalList."

    -- RCB vectors containing pairs holding a list of lone twins and a list of hidden twins.  The
    -- twins are stored as a list of pairs, with the first a list of the twin or triplet options,
    -- and the second, the board indexes they are found in.  We can remove different entries based
    -- on whether we have twins all by themselves or hidden twins/triplets.

    rcbTwinsTriplets = V.zipWith3 harvestUsefulTwinsTriplets rcbOptPairMap rcbOptTripleMap
                                  rcbOptionCounts

    -- RCB vectors containing maps of triplets of options to the list of squares with that triplet
    -- of options.

    rcbOptTripleMap = V.map createOptionTripletMap sepRCBLists

    -- RCB vectors containing maps of pairs of options to the list of squares with that pair of
    -- options.

    rcbOptPairMap = V.map createOptionPairMap sepRCBLists

    -- Accumulate options to remove from the list of lone twins and triples and the list of hidden
    -- twins and triples.

    accumOptsToRemoveTwinTrip :: SKConvertVec -> (Int -> [Int]) -> SKOptionsToRemove
                                 -> MapAccumulator -> SKOptionsToRemove
    accumOptsToRemoveTwinTrip boardIndToRCB rCBIndexToBoards acc (loneSets, hiddenSets) = newAcc
      where
        newLoneAcc = foldl' convertLoneSets acc loneSets
        newAcc = foldl' convertHiddenSets newLoneAcc hiddenSets
        convertLoneSets :: SKOptionsToRemove -> ([Int], [Int]) -> SKOptionsToRemove
        convertLoneSets currAcc (values, bdIndices) = (indicesFrom, convValues) : currAcc
          where
            indicesFrom = LO.minus' (rCBIndexToBoards (boardIndToRCB UV.! (head bdIndices)))
                                    (reverse bdIndices)
            convValues = map fromIntegral values
        convertHiddenSets :: SKOptionsToRemove -> ([Int], [Int]) -> SKOptionsToRemove
        convertHiddenSets currAcc (values, bdIndices)
          = (reverse bdIndices, map fromIntegral (LO.minus' [0..maxRCBInd] values)) : currAcc

    -- This function will work its way through the map of pairs and the map of triples associated
    -- with each RCB group and will accumulate the ones where there is a set of lone twins or
    -- triples, and the ones where there are two hidden twins or three hidden triples.  These will
    -- then be used to decide which options can be removed from which squares.

    harvestUsefulTwinsTriplets :: MapPairs -> MapTriples -> OptionCounts -> MapAccumulator
    harvestUsefulTwinsTriplets twinMap tripletMap optionCounts = combinedResult
      where
        combinedResult = M.foldlWithKey idTwins tripletResult twinMap
        tripletResult  = M.foldlWithKey idTriples ([], []) tripletMap

        -- Convert pairs and triples to lists so they can be processed by the same function.

        idTwins :: MapAccumulator -> (Int, Int) -> (Int, [Int]) -> MapAccumulator
        idTwins currAcc (twin1, twin2) countAndBdInds
          = idEitherWithList 2 currAcc [twin1, twin2] countAndBdInds
        idTriples :: MapAccumulator -> (Int, Int, Int) -> (Int, [Int]) -> MapAccumulator
        idTriples currAcc (trip1, trip2, trip3) countAndBdInds
          = idEitherWithList 3 currAcc [trip1, trip2, trip3] countAndBdInds
        idEitherWithList :: Int -> MapAccumulator -> [Int] -> (Int, [Int]) -> MapAccumulator
        idEitherWithList num currAccum@(loneAcc, hiddenAcc) opts (count, bdInds)
          | count < num = currAccum
          | (length loneTwinTripInds) == num
            = let !newLoneAcc = (opts, ((reverse . sort) loneTwinTripInds)) : loneAcc
                  !newAcc = (newLoneAcc, hiddenAcc)
              in newAcc
          | count /= num = currAccum
          | isNothing (find (\opt -> (optionCounts V.! opt) /= num) opts)
            = let !newHiddenAcc = (opts, ((reverse . sort) bdInds)) : hiddenAcc
                  !newAcc = (loneAcc, newHiddenAcc)
              in newAcc
          | otherwise = currAccum
          where loneTwinTripInds = filter (\ind -> (optionCount UV.! ind) == num) bdInds

    -- Given a list of options associated with board square indexes, create a map of all possible
    -- pairs of options for a board square in the list.  Lump all board squares together in the map,
    -- but the value in the map is the list of squares having that pair.

    createOptionTripletMap :: SKOptionsList -> MapTriples
    createOptionTripletMap xs = foldl' storeTriplets M.empty xs
      where
        storeTriplets :: MapTriples -> SKOptions -> MapTriples
        storeTriplets currMap (bdInd, options) = newMap
          where
            newMap = foldl' storeTriplets' currMap (listOfAllTriplesSameOrder intOptions)
            intOptions = map fromIntegral options
            storeTriplets' :: MapTriples -> (Int, Int, Int) -> MapTriples
            storeTriplets' inMap pair = M.insertWith combiner pair (1, [bdInd]) inMap
            combiner :: (Int, [Int]) -> (Int, [Int]) -> (Int, [Int])
            combiner (cnt1, xs1) (cnt2, xs2)
              = let !sumCount = cnt1 + cnt2; !newList = (head xs1) : xs2
                in (sumCount, newList)

    -- Given a list of options associated with board square indexes, create a map of all possible
    -- pairs of options for a board square in the list.  Lump all board squares together in the map,
    -- but the value in the map is the list of squares having that pair.

    createOptionPairMap :: SKOptionsList -> MapPairs
    createOptionPairMap xs = foldl' storePairs M.empty xs
      where
        storePairs :: MapPairs -> SKOptions -> MapPairs
        storePairs currMap (bdInd, options) = newMap
          where
            newMap = foldl' storePairs' currMap (listOfAllPairsSameOrder intOptions)
            intOptions = map fromIntegral options
            storePairs' :: MapPairs -> (Int, Int) -> MapPairs
            storePairs' inMap pair = M.insertWith combiner pair (1, [bdInd]) inMap
            combiner :: (Int, [Int]) -> (Int, [Int]) -> (Int, [Int])
            combiner (cnt1, xs1) (cnt2, xs2)
              = let !sumCount = cnt1 + cnt2; !newList = (head xs1) : xs2
                in (sumCount, newList)

genSubgroupExclusionRemovalList :: SKOptionsList -> RCB_t -> SKOptionsToRemove
genSubgroupExclusionRemovalList optionsList rcbType
  | rcbType == Row || rcbType == Col = UV.ifoldl' (findOptionsToRemove inBlockData) [] inBlockData
  | otherwise = error "Bad rcb type to genSubgroupExclusionRemovalList."
  where

    -- Merge the bit vectors representing options from an individual board square into one each for
    -- each small row or column within a block.  These are merged by adding, so each group of three
    -- bits represents the number of times that option is included in the mini-row or column.  It
    -- can be 0-4.

    inBlockData = UV.accum (+) (UV.replicate 27 0) initList

    -- Lists of unordered pairs containing the index of a row or column in a block, and a bit vector
    -- with bits set for the options from the board square.  There may be more than one of the same
    -- mini-row or column index, and these will be later merged.

    initList = convertToBlockRCUsedList appropriateBoardIndexToBlockIndex optionsList []
    appropriateBoardIndexToBlockIndex
      | isRow = boardIndexToBlockRowIndex
      | otherwise = boardIndexToBlockColIndex

    isRow = rcbType == Row

    -- Used in a fold operation to find cases where an option in only included in one row or
    -- column in a block.  It takes in the vector containing all of the bit vectors for the
    -- mini-rows or columns in blocks, a boolean indicating if this is for rows or columns,
    -- an accumulator list of results, the current vector index, and the bit vector
    -- corresponding with this vector index.

    findOptionsToRemove :: UV.Vector Int -> [([Int], [SKBoardElement])] -> Int -> Int
                           -> [([Int], [SKBoardElement])]
    findOptionsToRemove fullBlockRCData accum vIndex value

      -- If none of the options in this mini-row or column in a block occur more than once,
      -- or if there are no options to remove because options occur in other mini-rows or
      -- columns, then we just return the accumulator passed in.

      | (value .&. maskTwoOrThreeCounts == 0)
        || ((null optionsToRemoveBlock) && (null optionsToRemovePar)) = accum

      -- Here there are options to remove, so prepend them to the accumulator.

      | (not (null optionsToRemoveBlock)) && (not (null optionsToRemovePar))
          = (boardIndexListBlock, optionsToRemoveBlock)
            : (boardIndexListPar, optionsToRemovePar) : accum
      | not (null optionsToRemoveBlock)
          = (boardIndexListBlock, optionsToRemoveBlock) : accum
      | otherwise = (boardIndexListPar, optionsToRemovePar) : accum
      where

        -- Walk through the possible options accumulating any that can be removed.

        (optionsToRemovePar, optionsToRemoveBlock)
            = foldl' accumKeepableOptions ([], []) [1..9]

        -- Get the other two mini-rows or columns in the block, and from the indices get the
        -- bit vectors for each that have the options available in them.

        [otherRC1Index, otherRC2Index] = blockRCIndexToOthersInBlock UA.! vIndex
        otherRC1 = fullBlockRCData UV.! otherRC1Index
        otherRC2 = fullBlockRCData UV.! otherRC2Index

        -- Get the other two mini-rows or columns in line with this one that are not in the
        -- same block, and from these indices, get the bit vectors associated with them.

        [otherParRC1Index, otherParRC2Index] = if isRow
                                               then blockRCIndexToInLineRows UA.! vIndex
                                               else blockRCIndexToInLineCols UA.! vIndex
        otherParRC1 = fullBlockRCData UV.! otherParRC1Index
        otherParRC2 = fullBlockRCData UV.! otherParRC2Index

        -- Get the list of board squares that is outside of the block we are looking at but
        -- that are in line with the mini-row or column we are looking at.

        boardIndexListPar = (if isRow then inLineSquaresWithBlockRow
                                      else inLineSquaresWithBlockCol) UA.! vIndex

        -- Get the list of board squares that are in the same block we are looking at but
        -- not in the current mini-row or column.

        boardIndexListBlock = (if isRow then otherBlockSquaresThanMiniRow
                                        else otherBlockSquaresThanMiniCol) UA.! vIndex

        -- Look at the current option (1-9), and see if it occurs two or three times in the
        -- current block row or column, determined by masking with the bit that would be set
        -- if this had been added two or three times.  If so, and if it doesn't occur in
        -- either of the other row or columns in the block, then add it to the list.
        -- Alternatively, if there are two or three and there aren't any in the other
        -- mini-rows or columns in line with this one, then we can remove it from the
        -- parallel rows or columns in the block.

        accumKeepableOptions :: ([SKBoardElement], [SKBoardElement]) -> Int
                             -> ([SKBoardElement], [SKBoardElement])
        accumKeepableOptions acc@(accBlock, accPar) option
          | secondBitForOption /= 0 && otherRCBitsNotSet
            = ((fromIntegral option) : accBlock, accPar)
          | secondBitForOption /= 0 && otherParRCBitsNotSet
            = (accBlock, (fromIntegral option) : accPar)
          | otherwise = acc
          where
            secondBitForOption = (shiftL 0x1 (2 * option + 1)) .&. value
            bitsForThisOption = shiftL 0x3 (2 * option)
            otherRC1Masked = otherRC1 .&. bitsForThisOption
            otherRC2Masked = otherRC2 .&. bitsForThisOption
            otherRCBitsNotSet = otherRC1Masked == 0 && otherRC2Masked == 0
            otherParRC1Masked = otherParRC1 .&. bitsForThisOption
            otherParRC2Masked = otherParRC2 .&. bitsForThisOption
            otherParRCBitsNotSet = otherParRC1Masked == 0 && otherParRC2Masked == 0

    -- This function takes in a vector to convert board indices to indices for the rows
    -- or columns (depends on the vector passed in), within blocks.  It also takes a
    -- list of options (boardIndex, options), and an accumulator.  It will return a list
    -- of pairs containing first the index of a small row or column in a block, and
    -- second, a bit vector indicating with set bits which options came from the board
    -- square for this entry.  There can be up to three entries per small row or column
    -- in a block, and they won't be in any particular order.  The bits in the bit
    -- vector indicating options are separated by two bits, which leaves room for
    -- their later use.  For example, if a particular board square has options [1, 2,
    -- 4], the bit vector will hold 0b100010100.

    convertToBlockRCUsedList :: UV.Vector Int -> SKOptionsList -> [(Int, Int)]
                                -> [(Int, Int)]
    convertToBlockRCUsedList _ [] accum = accum
    convertToBlockRCUsedList convVec ((boardIndex, options) : xs) accum
      = convertToBlockRCUsedList convVec xs newAccum
      where
        newAccum = addOptPairs (convVec UV.! boardIndex) options accum
        addOptPairs :: Int -> [SKBoardElement] -> [(Int, Int)] -> [(Int, Int)]
        addOptPairs _ [] acc = acc
        addOptPairs blockRCIndex (element : elements) acc
          = let !doubleElement = 2 * (fromIntegral element)
                !shiftedOption = shiftL 0x1 doubleElement
                !rcIndexShiftedOptionPair = (blockRCIndex, shiftedOption)
                !newAcc = rcIndexShiftedOptionPair : acc
            in addOptPairs blockRCIndex elements newAcc

-- Generate list of options to remove for the X-Wing pattern, given the RCB type for the X and
-- the current options list for the board.

genXWingPatternRemovalList :: SKOptionsList -> RCB_t -> SKOptionsToRemove
genXWingPatternRemovalList optionsList rcbType = genOneTypeXWingList []
  where

    -- Set some objects that differ depending on the RCB type.  These are used by the inner
    -- functions.

    (mainConvRCB, firstConvRCB, secondConvRCB, firstBdIndForRCB, secondBdIndForRCB)
      | rcbType == Row = (skToRow, skToCol, skToBlock, boardIndicesForCol, boardIndicesForBlock)
      | rcbType == Col = (skToCol, skToRow, skToBlock, boardIndicesForRow, boardIndicesForBlock)
      | otherwise      = (skToBlock, skToRow, skToCol, boardIndicesForRow, boardIndicesForCol)
    skToRow n   = skIndexToRow   UV.! n
    skToCol n   = skIndexToCol   UV.! n
    skToBlock n = skIndexToBlock UV.! n

    -- Generate the list of removals given an accumulator.

    genOneTypeXWingList :: SKOptionsToRemove -> SKOptionsToRemove
    genOneTypeXWingList acc = resultOptionsToRemove
      where
        resultOptionsToRemove = foldl' findXWings acc entryPairsGrouped
        entryPairsGrouped :: [[(MapRCBAndValKey, MapRCBAndValEntry)]]
        entryPairsGrouped = filterAndGroupByOption optionInfoMap
        optionInfoMap :: MapRCBAndVal
        optionInfoMap = foldl' accEntry M.empty optionsList
    
    -- Search through the list of grouped (option, RCB) pairs looking for matches, and when found,
    -- generate the options we can remove.

    findXWings :: SKOptionsToRemove -> [(MapRCBAndValKey, MapRCBAndValEntry)]
                  -> SKOptionsToRemove
    findXWings acc entries = foldl' checkPair acc (pairsOrdered entries)
      where
        checkPair :: SKOptionsToRemove
                     -> ((MapRCBAndValKey, MapRCBAndValEntry), (MapRCBAndValKey, MapRCBAndValEntry))
                     -> SKOptionsToRemove
        checkPair acc' (((opt, _), (_, list1)), ((_, _), (_, list2))) = accWithSecondPair
          where

            -- These will be lists of length 2 of RCB numbers (0-8).  If we are working with row
            -- x-wings, then the first will be column numbers and the second block numbers, for
            -- example.

            sList1RCBFirst   = (sort . map firstConvRCB)  list1
            sList1RCBSecond  = (sort . map secondConvRCB) list1
            sList2RCBFirst   = (sort . map firstConvRCB)  list2
            sList2RCBSecond  = (sort . map secondConvRCB) list2
            bdIndsForFirst   = (sort . concatMap firstBdIndForRCB) sList1RCBFirst
            bdIndsForSecond  = (sort . concatMap secondBdIndForRCB) sList1RCBSecond
            sortedBdInds     = sort (list1 ++ list2)
            firstBdIndsAll   = removeSecondFromFirstSorted bdIndsForFirst  sortedBdInds
            secondBdIndsAll  = removeSecondFromFirstSorted bdIndsForSecond sortedBdInds
            accWithFirstPair  = if sList1RCBFirst == sList2RCBFirst
                                then (firstBdIndsAll, [opt]) : acc'
                                else acc'
            accWithSecondPair = if sList1RCBSecond == sList2RCBSecond
                                then (secondBdIndsAll, [opt]) : accWithFirstPair
                                else accWithFirstPair

    -- Take in a map and return a list of lists containing RCB entries with option number.

    filterAndGroupByOption = (filter (\lis -> tail lis /= [])
                              . groupBy (\((n, _), _) ((m, _), _) -> n == m)
                              . filter (\(_, (cnt, _)) -> cnt == 2) . M.toAscList)

    -- Accumulate (option, RCB) pairs in a map holding the count of how many there are along with a
    -- list of board indices where they are.

    accEntry :: MapRCBAndVal -> SKOptions -> MapRCBAndVal
    accEntry inMap (sqIndex, options) = foldl' addOptionToMap inMap options
      where
        mainConvIndex = mainConvRCB sqIndex
        addOptionToMap :: MapRCBAndVal -> SKBoardElement -> MapRCBAndVal
        addOptionToMap inMap' opt = M.insertWith combineFn key entry inMap'
          where
            key = (opt, mainConvIndex)
            entry = (1, [sqIndex])
            combineFn (addCount, addIndList) (accCount, accList) = newPair
              where !newCount = addCount + accCount
                    !indToAdd = head addIndList
                    !newIndList = indToAdd : accList
                    !newPair = (newCount, newIndList)

-- Just print out the board as one long string of digits.

printBoardBrief :: BC.ByteString -> IO ()
printBoardBrief board = do
  putStr "    "
  BC.putStrLn board

-- Print out the board in a textual Sudoku grid.

printBoardFull :: BC.ByteString -> IO ()
printBoardFull board = do
  printWithFormatting 0
  where
    limitIndex = ((BC.length board) - 3)
    printWithFormatting index
      | index > limitIndex = return ()
      | otherwise = do
        printCharsSepSpace index 3
        let newIndex = index + 3
        printSeparator newIndex
        printWithFormatting newIndex

    printCharsSepSpace :: Int -> Int -> IO ()
    printCharsSepSpace _ 0 = return ()
    printCharsSepSpace index count = do
      putChar (BC.index board index); putChar ' ';
      printCharsSepSpace (index + 1) (count - 1)
                                      
    printSeparator :: Int -> IO ()
    printSeparator n
      | n == 27 || n == 54 || n == 81 = putStrLn "\n"
      | n `rem` 9 == 0 = putStrLn ""
      | otherwise = putStr "  "

-- Print a heading for the board, and the board in either brief or full.

printBoard :: String -> Bool -> Bool -> BC.ByteString -> IO ()
printBoard heading brief indent solution = do
  putStrLn $ (if indent then "  " else "") ++ heading
  if brief
  then printBoardBrief solution
  else printBoardFull  solution

-- Used to print a series of solutions in a foldM.

printPuzzleSolutions :: Bool -> Int -> BC.ByteString -> IO (Int)
printPuzzleSolutions brief accum solution = do
  let newAccum = accum + 1
  printBoard ("Solution " ++ show newAccum ++ ":") brief brief solution
  return (newAccum)

-- Either there is a pathname to a file with puzzles or a list of puzzles was supplied directly.
-- Return whichever list of puzzles there are. If this is a file full of puzzles, ignore empty
-- lines and lines beginning with "--".

getPuzzles :: String -> [String] -> IO ([BC.ByteString])
getPuzzles inFile cmdLinePuzzles
  | null cmdLinePuzzles = do
    fileContents <- BC.readFile inFile
    let bcPuzzleLines = (filter notComment . BC.lines) fileContents
    return bcPuzzleLines
  | otherwise = return (map BC.pack cmdLinePuzzles)
  where
    commentPrefix = BC.pack "--"
    notComment bcLine = (BC.length firstTwoNonSpace /= 0) && not isComment
      where
        firstTwoNonSpace = (BC.take 2 . BC.dropWhile isSpace) bcLine
        isComment = firstTwoNonSpace == commentPrefix

-- Find and print related harder puzzles with a single solution.

findRelatedHarderPuzzles :: CmdOptions -> String -> IO (Int)
findRelatedHarderPuzzles cmdOptions puzzle = do
  putStrLn "Original puzzle:"
  putStrLn $ "  " ++ puzzle
  putStrLn "Progress..."
  putStr "  "
  hFlush stdout
  let doParSearch = optParSearch cmdOptions
  if doParSearch
  then do

    -- For a parallel search, we report progress based on puzzles with one fewer hint, so reporting
    -- is done in bursts, stopping at the first non '0' after a removable hint, although since it
    -- is done in parallel, the pauses usually jump past more than one removable hint.

    let puzzlesToTry = genAllPuzzlesWithOneLessFilledSquare puzzle
        puzzlesWithOneSolBool = parMap rpar solutionIsOne puzzlesToTry
        puzzlesWithOneSolPairs = zip puzzlesWithOneSolBool puzzlesToTry
        puzzlesWithOneSolFilt = filter (\(bVal, _) -> bVal) puzzlesWithOneSolPairs
        puzzlesWithOneSol = map (\(_, puzz) -> puzz) puzzlesWithOneSolFilt
        puzzlesWithOneSolAndCount = map addHintCount puzzlesWithOneSol
        emptiesAtStart = takeWhile (== '0') puzzle
        emptyCountAtStart = length emptiesAtStart
    putStr emptiesAtStart
    hFlush stdout
    (_, remainingPuzzle)
      <- foldM reportParallelProgress (emptyCountAtStart, drop emptyCountAtStart puzzle)
               puzzlesWithOneSol
    putStrLn $ remainingPuzzle ++ "\n"
    putStrLn "Puzzles having one solution and one more empty cell:"
    _ <- mapM putStrLn puzzlesWithOneSolAndCount
    return (length puzzlesWithOneSolAndCount)
  else do

    -- Report progress for each cell of the puzzle. While doParSearch is passed here,
    -- it will always be false.

    relatedStringsWithOneSolution <- findSingleSolutionDerivativesIO cmdOptions doParSearch puzzle
    let relatedStringsWithOneSolAndCount = map addHintCount relatedStringsWithOneSolution
    putStrLn "\n"
    putStrLn "Puzzles having one solution and one more empty cell:"
    _ <- mapM putStrLn (reverse relatedStringsWithOneSolAndCount)
    return (length relatedStringsWithOneSolAndCount)
  where
    reportParallelProgress :: (Int, String) -> String -> IO (Int, String)
    reportParallelProgress (count, remainingPuzzle) puzzleMissingHint = do
      let puzzleMissingHintPrefixChopped = drop count puzzleMissingHint
          countToDiff = findCountToDiff 1 remainingPuzzle puzzleMissingHintPrefixChopped
          findCountToDiff :: Int -> String -> String -> Int
          findCountToDiff cnt xs ys
            | (null xs) || (null ys) = 0  -- This should never happen.
            | (head xs) /= (head ys) = skipNextBlanks cnt (tail xs) (tail ys)
            | otherwise = let newCnt = cnt + 1
                          in newCnt `seq` findCountToDiff newCnt (tail xs) (tail ys)
          skipNextBlanks cnt xs ys
            | (null xs) || (null ys) || ((head ys) /= '0') = cnt
            | otherwise = let newCnt = cnt + 1
                          in newCnt `seq` skipNextBlanks newCnt (tail xs) (tail ys)
      putStr (take countToDiff remainingPuzzle)
      hFlush stdout
      return ((count + countToDiff, drop countToDiff remainingPuzzle))
    addHintCount :: String -> String
    addHintCount sol = sol ++ " (" ++ show (length $ filter (\x -> x /= '0') sol) ++ ")"
    solutionIsOne :: String -> Bool
    solutionIsOne puzzle' = singleSolution
      where
        singleSolution = (not $ null solutions) && (null $ tail solutions)

        -- I tried passing doParSearch here, but it slowed things down, which surprised
        -- me.  It's probably because there is too much fine-grain parallelism?

        (solutions, _) = solveSudoku cmdOptions False (BC.pack puzzle')

-- Solve the given puzzle.  Expected to be used in a fold operation, and will accumulate the total
-- number of puzzles and solutions.

solvePuzzle :: CmdOptions -> (Int, Int) -> BC.ByteString -> IO ((Int, Int))
solvePuzzle cmdOptions (accumTotalPuzzles, accumTotalSolutions) puzzle = do
  let (validPuzzle, rowErrors, colErrors, blockErrors, (rightLength, puzzleLength))
        = checkForValidSudokuPuzzle puzzle
      brief = (optBrief cmdOptions)
      doParSearch = optParSearch cmdOptions
      indentStr = (if brief then "  " else "")
  if (not validPuzzle)
  then do

    -- If there were errors in this puzzle, report the duplicated digits.

    if (not rightLength)
    then putStrLn $ indentStr ++ "Puzzle must be " ++ show cellCount
                    ++ " characters long, but this has " ++ show puzzleLength ++ " characters."
    else do
      printBoard "Initial board state:" brief False puzzle
      putStrLn $ indentStr ++ "Invalid puzzle configuration."
      when (not $ null rowErrors)
        (putStrLn $ indentStr ++ "  Repeated entries in rows (row, digit): " ++ show rowErrors)
      when (not $ null colErrors)
        (putStrLn $ indentStr ++ "  Repeated entries in columns (col, digit): " ++ show colErrors)
      when (not $ null blockErrors)
        (putStrLn $ indentStr ++ "  Repeated entries in blocks (block, digit): " ++ show blockErrors)
    return (accumTotalPuzzles, accumTotalSolutions)
  else do

    -- Find and report the solution(s) to this puzzle and give the time taken.

    printBoard "Initial board state:" brief False puzzle
    startTime <- getTime Realtime
    let (solutions, debugInfo) = solveSudoku cmdOptions doParSearch puzzle
    solutionCount <- foldM (printPuzzleSolutions brief) 0 solutions
    endTime <- getTime Realtime
    when (solutionCount == 0) (putStrLn $ indentStr ++ "Puzzle has no solutions.")
    let diff = computeElapsedTime startTime endTime
    printf "  Solve time: %0.4f sec.\n" (diff :: Double)
    when ((optDebug cmdOptions) == 1) $ do

      -- Here we do some simple debug printing.

      let printFn = printStringWithNewlineByMax 7 maxDebugLineLen
      new1Loc <- printFn 0 ("    Dbg(Dfs: " ++ show (d_dfsDepth debugInfo)
                            ++ " Iters: " ++ show (d_deduceLoops debugInfo) ++ " -> ")

      -- Create strings representing the list of iterations to solve the puzzle. Remove last comma.

      let iterStrings = map (\(a, b, c, _) -> show (a, b, c) ++ ",") (d_deducedCounts debugInfo)
          iterStringsR = reverse iterStrings
          lastStr = head iterStringsR
          iterStringsToPrint = (reverse . ((init lastStr) :) . tail) iterStringsR
      foldM_ printFn new1Loc ((if null (d_deducedCounts debugInfo)
                               then [] else iterStringsToPrint) ++ [")\n"])
    when ((optDebug cmdOptions) == 2) $ do

      -- Here we do some extensive debug printing.

      let indent  = 4
          extraIndent = 2
      putStrLn $ mconcat ["  Extensive debug -> Dfs: ", show (d_dfsDepth debugInfo), " Iters: ",
                          show (d_deduceLoops debugInfo)]

      -- Now print detail for each solve iteration.

      foldM_ (printIteration cmdOptions indent extraIndent) 1 (d_deducedCounts debugInfo)

    -- Free up any memory used during the solving of this puzzle.

    performGC
    return ((accumTotalPuzzles + 1, accumTotalSolutions + solutionCount))

-- Print extensive debug information about the given solve iteration, including the options reduced
-- by each kind of refining option. Takes in an iteration number and returns it incremented.

printIteration :: CmdOptions -> Int -> Int -> Int -> (Int, Int, Int, [DebugRemovedByStrategies])
                  -> IO (Int)
printIteration cmdOptions indent extraIndent iterNumber (simpDed, rcbDed, refineLoops, refineDetail)
  = do
    putStr $ (replicate indent ' ')
    putStr $ "Iter: " ++ show iterNumber ++ " Simple: " ++ show simpDed ++ " RCB: " ++ show rcbDed
             ++ " Refine Loops: " ++ show refineLoops
    putStrLn ""
    foldM_ (printRefineDetail cmdOptions (indent + extraIndent) extraIndent) 1 refineDetail
    return (iterNumber + 1)

-- Take in two lists of cell numbers and related options and return the intersection.

genCommonNumbers :: SKOptionsList -> SKOptionsList -> SKOptionsList
genCommonNumbers [] _ = []
genCommonNumbers _ [] = []
genCommonNumbers currAll@((currCell, currOpt) : currRest) remAll@((remCell, remOpt) : remRest)
  | currCell < remCell = genCommonNumbers currRest remAll
  | currCell > remCell = genCommonNumbers currAll remRest
  | null commonOpts = resultFromHereWithWhatsLeft
  | otherwise = (currCell, commonOpts) : resultFromHereWithWhatsLeft
  where
    commonOpts = LO.isect currOpt remOpt
    resultFromHereWithWhatsLeft = genCommonNumbers currRest remRest

-- Print out extensive detail about the solving process.

printRefineDetail :: CmdOptions -> Int -> Int -> Int -> DebugRemovedByStrategies -> IO (Int)
printRefineDetail cmdOptions indent extraIndent iterNumber refineDetail = do
  let indentStr = replicate indent ' '
      indentExtStr = replicate (indent + extraIndent) ' '
      optList = d_optionList refineDetail
      weededOptList = d_weededOptionsList refineDetail

      -- Take a list of refining numbers and organize them by square and if asked, take out all of
      -- the ones that aren't helpful to reduce the actual options.

      makeFriendlyList refinedList
        | (optExtendedAll cmdOptions) = friendlyList
        | otherwise = genCommonNumbers optList friendlyList
        where
          friendlyList = (mergeSameIndices . sortOn fst . foldl' expandList []) refinedList

      -- Indent the printing of some options along with the label for them.

      printOptionsLine name optionsList = do
        putStrLn $ mconcat [indentExtStr, name, ": ", show optionsList]

      -- Get the list of removable options from a specific refining step, make the list friendly
      -- for printing, and print it if it's non-null.

      printRefineListIfNonNull (getFn, idString) = do
        let printableList = makeFriendlyList (getFn refineDetail)
        unless (null printableList) $ printOptionsLine idString printableList

  -- Detail the refining done in this iteration. Print out the option list for each empty square and
  -- the same list with any refining options eliminated. There is an additional option to not print
  -- these two because they can be quite long. Then print out all individual refining steps where at
  -- least one option was eliminated.

  putStrLn $ indentStr ++ "Refine iter: " ++ show iterNumber
                                           
  unless (null optList || not (optExtendedOptionList cmdOptions))
    (putStrLn $ mconcat [indentExtStr, "OptionList: ", show optList])
  unless (null weededOptList || not (optExtendedOptionList cmdOptions))
    (putStrLn $ mconcat [indentExtStr, "WeededOptList: ", show weededOptList])

  -- Print out all of the refining options that found options to eliminate.

  mapM_ printRefineListIfNonNull $ zip listOfDebugRefiningLists namesOfRefiningLists
  return (iterNumber + 1)

-- Write a string to stdout. If the length of this string plus the current line location is greater
-- than the maximum length, start a new line with the given indent spaces.

printStringWithNewlineByMax :: Int -> Int -> Int -> String -> IO Int
printStringWithNewlineByMax indent maxLoc currLoc str
  | currLoc + lenStr <= maxLoc = do
      putStr str
      return (currLoc + lenStr)
  | otherwise = do
      putStrLn ""
      putStr $ (replicate indent ' ') ++ str
      return (indent + lenStr)
  where
    lenStr = length str

main :: IO ()
main = do
  (cmdOptions, cmdLinePuzzles) <- parseArgs

  -- Check that puzzles are specified either in a file or on the command line.

  when ((optReqSearch cmdOptions) && (null cmdLinePuzzles))
    (ioError (userError "Error: Puzzle must be specified to search for related puzzles."))
  when ((optInFile cmdOptions) /= "" && (not $ null cmdLinePuzzles))
    (ioError (userError "Error: Puzzles specified both in a file and the command line."))
  when ((optInFile cmdOptions) == "" && null cmdLinePuzzles)
    (ioError (userError "Error: No Sudoku puzzles to solve."))

  if (optReqSearch cmdOptions)
  then do

    let puzzleToUse = head cmdLinePuzzles
    let (validPuzzle, rowErrors, colErrors, blockErrors, (rightLength, puzzleLength))
          = checkForValidSudokuPuzzle (BC.pack puzzleToUse)

    if (not validPuzzle)
    then do

      -- If there were errors in this puzzle, report the duplicated digits.

      if (not rightLength)
      then putStrLn $ "  Puzzle must be " ++ show cellCount ++ " characters long, but this has "
                      ++ show puzzleLength ++ " characters."
      else do
        putStrLn $ "Invalid puzzle configuration."
        when (not $ null rowErrors)
          (putStrLn $ "  Repeated entries in rows (row, digit): " ++ show rowErrors)
        when (not $ null colErrors)
          (putStrLn $ "  Repeated entries in columns (col, digit): " ++ show colErrors)
        when (not $ null blockErrors)
          (putStrLn $ "  Repeated entries in blocks (block, digit): " ++ show blockErrors)
      return ()
    else do
      startTime <- getTime Realtime
      numberFound <- findRelatedHarderPuzzles cmdOptions puzzleToUse
      endTime <- getTime Realtime

      putStrLn $ "\nPuzzles found with one solution and one fewer filled element: "
                 ++ show numberFound

      let diff = computeElapsedTime startTime endTime
      printf "Total time: %0.4f sec.\n" (diff :: Double)

  else do
        
    -- Get the list of puzzles from either the file or command line.

    puzzles <- getPuzzles (optInFile cmdOptions) cmdLinePuzzles

    -- Measure the time to solve all of the puzzles given to us.

    startTime <- getTime Realtime
    (totalPuzzles, totalSolutions) <- foldlM (solvePuzzle cmdOptions) (0, 0) puzzles
    endTime <- getTime Realtime

    putStrLn $ "\nTotal puzzles: " ++ show totalPuzzles ++
               " Total solutions: " ++ show totalSolutions

    let diff = computeElapsedTime startTime endTime
    printf "Total time: %0.4f sec.\n" (diff :: Double)

-- Defines the record used to hold command line options.  This is filled in and processed by the
-- commands in the getOpt package. When any refining options are added, they should also be added
-- to listOfRefiningOptions (in order), to defaultOptions, and to refineControl.

data CmdOptions = CmdOptions {
    optVersion                :: Bool
  , optBrief                  :: Bool
  , optHelp                   :: Bool
  , optDebug                  :: Int
  , optExtendedAll            :: Bool
  , optExtendedOptionList     :: Bool
  , optInFile                 :: String
  , optReqSearch              :: Bool
  , optParSearch              :: Bool
  , optAlwaysRefine           :: Bool
  , optUseSubExclusionRows    :: Bool
  , optUseSubExclusionCols    :: Bool
  , optUseTwinTripRows        :: Bool
  , optUseTwinTripCols        :: Bool
  , optUseTwinTripBlocks      :: Bool
  , optUseTwoChainsRows       :: Bool
  , optUseTwoChainsCols       :: Bool
  , optUseTwoChainsBlocks     :: Bool
  , optUse2HiddenChainsRows   :: Bool
  , optUse2HiddenChainsCols   :: Bool
  , optUse2HiddenChainsBlocks :: Bool
  , optUseXWingRows           :: Bool
  , optUseXWingCols           :: Bool
  , optUseXWingBlocks         :: Bool
  } deriving Show

-- This is a list of the refining options accessor functions for CmdOptions. These should be in the
-- same order as defined in the CmdOptions record. Add to this list when any new refining steps are
-- added.
-- Note that if a new refining option is added, the function refineControl must be updated.

listOfRefiningOptions :: [(CmdOptions -> Bool)]
listOfRefiningOptions
  = [optUseSubExclusionRows, optUseSubExclusionCols, optUseTwinTripRows, optUseTwinTripCols,
     optUseTwinTripBlocks, optUseTwoChainsRows, optUseTwoChainsCols, optUseTwoChainsBlocks,
     optUse2HiddenChainsRows, optUse2HiddenChainsCols, optUse2HiddenChainsBlocks,
     optUseXWingRows, optUseXWingCols, optUseXWingBlocks]
  
-- Default options when not specified.

defaultOptions :: CmdOptions
defaultOptions = CmdOptions {
    optVersion                = False
  , optBrief                  = False
  , optHelp                   = False
  , optDebug                  = 0
  , optExtendedAll            = False
  , optExtendedOptionList     = False
  , optInFile                 = ""
  , optReqSearch              = False
  , optParSearch              = False
  , optAlwaysRefine           = False
  , optUseSubExclusionRows    = True
  , optUseSubExclusionCols    = True
  , optUseTwinTripRows        = True
  , optUseTwinTripCols        = True
  , optUseTwinTripBlocks      = True
  , optUseTwoChainsRows       = True
  , optUseTwoChainsCols       = True
  , optUseTwoChainsBlocks     = True
  , optUse2HiddenChainsRows   = True
  , optUse2HiddenChainsCols   = True
  , optUse2HiddenChainsBlocks = True
  , optUseXWingRows           = True
  , optUseXWingCols           = True
  , optUseXWingBlocks         = True
  }

-- This function describes all of the options.  Each entry contains the short option flags,
-- specified like -b, and the long option flags, specified like -brief.  It also has a short
-- description of the option, which is used by the usageInfo function to generate a help message for
-- the program.  The third entry is a tuple that describes whether the option has no argument, an
-- optional one, or a required one.  It also has a value that is returned in a list from the getOpts
-- function.  Normally this would just be a value or enumeration, but the idea here is a little more
-- clever.  We return a function, that may have a value bound into it, such as the one for help.
-- This function is monadic, and takes and returns an option record.  The idea is that when the
-- getOpts function returns a list of these functions, then they can be processed using foldlM, and
-- each will set the approprate value of the option record, which will start out with the default
-- values.  Each function will also do any appropriate error checking.

-- The function takes a parameter, which is the help text that is used with the help option.
-- Interesting because the help text is generated by calling this function with an empty string and
-- sending it to usageInfo.

cmdOptionsFn :: String -> [OptDescr (CmdOptions -> IO CmdOptions)]
cmdOptionsFn optionDescription =
  [ Option ['v'] ["version"]
    (NoArg (\_ -> do
                  progName <- getProgName
                  putStr $ progName
                  putStrLn $ ", version " ++ version
                  exitSuccess))
    "print the program version"
  , Option ['h', 'u'] ["help", "usage"]
    (NoArg (\_ -> do
                  putStr optionDescription
                  exitSuccess))
    "print usage and help text"
  , Option ['b'] ["brief"]
    (NoArg (\opts -> do
                  return $ opts {optBrief = True}))
    "print Sudoku boards as a single line"
  , Option ['d'] ["debug"]
    (NoArg (\opts -> do
                  return $ opts {optDebug = 1}))
    "print debugging info about the solving process"
  , Option ['e'] ["extensive"]
    (NoArg (\opts -> do
                  return $ opts {optDebug = 2}))
    "print extensive debugging info about the solving process"
  , Option ['a'] ["all"]
    (NoArg (\opts -> do
                  return $ opts {optExtendedAll = True}))
    "for extensive debugging, print all, not just useful refines"
  , Option ['o'] ["optlist"]
    (NoArg (\opts -> do
                  return $ opts {optExtendedOptionList = True}))
    "for extensive debugging, print initial and weeded options lists"
  , Option ['f'] ["file"]
    (ReqArg (\str opts -> do
                  return $ opts {optInFile = str}) "FILE")
    "input file of puzzle strings (one per line)"
  , Option ['r'] ["reduce"]
    (NoArg (\opts -> do
                  return $ opts {optReqSearch = True}))
    "puzzle to find harder related puzzles with one solution"
  , Option ['p'] ["parallel"]
    (NoArg (\opts -> do
                  return $ opts {optParSearch = True}))
    "use parallelism both with normal search and with the -r option"
  , Option [] ["aref"]
    (NoArg (\opts -> do
               return $ opts {optAlwaysRefine = True}))
    "always do the refining step at each iteration"
  , Option [] ["twintrip"]
    (ReqArg (refineControl "twintrip") "a|r|c|b")
    "turn on twin-triple refining for all, row, column, or block"
  , Option [] ["twochains"]
    (ReqArg (refineControl "twochains") "a|r|c|b")
    "turn on two-chains refining for all, row, column, or block"
  , Option [] ["twohiddenchains"]
    (ReqArg (refineControl "twohiddenchains") "a|r|c|b")
    "turn on two-hidden-chains refining for all, row, column, or block"
  , Option [] ["xwing"]
    (ReqArg (refineControl "xwing") "a|r|c|b")
    "turn on x-wing refining for all, row, column, or block"
  , Option [] ["subexclusion"]
    (ReqArg (refineControl "subexclusion") "a|r|c")
    "turn on sub-exclusion refining for all, row, or block"
  ]

-- Take in a command option related to turning on one or more refining steps for row, column, block,
-- or all, and set the appropriate command option flags. Since by default, all of these are turned
-- on, the first of these that is encountered on the command line will turn them all off first, then
-- that flag and any further related flags will turn just those refining parts on.
-- There should be a more consice way to do this, but I can't figure out what it is.

refineControl :: String -> String -> CmdOptions -> IO CmdOptions
refineControl refKind str opts
  | errorInStr strL = do
      putStrLn "Refine option must be: a, r, c, or b."
      return opts
  | refKind == "subexclusion" && strL == "r" = return $ updatedOpts {optUseSubExclusionRows = True}
  | refKind == "subexclusion" && strL == "c" = return $ updatedOpts {optUseSubExclusionCols = True}
  | refKind == "subexclusion" && strL == "a"
    = return $ updatedOpts {optUseSubExclusionRows = True, optUseSubExclusionCols = True}
  | refKind == "twintrip" && strL == "r" = return $ updatedOpts {optUseTwinTripRows = True}
  | refKind == "twintrip" && strL == "c" = return $ updatedOpts {optUseTwinTripCols = True}
  | refKind == "twintrip" && strL == "b" = return $ updatedOpts {optUseTwinTripBlocks = True}
  | refKind == "twintrip" && strL == "a"
    = return $ updatedOpts {optUseTwinTripRows = True, optUseTwinTripCols = True,
                            optUseTwinTripBlocks = True}
  | refKind == "twochains" && strL == "r" = return $ updatedOpts {optUseTwoChainsRows = True}
  | refKind == "twochains" && strL == "c" = return $ updatedOpts {optUseTwoChainsCols = True}
  | refKind == "twochains" && strL == "b" = return $ updatedOpts {optUseTwoChainsBlocks = True}
  | refKind == "twochains" && strL == "a"
    = return $ updatedOpts {optUseTwoChainsRows = True, optUseTwoChainsCols = True,
                            optUseTwoChainsBlocks = True}
  | refKind == "twohiddenchains" && strL == "r" = return $ updatedOpts {optUse2HiddenChainsRows = True}
  | refKind == "twohiddenchains" && strL == "c" = return $ updatedOpts {optUse2HiddenChainsCols = True}
  | refKind == "twohiddenchains" && strL == "b" = return $ updatedOpts {optUse2HiddenChainsBlocks = True}
  | refKind == "twohiddenchains" && strL == "a"
    = return $ updatedOpts {optUse2HiddenChainsRows = True, optUse2HiddenChainsCols = True,
                            optUse2HiddenChainsBlocks = True}
  | refKind == "xwing" && strL == "r" = return $ updatedOpts {optUseXWingRows = True}
  | refKind == "xwing" && strL == "c" = return $ updatedOpts {optUseXWingCols = True}
  | refKind == "xwing" && strL == "b" = return $ updatedOpts {optUseXWingBlocks = True}
  | refKind == "xwing" && strL == "a"
    = return $ updatedOpts {optUseXWingRows = True, optUseXWingCols = True,
                            optUseXWingBlocks = True}
  | otherwise = do  -- This shouldn't happen.
      putStrLn "Unknown refining option."
      return opts
  where
    strL = map toLower str
    updatedOpts
      | allRefiningOptsOn = turnOffAllRefiningOptions
      | otherwise = opts
    allRefiningOptsOn = and $ zipWith (\fn op -> fn op) listOfRefiningOptions (repeat opts)
    turnOffAllRefiningOptions
      = opts {optUseSubExclusionRows = False, optUseSubExclusionCols = False,
              optUseTwinTripRows = False, optUseTwinTripCols = False, optUseTwinTripBlocks = False,
              optUseTwoChainsRows = False, optUseTwoChainsCols = False,
              optUseTwoChainsBlocks = False, optUse2HiddenChainsRows = False,
              optUse2HiddenChainsCols = False, optUse2HiddenChainsBlocks = False,
              optUseXWingRows = False, optUseXWingCols = False, optUseXWingBlocks = False}
    errorInStr rcb
      | rcb == "r" = False
      | rcb == "c" = False
      | rcb == "b" = if refKind == "subexclusion" then True else False
      | rcb == "a" = False
      | otherwise = True

parseArgs :: IO (CmdOptions, [String])
parseArgs = do
  argv     <- getArgs
  progName <- getProgName

  -- The header for the help message is written by me, but the options are described using the
  -- usageInfo function called with the header and the command options.
  
  let helpHeader
        = "This program will solve Sudoku puzzles with '-' for empty and 1-9 for values.\n"
          ++ "Usage: " ++ progName ++ " [OPTION...] puzzle..."
      helpMessage = usageInfo helpHeader (cmdOptionsFn "")
      optionTemplate = cmdOptionsFn helpMessage
      (optFuncs, otherArgs, errs) = getOpt RequireOrder optionTemplate argv
      errorsFound = not $ null errs

  -- If errors were found while parsing the options, report them and then generate the help message.

  when errorsFound (ioError (userError (concat errs ++ "\n" ++ helpMessage)))

  -- Take the default options record, call each of the parameter functions returned by getOpt on it
  -- successively, and this will result in the option record with the user-specified options set.
  -- This can also be done with this line, but it seems less clear to me: optionRecord <- foldlM
  -- (flip id) defaultOptions opts

  optionRecord <- foldlM (\acc fn -> (fn acc)) defaultOptions optFuncs
  return (optionRecord, otherArgs)
