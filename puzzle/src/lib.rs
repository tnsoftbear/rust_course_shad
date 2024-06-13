#![forbid(unsafe_code)]

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

////////////////////////////////////////////////////////////////////////////////

/// Represents a tile on a board. A tile can either be empty or a number from 1 to 8.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Tile(u8);

impl Tile {
    /// Creates a new tile.
    ///
    /// # Arguments
    ///
    /// * `maybe_value` - Some(1..=8) or None.
    ///
    /// # Panics
    ///
    /// Panics if value is 0 or > 8.
    pub fn new(maybe_value: Option<u8>) -> Self {
        match maybe_value {
            Some(value @ 1..=8) => Self(value),
            None => Self(0),
            Some(v) => panic!("Tile value must be 1,2,3,4,5,6,7,8, get: {v}")
        }
    }

    /// Creates an empty tile.
    pub fn empty() -> Self {
        Self(0)
    }

    /// Returns `Some(value)` if tile contains a value, otherwise returns `None`.
    pub fn number(&self) -> Option<u8> {
        match self.0 {
            1..=8 => Some(self.0),
            _ => None
        }
    }

    /// Returns true if tile does not contain a value.
    pub fn is_empty(&self) -> bool {
        self.number().is_none()
    }
}

impl fmt::Display for Tile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let binding = self.0.to_string();
        let str = match &self.0 {
            0 => ".",
            _ => &binding
        };
        write!(f, "{str}")
    }
}

////////////////////////////////////////////////////////////////////////////////

/// Represents a 3x3 board of tiles.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Board {
    tiles: [[Tile; 3]; 3],
}

impl Board {
    /// Creates a new `Board` from a 3x3 matrix if `Tile`s.
    ///
    /// # Panics
    ///
    /// Panics if `tiles` contains more than one instance if some tile.
    pub fn new(tiles: [[Tile; 3]; 3]) -> Self {
        let mut existing_tiles: HashSet<Tile> = HashSet::new();
        for col in 0..3 {
            for row in 0..3 {
                if existing_tiles.contains(&tiles[row][col]) {
                    panic!("Unexpected tile")
                }
                existing_tiles.insert(tiles[row][col]);
            }
        }

        // Alternatively:
        // let set = tiles
        //     .iter()
        //     .flatten()
        //     // .cloned()// С cloned() тип результата будет `HashSet<Tile>`, а не `HashSet<&Tile>`
        //     .collect::<HashSet<_>>();
        // assert_eq!(set.len(), 9, "Wrong tiles");

        Self {
            tiles
        }
    }

    /// Returns a tile on a given `row` and `col`.
    ///
    /// # Panics
    ///
    /// Panics if `row` or `col` > 2.
    pub fn get(&self, row: usize, col: usize) -> Tile {
        self.tiles[row][col]
    }

    /// Swaps two given tiles.
    ///
    /// # Panics
    ///
    /// Panics if some of `r1`, `r2`, `c1` or `c2` > 2.
    pub fn swap(&mut self, r1: usize, c1: usize, r2: usize, c2: usize) {
        let tile_tmp = self.get(r1, c1);
        self.tiles[r1][c1] = self.get(r2, c2);
        self.tiles[r2][c2] = tile_tmp;
    }

    /// Parses `Board` from string.
    ///
    /// # Arguments
    ///
    /// * `s` must be a string in the following format:
    ///
    /// '''
    /// .12
    /// 345
    /// 678
    /// '''
    ///
    /// # Panics
    ///
    /// Panics of `s` is the wrong format or does not represent a valid `Board`.
    pub fn from_string(s: &str) -> Self {
        let mut tiles : [[Tile; 3]; 3] = [[Tile::empty(); 3]; 3];
        for (row, line) in s.split("\n").enumerate() {
            for (col, ch) in line.chars().enumerate() {
                tiles[row][col] = match ch {
                    '.' => Tile::empty(),
                    v @ '1'..='8' => Tile::new(Some(v.to_digit(10).unwrap() as u8)),
                    v => panic!("Unexpected character: {}", v)
                }
            }
        }
        Self::new(tiles)
    }

    /// Returns a string representation of this board in the following format:
    ///
    /// '''
    /// .12
    /// 345
    /// 678
    /// '''
    pub fn to_string(&self) -> String {
        let mut result: String = String::new();
        for row in 0..3 {
            for col in 0..3 {
                let tile = &self.get(row, col);
                result += &tile.to_string();
            }
            result += "\n";
        }
        result
    }

    pub fn find_empty_pos(&self) -> (usize, usize) {
        for row in 0..3 {
            for col in 0..3 {
                if self.get(row, col).is_empty() {
                    return (row, col)
                }
            }
        }
        panic!("No empty tile on board")
    }

    pub fn find_neighbour_boards_for_empty_pos(&self) -> Vec<Self> {
        let (empty_pos_row, empty_pos_col) = self.find_empty_pos();
        let mut neighbour_positions: HashSet<(usize, usize)> = HashSet::new();
        if empty_pos_row > 0 {
            neighbour_positions.insert((empty_pos_row - 1, empty_pos_col));
            if empty_pos_col > 0 {
                neighbour_positions.insert((empty_pos_row, empty_pos_col - 1));
            }
            if empty_pos_col < 2 {
                neighbour_positions.insert((empty_pos_row, empty_pos_col + 1));
            }
        }
        if empty_pos_row < 2 {
            neighbour_positions.insert((empty_pos_row + 1, empty_pos_col));
            if empty_pos_col > 0 {
                neighbour_positions.insert((empty_pos_row, empty_pos_col - 1));
            }
            if empty_pos_col < 2 {
                neighbour_positions.insert((empty_pos_row, empty_pos_col + 1));
            }
        }
        let mut neighbour_boards : Vec<Self> = vec![];
        for (neighbour_row, neighbour_col) in neighbour_positions {
            let mut neighbour_board = self.clone();
            neighbour_board.swap(empty_pos_row, empty_pos_col, neighbour_row, neighbour_col);
            neighbour_boards.push(neighbour_board);
        }
        neighbour_boards
    }

    pub fn is_final(&self) -> bool {
        let final_board = Board::from_string(
            "123\n\
             456\n\
             78.\n"
        );
        return &final_board == self
    }
}

////////////////////////////////////////////////////////////////////////////////

/// Returns the shortest sequence of moves that solves this board.
/// That is, a sequence of boards such that each consecutive board can be obtained from
/// the previous one via a single swap of an empty tile with some adjacent tile,
/// and the final board in the sequence is
///
/// '''
/// 123
/// 456
/// 78.
/// '''
///
/// If the board is unsolvable, returns `None`. If the board is already solved,
/// returns an empty vector.
pub fn solve(start: Board) -> Option<Vec<Board>> {
    let mut checking_boards = VecDeque::from([start]);
    let mut prev_to_next_boards = HashMap::new();
    prev_to_next_boards.insert(start, start);
    while let Some(checking_board) = checking_boards.pop_front() {
        if checking_board.is_final() {
            let mut result_boards = vec![];
            let mut cur = checking_board;
            while cur != start {
                result_boards.push(cur);
                cur = prev_to_next_boards[&cur];
            }
            result_boards.reverse();
            return Some(result_boards)
        }
        let neighbour_boards = checking_board.find_neighbour_boards_for_empty_pos();
        for neighbour_board in neighbour_boards {
            if !prev_to_next_boards.contains_key(&neighbour_board) {
                prev_to_next_boards.insert(neighbour_board, checking_board);
                checking_boards.push_back(neighbour_board);
            }
        }
    }
    None
}
