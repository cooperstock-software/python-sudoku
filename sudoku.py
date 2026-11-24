#!/usr/bin/env python3
"""Sudoku (9x9 and 6x6) with a tkinter window: a Python version of the Delphi Sudoku program.

Run with:  python sudoku.py
(tkinter comes with Python on Windows and macOS. On Debian/Ubuntu Linux: sudo apt install python3-tk)

Type a puzzle's starting digits into the squares, then click Manual Play (to solve it yourself, with small helper
digits in each square) or Solve (to have the program solve it). Click Help in the program for more.

Options are saved in sudoku_options.json, in the same folder as this program.
Saved puzzles (*.sud) are in the same text format as the Delphi version, so the two programs can swap files.
"""
from __future__ import annotations

import enum
import itertools
import json
import os
import subprocess
import sys
import time
import tkinter as tk
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from dataclasses import asdict, dataclass, field, fields
from pathlib import Path
from tkinter import filedialog, messagebox, ttk
from tkinter import font as tkfont
from typing import NamedTuple

APP_TITLE = "Sudoku"

WHITE = "#ffffff"
SILVER = "#c0c0c0"
SELECTED_COLOR = "#c0dcc0"          # the "money green" the Delphi version used for the selected square
POSSIBLE_COLOR = "#000000"          # small digits that are still possible (drawn bold)
IMPOSSIBLE_COLOR = "#777777"        # small digits that are not (drawn italic and grey, so the difference is clear everywhere)

# The first of these that is installed is used for the digits. All have a real italic.
FONT_PREFERENCES = ("Tahoma", "Helvetica Neue", "Arial", "Verdana", "DejaVu Sans", "Liberation Sans")

SHIFT_MASK = 0x1                    # bits of a key event's state
CONTROL_MASK = 0x4
DIGIT_CHARS = "123456789"           # the digits that can be typed (only the first 6 in the 6x6 puzzle)


class Mode(enum.Enum):
	"""What a square is showing."""
	EMPTY = enum.auto()
	DIGITS = enum.auto()            # the small helper digits
	RESULT = enum.auto()            # one big digit


# ---------------------------------------------------------------------------
# Options, saved as JSON
# ---------------------------------------------------------------------------

class Method(enum.IntEnum):
	SIMPLE_PROMPT_BACKTRACK = 1     # simple solving rules, then ask before using backtracking
	SIMPLE_AUTO_BACKTRACK = 2       # simple solving rules, then use backtracking if needed
	ONLY_BACKTRACK = 3              # only backtracking


def program_folder() -> Path:
	if getattr(sys, "frozen", False):        # built into an exe by PyInstaller
		return Path(sys.executable).parent
	return Path(__file__).resolve().parent


@dataclass
class Options:
	"""The settings from the Options window. Options.load() reads them from a small JSON file, and save() writes them."""
	method: Method = Method.SIMPLE_PROMPT_BACKTRACK
	show_small_digits: bool = True     # show the small helper digits in squares, or not
	do_sleeps: bool = True             # pause briefly after each square the program solves
	report_duration: bool = False      # say how long a solve took
	show_attempts: bool = False        # in backtracking, show the digits being tried
	path: Path = field(default_factory=lambda: program_folder() / "sudoku_options.json", repr=False, compare=False)

	@classmethod
	def load(cls, path: str | Path | None = None) -> Options:
		"""The settings in the JSON file, with the defaults for any that are missing or not valid."""
		options = cls() if path is None else cls(path=Path(path))
		try:
			data = json.loads(options.path.read_text(encoding="utf-8"))
		except (OSError, ValueError):        # no file yet, or it can't be read: keep the defaults
			return options
		if not isinstance(data, dict):
			return options
		# Each setting is only taken if it has the right type and (for the method) is a known name.
		method = data.get("method")
		if isinstance(method, str) and method in Method.__members__:
			options.method = Method[method]
		for f in fields(options):
			if isinstance(getattr(options, f.name), bool) and isinstance(data.get(f.name), bool):
				setattr(options, f.name, data[f.name])
		return options

	def save(self) -> None:
		"""Write the settings to the JSON file. Raise OSError if that isn't possible."""
		data = asdict(self)
		del data["path"]
		data["method"] = self.method.name
		with self.path.open("w", encoding="utf-8") as file:
			json.dump(data, file, indent=2)
			file.write("\n")


# ---------------------------------------------------------------------------
# The puzzle: squares, solving rules, backtracking, saving and loading (no tkinter in this part)
# ---------------------------------------------------------------------------

class Cell:
	"""One square. Rows, columns and boxes are numbered from 0, digits from 1."""

	def __init__(self, puzzle: Puzzle, row: int, col: int, box: int):
		self.puzzle = puzzle
		self.row = row
		self.col = col
		self.box = box
		self._reset()

	@property
	def base_color(self) -> str:
		return WHITE if self.puzzle.is_light_box(self.box) else SILVER

	def _reset(self) -> None:
		"""Nothing showing, every small digit possible, and a result (once there is one) counting as original."""
		self.mode = Mode.EMPTY
		self.value: int | None = None              # the result digit: not None exactly when the mode is RESULT
		self.original = True                       # is the result part of the original puzzle (shown bold)
		self.possible = set(range(1, self.puzzle.n + 1))     # the digits that can still go here

	def clear_all(self) -> None:
		self._reset()
		self.puzzle.changed(self)

	def show_digits(self) -> None:
		self.mode = Mode.DIGITS
		self.value = None
		self.puzzle.changed(self)

	def set_result(self, value: int | None, original: bool = False) -> None:
		"""Show value as the result (original says whether it's part of the original puzzle), or clear the square
		if value is None. A new result is bubbled out to the other squares in its row, column and box."""
		if value is None:
			self.mode = Mode.DIGITS if self.puzzle.is_started else Mode.EMPTY
			self.value = None
			self.original = False
			self.puzzle.changed(self)
		else:
			self.mode = Mode.RESULT
			self.value = value
			self.original = original
			self.puzzle.changed(self)
			self.puzzle.bubble_result(self.row, self.col, value)

	def set_possible(self, digit: int, possible: bool) -> None:
		if (digit in self.possible) != possible:
			if possible:
				self.possible.add(digit)
			else:
				self.possible.discard(digit)
			if self.mode is Mode.DIGITS:
				self.puzzle.changed(self)

	def save_value(self) -> str:
		"""Three characters for saving: spaces if there's no result, the digit three times if it's an original
		puzzle digit, or the digit with a space each side if not."""
		if self.mode is not Mode.RESULT:
			return "   "
		return str(self.value) * 3 if self.original else f" {self.value} "


class DeadEnd(Exception):
	"""A square has no digit left that can go in it, so the puzzle can't be solved from where it is now."""


class StepsResult(NamedTuple):
	"""What the simple solving rules achieved."""
	made_progress: bool       # at least one square was solved
	solved: bool              # the whole puzzle is solved
	dead_end: bool            # a square was found with no digit possible


class WrongSize(ValueError):
	"""A saved file is for the other size of puzzle."""


class Puzzle:
	def __init__(self, n: int, on_change: Callable[[Cell], None] | None = None,
	             place: Callable[[Cell, int], None] | None = None):
		"""n is 9 or 6. on_change(cell) is called whenever a square's display needs updating. place(cell, digit) is how
		the solving code puts a digit in a square, so a window can add pauses (the default just does it)."""
		self.n = n
		self.box_h, self.box_w = (3, 3) if n == 9 else (2, 3)     # rows and columns in a box
		self.is_started = False                      # Manual Play or Solve has been clicked
		self.on_change = on_change
		self.place = place or self._place

		self.cells = [[None] * n for _ in range(n)]      # cells[row][col]
		self.boxes = [[None] * n for _ in range(n)]      # boxes[box][position in box]
		for row in range(n):
			for col in range(n):
				box, pos = self.box_and_pos(row, col)
				cell = Cell(self, row, col, box)
				self.cells[row][col] = cell
				self.boxes[box][pos] = cell
		self.columns = [[self.cells[row][col] for row in range(n)] for col in range(n)]    # columns[col][row]

	@property
	def all_cells(self) -> Iterator[Cell]:
		return itertools.chain.from_iterable(self.cells)

	def changed(self, cell: Cell) -> None:
		if self.on_change is not None:
			self.on_change(cell)

	@staticmethod
	def _place(cell: Cell, digit: int) -> None:
		cell.set_result(digit)

	def box_and_pos(self, row: int, col: int) -> tuple[int, int]:
		"""The box number and the position within the box (both 0 to n - 1) of a square. A 9x9 puzzle has 3x3 boxes
		numbered across then down. A 6x6 one has boxes 3 wide by 2 tall, 2 across and 3 down."""
		boxes_across = self.n // self.box_w
		box = (row // self.box_h) * boxes_across + col // self.box_w
		pos = (row % self.box_h) * self.box_w + col % self.box_w
		return box, pos

	def is_light_box(self, box: int) -> bool:
		"""The box colours alternate like a chessboard. (In the 6x6 puzzle that means boxes 1, 4 and 5, counting from 1.)"""
		if self.n == 9:
			return box % 2 == 0
		return box in (0, 3, 4)

	@property
	def box_name(self) -> str:
		return f"{self.box_w} x {self.box_h}"

	def clear_all(self) -> None:
		for cell in self.all_cells:
			cell.clear_all()
		self.is_started = False

	def is_clear(self) -> bool:
		return all(cell.mode is not Mode.RESULT for cell in self.all_cells)

	def is_solved(self) -> bool:
		return all(cell.mode is Mode.RESULT for cell in self.all_cells)

	def bubble_result(self, row: int, col: int, digit: int) -> None:
		"""After a result digit is entered in a square, remove it from the digits considered possible in the other
		squares of its row, column and box."""
		for cell in self.cells[row]:
			if cell.col != col:
				cell.set_possible(digit, False)
		for cell in self.columns[col]:
			if cell.row != row:
				cell.set_possible(digit, False)
		for cell in self.boxes[self.cells[row][col].box]:
			if cell.row != row and cell.col != col:
				cell.set_possible(digit, False)

	def find_conflict(self, row: int, col: int, digit: int | None) -> str | None:
		"""Where the digit already occurs, if it can't go in the square at row, col: "row", "column" or the box
		description such as "3 x 3 box". Return None if it's allowed. Clearing a square (digit None) is always allowed."""
		if digit is None:
			return None
		if any(cell.col != col and cell.value == digit for cell in self.cells[row]):
			return "row"
		if any(cell.row != row and cell.value == digit for cell in self.columns[col]):
			return "column"
		if any(cell.row != row and cell.col != col and cell.value == digit
		       for cell in self.boxes[self.cells[row][col].box]):
			return self.box_name + " box"
		return None

	def manual_play(self) -> None:
		"""Show the small digits in every square that has neither a result nor the small digits yet, and start."""
		for cell in self.all_cells:
			if cell.mode is Mode.EMPTY:
				cell.show_digits()
		self.prepare_for_solve()       # re-bubble all of the results
		self.is_started = True

	def prepare_for_solve(self) -> None:
		"""Get ready to solve: put every square without a result back to all digits possible, then bubble out the
		result in every square that has one across its row, column and box."""
		for cell in self.all_cells:
			if cell.mode is not Mode.RESULT:
				cell.clear_all()
				cell.show_digits()
		for cell in self.all_cells:
			if cell.mode is Mode.RESULT:
				self.bubble_result(cell.row, cell.col, cell.value)

	def solve_singleton_squares(self) -> bool:
		"""Solve any squares showing the small digits where only one digit is still possible. Return whether any
		square was solved. Raise DeadEnd if a square has no digit possible, which can happen when the puzzle
		can't be solved."""
		solved_one = False
		for cell in self.all_cells:
			if cell.mode is not Mode.DIGITS:
				continue
			if not cell.possible:
				raise DeadEnd
			if len(cell.possible) == 1:
				(digit,) = cell.possible
				self.place(cell, digit)
				solved_one = True
		return solved_one

	def solve_row_col_box(self, unit: list[Cell], digit: int) -> bool:
		"""In one row, column or box (a list of squares), if the digit can only go in one of the squares that
		are showing small digits, solve that square. Return whether one was solved."""
		candidates = [cell for cell in unit if cell.mode is Mode.DIGITS and digit in cell.possible]
		if len(candidates) == 1:
			self.place(candidates[0], digit)
			return True
		return False

	def solve_rows_cols_boxes(self) -> bool:
		"""For all rows, then all columns, then all boxes, look for digits that can only go in one square, and
		solve them. Return whether any were solved."""
		solved_any = False
		for units in (self.cells, self.columns, self.boxes):
			for unit in units:
				for digit in range(1, self.n + 1):
					if self.solve_row_col_box(unit, digit):
						solved_any = True
		return solved_any

	def main_solve_steps(self) -> StepsResult:
		"""Do the two simple solving steps in a loop until nothing more can be done."""
		results_before = sum(cell.mode is Mode.RESULT for cell in self.all_cells)
		dead_end = False
		while True:
			try:
				progressed = self.solve_singleton_squares()
			except DeadEnd:
				dead_end = True
				break
			if self.is_solved():
				break
			progressed = self.solve_rows_cols_boxes() or progressed
			if self.is_solved() or not progressed:
				break
		results_now = sum(cell.mode is Mode.RESULT for cell in self.all_cells)
		return StepsResult(results_now > results_before, self.is_solved(), dead_end)

	def backtrack_solve(self, show_attempts: bool = False, progress: Callable[[], None] | None = None) -> bool:
		"""Solve the puzzle by trying every possibility (backtracking): take the first empty square, try each digit
		that isn't already in its row, column or box, and recurse. A digit's presence in a row, column or box is a bit
		in a number. If show_attempts, each digit tried is shown in its square, which is much slower.
		progress() is called now and then, so a window can stay alive. Return whether it was solved."""
		n = self.n
		flat = list(self.all_cells)
		board = [cell.value or 0 for cell in flat]
		row_masks = [0] * n
		col_masks = [0] * n
		box_masks = [0] * n
		for cell, digit in zip(flat, board):
			if digit:
				bit = 1 << (digit - 1)
				row_masks[cell.row] |= bit
				col_masks[cell.col] |= bit
				box_masks[cell.box] |= bit
		empties = [i for i, digit in enumerate(board) if digit == 0]
		full = (1 << n) - 1
		count = 0

		def solve(k: int) -> bool:
			nonlocal count
			if k == len(empties):
				return True
			i = empties[k]
			cell = flat[i]
			row, col, box = cell.row, cell.col, cell.box
			available = full & ~(row_masks[row] | col_masks[col] | box_masks[box])
			while available:
				bit = available & -available          # the lowest digit still allowed
				available ^= bit
				digit = bit.bit_length()
				board[i] = digit
				row_masks[row] |= bit
				col_masks[col] |= bit
				box_masks[box] |= bit
				count += 1
				if show_attempts:
					cell.set_result(digit)
					if progress:
						progress()
				elif progress and count % 20000 == 0:
					progress()
				if solve(k + 1):
					return True
				board[i] = 0
				row_masks[row] ^= bit
				col_masks[col] ^= bit
				box_masks[box] ^= bit
				if show_attempts:
					cell.set_result(None)
					if progress:
						progress()
			return False

		if not solve(0):
			return False
		for cell, digit in zip(flat, board):                 # transfer the results back to the squares
			if cell.mode is not Mode.RESULT:
				cell.set_result(digit)
		return True

	def to_text(self) -> str:
		"""The text of a saved puzzle, in the same format as the Delphi version: border lines and a line for each
		row, like   +---+---+...   then   |111|   | 5 |...|"""
		border = "+" + "---+" * self.n
		lines = []
		for row in self.cells:
			lines.append(border)
			lines.append("|" + "|".join(cell.save_value() for cell in row) + "|")
		lines.append(border)
		return "\n".join(lines) + "\n"

	def load_text(self, text: str) -> None:
		"""Show a puzzle saved by to_text. Raise WrongSize if it's for the other size, or ValueError for any other
		problem. Squares before the problem will already have been filled in."""
		self.clear_all()
		for row, line in enumerate(text.splitlines()[1::2][:self.n]):      # every second line is a border
			if row == 0:                                 # check it is for this size of puzzle
				num_cells = (len(line) - len(line) % 2) // 4
				if num_cells != self.n:
					raise WrongSize(
						f"This appears to be a file saved from a {num_cells} x {num_cells} Sudoku, "
						f"rather than a {self.n} x {self.n} one.\n\nIt cannot be loaded into this puzzle")
			for col in range(self.n):
				s = line[col * 4 + 1:col * 4 + 4]
				if len(s) < 3:
					raise ValueError(f"row {row + 1} is too short")
				digit = s[1]
				if digit == " ":
					continue                             # nothing in this square
				if digit not in DIGIT_CHARS[:self.n]:
					raise ValueError(f"unexpected character {digit!r} in row {row + 1}, column {col + 1}")
				self.cells[row][col].set_result(int(digit), s[0] != " ")


# ---------------------------------------------------------------------------
# The windows
# ---------------------------------------------------------------------------

class SolveAborted(Exception):
	"""The window was closed while a solve was running."""


CELL_SIZE = 65
X_POSITIONS = [10, 76, 142, 209, 275, 341, 408, 474, 540]                  # left edges of the columns
Y_POSITIONS = {9: [10, 76, 142, 209, 275, 341, 408, 474, 540],             # top edges of the rows
               6: [10, 76, 143, 209, 276, 342]}
SMALL_X = (4, 26, 47)                                                      # where the small digits go in a square
SMALL_Y = {9: (2, 22, 41), 6: (2, 35)}

# Size of the board's black background square, of the window, and of each button: left, top, width, height
BOARD_SIZE = {9: 599, 6: 402}
WINDOW_SIZE = {9: (615, 716), 6: (423, 571)}
BUTTONS = {
	9: {"manual": (9, 628, 98, 30), "solve": (122, 628, 94, 30), "load": (285, 628, 92, 30),
	    "save": (397, 628, 92, 30), "help": (512, 627, 94, 31),
	    "clear": (9, 672, 98, 30), "options": (122, 672, 94, 30), "switch": (285, 672, 206, 30)},
	6: {"manual": (9, 439, 98, 32), "solve": (122, 439, 94, 32), "clear": (316, 439, 94, 30),
	    "load": (9, 479, 92, 32), "save": (122, 479, 92, 30), "options": (316, 478, 94, 30),
	    "switch": (9, 527, 206, 30), "help": (319, 530, 94, 31)},
}
BUTTON_TEXT_MARGIN = 26      # room left each side of a button's text on a Mac, whose rounded buttons clip it otherwise
BUTTON_SPARE_WIDTH = 16      # and extra room on top of the width Tk says the button needs


def button_layout(n: int, manual_width_needed: int) -> dict[str, tuple[int, int, int, int]]:
	"""The (left, top, width, height) of each button for the n x n window. The Delphi positions are used, unless
	the "Manual Play" button needs to be wider than that layout makes it (manual_width_needed pixels). Then the left
	column of buttons is made wider (all the same width, so "Manual Play" and the button under it match), and the
	next column is moved right by the same amount, so the gap between them stays the same. The buttons further
	right don't move, so the growth is limited to what leaves the same size of gap before them."""
	layout = dict(BUTTONS[n])
	manual_left, _, manual_width, _ = layout["manual"]
	next_column = layout["solve"][0]
	next_column_right = max(left + width for left, _, width, _ in BUTTONS[n].values() if left == next_column)
	right_of_that = min(left for left, _, _, _ in BUTTONS[n].values() if left > next_column)
	extra = min(manual_width_needed - manual_width,
	            right_of_that - next_column_right - (next_column - (manual_left + manual_width)))     # keep the gaps
	if extra <= 0:
		return layout
	for name, (left, top, width, height) in BUTTONS[n].items():
		if left == manual_left:
			# ("Switch" in the 6x6 window spans the first two columns, so it grows by as much as the gap moves)
			layout[name] = (left, top, width + extra if name == "switch" else manual_width + extra, height)
		elif left == next_column:
			layout[name] = (left + extra, top, width, height)
	return layout


def hot_key_sequences(letter: str) -> list[str]:
	"""The key presses that act as the hot key for a button, whose caption has the letter underlined: Alt plus the
	letter. A Mac's Alt key (Option) types other characters instead, and a Windows keyboard has no Command key, so
	there Command (the Windows key) or Control plus the letter work."""
	modifiers = ("Command", "Control") if sys.platform == "darwin" else ("Alt",)
	return [f"<{modifier}-{key}>" for modifier in modifiers for key in (letter.lower(), letter.upper())]

HELP_TEXT = """\
Entering a puzzle
Click a square, then type a digit (1 to 9, or 1 to 6 in the 6x6 puzzle) to put it there. Backspace or Delete clears \
the square. The digits you type before clicking Manual Play or Solve are the original puzzle, and are shown in bold.

Moving around
The arrow keys move one square (and beep at the edge). Tab and Shift+Tab move forward and back through the squares, \
wrapping from the end of one row to the start of the next. Home and End go to the start and end of the row, and \
Page Up and Page Down to the top and bottom of the column.

Manual Play
Shows small helper digits in every square that has no digit yet. A bold small digit is still possible in that \
square; a grey italic one is not. When you put a digit in a square, it is removed from the possible digits in its \
row, column and box.
 - Click a small digit to switch it between possible and not possible.
 - Double-click a small digit to make it that square's answer.
 - Double-click an answer you entered during play (one that isn't bold) to go back to the small digits.
The program tells you if you try to enter a digit that already occurs in the same row, column or box, and when \
you have solved the puzzle.

Solve
Solves the puzzle for you. It first uses the simple solving rules: a square where only one digit is possible, \
and a digit that can only go in one square of a row, column or box. If that isn't enough, the Options say whether \
it asks first, or goes straight on to the fast backtracking approach, which tries all remaining possibilities. \
You can also choose to use only the backtracking approach.

Load and Save
Saved puzzles are text files (*.sud) showing the digits, with the original digits repeated three times. \
Files saved from the 9x9 puzzle can only be loaded into the 9x9 puzzle, and likewise for 6x6.

Options
 - Do short pauses after solving squares, so you can watch it work.
 - Report the time taken to solve the puzzle, ignoring pauses.
 - Show the small helper digits during Manual Play or simple solving. If they are off, the program still keeps \
track of the possible digits, it just doesn't draw them.
 - Which solving method to use.
 - In the fast backtracking approach, show the digits being tried. This makes it much slower.

Switch
Switches between the 9x9 and 6x6 puzzles. Each keeps its own squares.

Clear
Clears the whole puzzle.

Hot keys
The underlined letter in a button's name (or in an option in the Options window) is its hot key: hold down Alt \
and press the letter. On a Mac, hold down Command (the Windows key on a Windows keyboard) or Control instead. \
A Mac doesn't underline the letters.
"""


class SudokuApp:
	"""The two puzzle windows (9x9 and 6x6, each keeping its own squares) and what they share."""

	def __init__(self, options_path: str | Path | None = None):
		self.root = tk.Tk()
		self.root.withdraw()                  # the windows are all Toplevels, so each can be shown and hidden
		self.options = Options.load(options_path)
		self.busy = False                     # a solve is running
		self.abort = False                    # the window was closed during it

		self.default_font = tkfont.nametofont("TkDefaultFont")
		families = set(tkfont.families(self.root))
		self.family = next((name for name in FONT_PREFERENCES if name in families),
		                   self.default_font.actual("family"))
		self.ui_font = tkfont.Font(family=self.default_font.actual("family"), size=-15)
		style = ttk.Style(self.root)
		for name in ("TButton", "TCheckbutton", "TRadiobutton", "TLabelframe.Label"):
			style.configure(name, font=self.ui_font)
		self.background = style.lookup("TFrame", "background") or "#f0f0f0"

		self.icon = None
		try:
			self.icon = tk.PhotoImage(master=self.root, file=str(program_folder() / "sudoku_icon.png"))
		except tk.TclError:
			pass                              # the icon file isn't there: no icon

		self.windows = {9: SudokuWindow(self, 9), 6: SudokuWindow(self, 6)}
		self.windows[6].win.withdraw()
		self.windows[9].show()

	def other_window(self, window: SudokuWindow) -> SudokuWindow:
		return self.windows[6 if window.n == 9 else 9]

	def redraw_all(self) -> None:
		for window in self.windows.values():
			window.redraw()

	def quit(self) -> None:
		self.root.destroy()

	def on_close(self) -> None:
		if self.busy:
			self.abort = True                 # the solve notices, and then closes the program
		else:
			self.quit()

	def run(self) -> None:
		self.root.mainloop()


class SudokuWindow:
	def __init__(self, app, n):
		self.app = app
		self.n = n
		self.puzzle = Puzzle(n, on_change=self.draw_cell, place=self.place)
		self.x_pos = X_POSITIONS
		self.y_pos = Y_POSITIONS[n]
		self.selected: tuple[int, int] | None = None     # (row, col) of the selected square, if any
		self.save_file: Path | None = None    # the last file saved to or loaded from
		self.current_dir = Path.cwd()
		self.pauses = 0.0                     # seconds spent in pauses during a solve

		win = self.win = tk.Toplevel(app.root)
		win.title(APP_TITLE if n == 9 else APP_TITLE + " 6x6")
		win.configure(bg=app.background)
		win.resizable(False, False)
		width, height = WINDOW_SIZE[n]
		x = (win.winfo_screenwidth() - width) // 2
		y = (win.winfo_screenheight() - height) // 2
		win.geometry(f"{width}x{height}+{x}+{max(y, 0)}")
		win.protocol("WM_DELETE_WINDOW", app.on_close)
		if app.icon is not None:
			win.iconphoto(False, app.icon)

		# fonts: the result digit (bold for original digits), and the small digits (bold if possible, italic if not)
		self.result_bold = tkfont.Font(family=app.family, size=-37, weight="bold")
		self.result_plain = tkfont.Font(family=app.family, size=-37)
		self.small_bold = tkfont.Font(family=app.family, size=-17, weight="bold")
		self.small_italic = tkfont.Font(family=app.family, size=-17, slant="italic")

		board = BOARD_SIZE[n]
		self.canvas = tk.Canvas(win, width=width, height=board + 16, bg=app.background, highlightthickness=0)
		self.canvas.place(x=0, y=0)
		self.canvas.bind("<Button-1>", self.on_click)
		self.canvas.bind("<Double-Button-1>", self.on_double_click)

		self.buttons = {}
		other = 6 if n == 9 else 9
		button_specs = [               # name, caption, which letter of it is underlined (the Alt key), action
			("manual", "Manual Play", 0, self.on_manual_play),
			("solve", "Solve", 0, self.on_solve),
			("load", "Load", 0, self.on_load),
			("save", "Save", 1, self.on_save),
			("clear", "Clear", 0, self.on_clear),
			("options", "Options", 0, self.on_options),
			("help", "Help", 0, self.on_help),
			("switch", f"Switch to {other}x{other} Sudoku", 1, self.on_switch),
		]
		for name, text, underline, action in button_specs:
			button = ttk.Button(win, text=text, underline=underline, command=self.guarded(action))
			self.buttons[name] = button
			for sequence in hot_key_sequences(text[underline]):
				win.bind(sequence, lambda event, b=button: b.invoke())
		manual_width_needed = 0                # (only a Mac's buttons need more room than the Delphi layout gives)
		if sys.platform == "darwin":
			win.update_idletasks()
			manual_width_needed = max(self.buttons["manual"].winfo_reqwidth() + BUTTON_SPARE_WIDTH,
			                          app.ui_font.measure("Manual Play") + 2 * BUTTON_TEXT_MARGIN)
		for name, (left, top, w, h) in button_layout(n, manual_width_needed).items():
			self.buttons[name].place(x=left, y=top, width=w, height=h)

		win.bind("<Key>", self.on_key)
		self.redraw()
		self.canvas.focus_set()

	# ----- showing the puzzle -----

	def show(self) -> None:
		self.win.deiconify()
		self.win.lift()
		self.canvas.focus_set()

	def redraw(self) -> None:
		self.canvas.delete("all")
		board = BOARD_SIZE[self.n]
		self.canvas.create_rectangle(8, 8, 8 + board, 8 + board, fill="black", outline="")
		for cell in self.puzzle.all_cells:
			self.draw_cell(cell)

	def draw_cell(self, cell: Cell) -> None:
		canvas = self.canvas
		tag = f"cell{cell.row}_{cell.col}"
		canvas.delete(tag)
		x = self.x_pos[cell.col]
		y = self.y_pos[cell.row]
		selected = self.selected == (cell.row, cell.col)
		canvas.create_rectangle(x, y, x + CELL_SIZE, y + CELL_SIZE, fill=SELECTED_COLOR if selected else cell.base_color,
		                        outline="", tags=tag)
		if cell.mode is Mode.RESULT:
			font = self.result_bold if cell.original else self.result_plain
			canvas.create_text(x + CELL_SIZE // 2, y + CELL_SIZE // 2 + 1, text=str(cell.value), font=font, tags=tag)
		elif cell.mode is Mode.DIGITS and self.app.options.show_small_digits:
			small_y = SMALL_Y[self.n]
			for digit in range(1, self.n + 1):
				row_slot, col_slot = divmod(digit - 1, 3)
				possible = digit in cell.possible
				canvas.create_text(x + SMALL_X[col_slot] + 5, y + small_y[row_slot] + 9, text=str(digit),
				                   font=self.small_bold if possible else self.small_italic,
				                   fill=POSSIBLE_COLOR if possible else IMPOSSIBLE_COLOR, tags=tag)

	def select(self, row: int, col: int) -> None:
		"""Make the square at row, col the selected one."""
		old = self.selected
		self.selected = (row, col)
		if old is not None:
			self.draw_cell(self.puzzle.cells[old[0]][old[1]])
		self.draw_cell(self.puzzle.cells[row][col])

	# ----- messages -----

	def info(self, text: str) -> None:
		messagebox.showinfo(APP_TITLE, text, parent=self.win)

	def ask(self, text: str) -> bool:
		return messagebox.askyesno(APP_TITLE, text, parent=self.win)

	def beep(self) -> None:
		self.win.bell()

	def guarded(self, action: Callable[[], None]) -> Callable[[], None]:
		"""Run a button's action, unless a solve is running."""
		def run():
			if not self.app.busy:
				action()
		return run

	def check_allowed(self, cell: Cell, digit: int | None, verbose: bool) -> bool:
		"""Check whether digit can go in the square, and say why not if it can't."""
		where = self.puzzle.find_conflict(cell.row, cell.col, digit)
		if where is not None and verbose:
			self.info(f"You cannot put a {digit} in this square, because it already occurs in another "
			          f"square in the same {where}.")
		return where is None

	# ----- the mouse -----

	def hit_test(self, x: int, y: int) -> tuple[Cell | None, int]:
		"""Which square, and which small digit within it (0 if none), is at a point on the canvas."""
		for cell in self.puzzle.all_cells:
			left, top = self.x_pos[cell.col], self.y_pos[cell.row]
			if left <= x < left + CELL_SIZE and top <= y < top + CELL_SIZE:
				digit = 0
				if cell.mode is Mode.DIGITS and self.app.options.show_small_digits:
					col_slot = min(2, (x - left) * 3 // CELL_SIZE)
					rows_of_digits = 3 if self.n == 9 else 2
					row_slot = min(rows_of_digits - 1, (y - top) * rows_of_digits // CELL_SIZE)
					digit = row_slot * 3 + col_slot + 1
				return cell, digit
		return None, 0

	def on_click(self, event: tk.Event) -> None:
		self.canvas.focus_set()
		if self.app.busy:
			return
		cell, digit = self.hit_test(event.x, event.y)
		if cell is None:
			return
		if digit:
			# a click on a small digit switches it between possible and not possible (if it's allowed)
			possible = digit in cell.possible
			if possible or self.check_allowed(cell, digit, True):
				cell.set_possible(digit, not possible)
		self.select(cell.row, cell.col)

	def on_double_click(self, event: tk.Event) -> None:
		if self.app.busy:
			return
		cell, digit = self.hit_test(event.x, event.y)
		if cell is None:
			return
		if digit:
			# a double-click on a small digit makes it the square's answer, if it's allowed
			if self.check_allowed(cell, digit, True):
				cell.set_result(digit)
				cell.possible.add(digit)         # (the first click of the double-click may have turned it off)
				self.win.update_idletasks()
				if self.puzzle.is_solved():
					self.info("You have solved the puzzle!")
			self.select(cell.row, cell.col)
		elif cell.mode is Mode.RESULT and not cell.original:
			# a double-click on an answer that isn't part of the original puzzle goes back to the small digits,
			# without showing any digit now disallowed as possible
			cell.show_digits()
			for d in sorted(cell.possible):
				if not self.check_allowed(cell, d, False):
					cell.set_possible(d, False)
		else:
			self.select(cell.row, cell.col)

	# ----- the keyboard -----

	def on_key(self, event: tk.Event) -> str | None:
		if self.app.busy:
			return "break" if event.keysym in ("Tab", "ISO_Left_Tab") else None
		key = event.keysym
		n = self.n

		if key in ("Tab", "ISO_Left_Tab"):
			# Tab walks forward through the rows and columns, from the end of a row to the start of the next, and
			# from the end of the last row to the top. Shift-Tab is the same in reverse.
			if self.selected is None:
				row, col = 0, 0
			else:
				row, col = self.selected
				if key == "Tab" and not event.state & SHIFT_MASK:
					col += 1
					if col >= n:
						col = 0
						row = (row + 1) % n
				else:
					col -= 1
					if col < 0:
						col = n - 1
						row = (row - 1) % n
			self.select(row, col)
			return "break"

		moves = {"Down": (1, 0), "Up": (-1, 0), "Right": (0, 1), "Left": (0, -1)}
		if key in moves:
			if self.selected is None:
				row, col = 0, 0
			else:
				row, col = self.selected
				row, col = row + moves[key][0], col + moves[key][1]
				if not (0 <= row < n and 0 <= col < n):
					self.beep()                    # arrow keys don't wrap
					return "break"
			self.select(row, col)
			return "break"

		jumps = {"Next": lambda r, c: (n - 1, c), "Prior": lambda r, c: (0, c),      # Page Down / Page Up
		         "End": lambda r, c: (r, n - 1), "Home": lambda r, c: (r, 0)}
		if key in jumps:
			self.select(*jumps[key](*(self.selected or (0, 0))))
			return "break"

		if key in ("Delete", "BackSpace"):
			self.type_digit(None)
			return "break"
		if event.char and len(event.char) == 1 and event.char in DIGIT_CHARS[:n] and not event.state & CONTROL_MASK:
			self.type_digit(int(event.char))
			return "break"
		return None

	def type_digit(self, digit: int | None) -> None:
		"""Put the digit (or nothing, for None) in the selected square."""
		if self.selected is None:
			return
		row, col = self.selected
		cell = self.puzzle.cells[row][col]
		# can't change original values once started
		if self.puzzle.is_started and cell.mode is Mode.RESULT and cell.original:
			self.beep()
			return
		if digit is None:
			cell.set_result(None)
		elif self.check_allowed(cell, digit, True):
			cell.set_result(digit, original=not (self.puzzle.is_started or cell.mode is Mode.DIGITS))
			self.win.update_idletasks()
			if self.puzzle.is_solved():
				self.info("You have solved the puzzle!")

	# ----- solving -----

	def pump(self) -> None:
		"""Let the window repaint and handle events (which are ignored while a solve is running)."""
		self.win.update()
		if self.app.abort:
			raise SolveAborted

	@contextmanager
	def untimed(self) -> Iterator[None]:
		"""Time spent in this block (a pause, or waiting for an answer to a question) isn't part of the solve time."""
		start = time.perf_counter()
		try:
			yield
		finally:
			self.pauses += time.perf_counter() - start

	def pause(self, seconds: float) -> None:
		"""Wait a little, keeping the window alive."""
		with self.untimed():
			end = time.perf_counter() + seconds
			while time.perf_counter() < end:
				self.pump()
				time.sleep(0.01)

	def ask_untimed(self, text: str) -> bool:
		with self.untimed():
			return self.ask(text)

	def place(self, cell: Cell, digit: int) -> None:
		"""How a square gets solved: select it, show the digit, and pause."""
		self.select(cell.row, cell.col)
		cell.set_result(digit)
		self.pump()
		if self.app.options.do_sleeps:
			self.pause(0.2)

	def on_manual_play(self) -> None:
		self.puzzle.manual_play()

	def on_solve(self) -> None:
		if not self.puzzle.is_started:
			self.on_manual_play()
		self.full_solve()

	def full_solve(self) -> None:
		"""Follow the steps to solve the puzzle: the simple rules, then backtracking if the options say so."""
		app = self.app
		puzzle = self.puzzle
		start = time.perf_counter()
		self.pauses = 0.0
		app.busy = True
		app.abort = False
		self.win.configure(cursor="watch")
		try:
			puzzle.prepare_for_solve()
			self.run_solving_steps()
			duration = time.perf_counter() - start - self.pauses
		except SolveAborted:
			app.quit()
			return
		finally:
			app.busy = False
			try:
				self.win.configure(cursor="")
			except tk.TclError:
				pass                                  # the window is already gone

		if puzzle.is_solved():
			message = "The puzzle has been successfully solved."
			if app.options.report_duration:
				message += f"\n\nThat took {duration:.2f} seconds"
				if self.pauses > 0:
					message += ", ignoring any pauses"
				message += "."
			self.win.update_idletasks()
			self.info(message)

	def run_solving_steps(self) -> None:
		"""The simple rules, then backtracking if the options say so (asking first, if they say that)."""
		options = self.app.options
		puzzle = self.puzzle
		if options.method is not Method.ONLY_BACKTRACK and puzzle.main_solve_steps().solved:
			return
		if options.method is Method.SIMPLE_PROMPT_BACKTRACK and not self.ask_untimed(
				"Sorry, the simple solving rules in this program were not able to completely solve the puzzle.\n\n"
				"Would you like to have the program use its backtracking approach of trying all remaining "
				"possibilities?"):
			self.info("You can try solving the rest of it manually.")
			return
		show_attempts = options.show_attempts and self.ask_untimed(
			"Showing the attempted digits when using the code for the backtracking approach "
			"can make solving it extremely slow!\n\nAre you sure you want to show the attempted digits?")
		if not puzzle.backtrack_solve(show_attempts, self.pump):
			self.info("The possibly slower method was not successful.")

	# ----- the other buttons -----

	def clear_all(self) -> None:
		self.puzzle.clear_all()
		self.selected = None
		self.pauses = 0.0
		self.redraw()

	def on_clear(self) -> None:
		if not self.puzzle.is_clear():
			if not self.ask("There are already results in the puzzle. Are you sure you want to clear it?"):
				return
		self.clear_all()

	def on_switch(self) -> None:
		if not self.puzzle.is_clear():
			if not self.ask("There are already results in the puzzle. Are you sure you want to switch to the other size?"):
				return
		self.win.withdraw()
		self.app.other_window(self).show()

	def on_options(self) -> None:
		dialog = OptionsDialog(self.win, self.app)
		dialog.wait_window()
		if dialog.saved:
			self.app.redraw_all()            # in case the small digits were turned on or off

	def on_help(self) -> None:
		pdf = next((path for folder in (program_folder(), Path.cwd())
		            if (path := folder / "sudoku.pdf").is_file()), None)
		if pdf is None:
			HelpWindow(self.win)
			return
		try:
			if sys.platform.startswith("win"):
				os.startfile(pdf)
			elif sys.platform == "darwin":
				subprocess.Popen(["open", pdf])
			else:
				subprocess.Popen(["xdg-open", pdf])
		except OSError as e:
			self.info(f"Error opening Help file {pdf}.\n{e}")

	def on_save(self) -> None:
		if self.save_file:
			initial_dir, initial_file = self.save_file.parent, self.save_file.name
		else:
			initial_dir, initial_file = self.current_dir, "save.sud"
		path = filedialog.asksaveasfilename(parent=self.win, title="Save puzzle", initialdir=str(initial_dir),
		                                    initialfile=initial_file, defaultextension=".sud",
		                                    filetypes=[("Sudoku Files", "*.sud")])
		if not path:
			return
		path = Path(path)
		try:
			with path.open("w", encoding="latin-1", newline="\n") as file:
				file.write(self.puzzle.to_text())
		except OSError as e:
			self.info(f"Unable to write to file {path}.\nError: {e}")
			return
		self.save_file = path            # for re-loads or re-saves

	def on_load(self) -> None:
		if self.save_file:
			initial_dir, initial_file = self.save_file.parent, self.save_file.name
		else:
			initial_dir, initial_file = self.current_dir, ""
		path = filedialog.askopenfilename(parent=self.win, title="Load puzzle", initialdir=str(initial_dir),
		                                  initialfile=initial_file, defaultextension=".sud",
		                                  filetypes=[("Sudoku Files", "*.sud")])
		if not path:
			return
		if not self.puzzle.is_clear():
			if not self.ask("Is it OK to clear whatever is currently displayed, before Loading a puzzle?"):
				return
		self.load_file(path)

	def load_file(self, path: str | Path) -> None:
		"""Clear the puzzle and show the puzzle in the file."""
		path = Path(path)
		if not path.is_file():
			self.info(f"Cannot open file {path} since it doesn't seem to exist.")
			return
		self.clear_all()
		try:
			self.puzzle.load_text(path.read_text(encoding="latin-1"))
		except WrongSize as e:
			self.info(str(e))
		except OSError as e:
			self.info(f"Error reading file {path} {e}")
		except ValueError as e:
			self.info(f"Error processing file {path} {e}")
		else:
			self.save_file = path            # for re-loads or re-saves
		self.redraw()


class OptionsDialog(tk.Toplevel):
	"""The Options window. It sets self.saved if Save was clicked."""

	def __init__(self, parent: tk.Misc, app: SudokuApp):
		super().__init__(parent)
		self.app = app
		self.saved = False
		options = app.options
		self.title("Options")
		self.configure(bg=app.background)
		self.resizable(False, False)
		self.transient(parent)
		width, height = 655, 337
		x = (self.winfo_screenwidth() - width) // 2
		y = (self.winfo_screenheight() - height) // 2
		self.geometry(f"{width}x{height}+{x}+{max(y, 0)}")

		self.sleeps = tk.BooleanVar(value=options.do_sleeps)
		self.report = tk.BooleanVar(value=options.report_duration)
		self.small = tk.BooleanVar(value=options.show_small_digits)
		self.attempts = tk.BooleanVar(value=options.show_attempts)
		self.method = tk.IntVar(value=int(options.method))
		self.accelerators = {}

		def add(widget, key):
			self.accelerators[key] = widget
			for sequence in hot_key_sequences(key):
				self.bind(sequence, lambda event: widget.invoke())

		def checkbox(text, variable, left, top, underline):
			box = ttk.Checkbutton(self, text=text, variable=variable, underline=underline)
			box.place(x=left, y=top, width=619, height=24)
			add(box, text[underline].lower())

		checkbox("Do short pauses after solving squares", self.sleeps, 20, 16, 0)
		checkbox("Report the time taken to solve the puzzle, ignoring pauses", self.report, 20, 44, 0)
		checkbox("Show small helper digits in each square during Manual Play or Simple Solving", self.small, 20, 72, 1)

		group = ttk.LabelFrame(self, text="Solving Method to Use")
		group.place(x=12, y=114, width=619, height=126)      # (taller than Delphi's, so bigger fonts don't clip the buttons)
		texts = ["Simple solving rules, plus prompt to use fast backtracking approach if needed",
		         "Simple solving rules, automatically use fast backtracking approach if needed",
		         "Only use fast backtracking approach"]
		for value, (text, underline) in enumerate(zip(texts, (1, 2, 0)), start=1):
			radio = ttk.Radiobutton(group, text=text, value=value, variable=self.method, underline=underline)
			radio.pack(anchor="w", padx=6, pady=3)
			add(radio, text[underline].lower())

		attempts_text = "In fast backtracking approach, show digits being tried"
		checkbox(attempts_text, self.attempts, 20, 253, attempts_text.index("approach"))
		save = ttk.Button(self, text="Save", underline=0, command=self.on_save)
		save.place(x=20, y=293, width=75, height=28)
		cancel = ttk.Button(self, text="Cancel", underline=0, command=self.destroy)
		cancel.place(x=128, y=293, width=75, height=28)
		add(save, "s")
		add(cancel, "c")
		self.bind("<Return>", lambda event: self.on_save())
		self.bind("<Escape>", lambda event: self.destroy())
		save.focus_set()
		self.wait_visibility()           # a window has to be showing before it can grab input
		self.grab_set()

	def on_save(self) -> None:
		options = self.app.options
		options.do_sleeps = self.sleeps.get()
		options.report_duration = self.report.get()
		options.show_small_digits = self.small.get()
		options.show_attempts = self.attempts.get()
		options.method = Method(self.method.get())
		self.saved = True
		self.destroy()
		try:
			options.save()
		except OSError as e:
			messagebox.showwarning(APP_TITLE, f"The options couldn't be saved to {options.path}:\n{e}\n\n"
			                       "They will be used until the program is closed.")


class HelpWindow(tk.Toplevel):
	"""Used for Help when there is no sudoku.pdf next to the program."""

	def __init__(self, parent):
		super().__init__(parent)
		self.title("Sudoku Help")
		self.geometry("640x560")
		frame = ttk.Frame(self)
		frame.pack(fill="both", expand=True)
		bar = ttk.Scrollbar(frame)
		bar.pack(side="right", fill="y")
		text = tk.Text(frame, wrap="word", padx=12, pady=8, yscrollcommand=bar.set, borderwidth=0)
		text.pack(side="left", fill="both", expand=True)
		bar.config(command=text.yview)
		text.insert("1.0", HELP_TEXT)
		text.config(state="disabled")
		self.bind("<Escape>", lambda event: self.destroy())


def main():
	SudokuApp().run()


if __name__ == "__main__":
	main()
