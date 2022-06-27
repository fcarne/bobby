// a simple example with a tic tac toe game

asm bobby

import StandardLibrary

signature:
	// DOMAINS
	domain Rank subsetof Integer
	domain File subsetof Integer
	
	enum domain Piece = { PAWN | BISHOP | KNIGHT | ROOK | QUEEN | KING}
	enum domain Color = { WHITE | BLACK }
	
	enum domain Status = { SETUP, IN_PROGRESS, CHECKMATE, STALEMATE, FIFTY_MOVES, THREEFOLD, AGREEMENT }
	
	// FUNCTIONS
	
	controlled board: Prod(File, Rank) -> Prod(Piece, Color)
	controlled status: Status
	controlled turn: Color
			
	controlled playerColor: Color
	monitored playerChosenColor: Color
	
	monitored fromSquare: Prod(File, Rank)
	monitored toSquare: Prod(File, Rank)
	
	
	static isLegalMove: Prod(Prod(File, Rank), Prod(File, Rank)) -> Boolean
definitions:
	// DOMAIN DEFINITIONS
	domain Rank = { 1 : 8 }
	domain File = { 1 : 8 }
	
	// FUNCTION DEFINITIONS
	function isLegalMove($from in Prod(File, Rank), $to in Prod(File, Rank)) = 
		isDef(board($from)) and second(board($from)) = playerColor 
			and ( isUndef(board($to)) or second(board($to)) != playerColor)
		

	// RULE DEFINITIONS
	rule r_setup($c in Color) = 
		par
			turn := WHITE
			playerColor := $c
			status := IN_PROGRESS
		endpar
	
	rule r_movePlayer($from in Prod(File,Rank), $to in Prod(File,Rank)) =
		if isLegalMove($from, $to) then
			board($to) := board($from)
		endif
	
	rule r_movePC = skip
	rule r_checkState = skip
	// MAIN RULE
	main rule r_main =
		switch status
			case SETUP : r_setup[playerChosenColor]
			case IN_PROGRESS : 
				par
					if turn = playerColor then 
						r_movePlayer[fromSquare, toSquare] 
					else
						r_movePC[]
					endif
					
					r_checkState[]
				endpar
		endswitch

// INITIAL STATE
default init s0:
	function board($f in File, $r in Rank) = 
		switch ($f, $r)
			case ($f, 2) : (PAWN, WHITE)
			case ($f, 7) : (PAWN, BLACK)
			
			case (1, 1) : (ROOK, WHITE)
			case (8, 1) : (ROOK, WHITE)
			case (1, 8) : (ROOK, BLACK)
			case (8, 8) : (ROOK, BLACK)
			
			case (2, 1) : (KNIGHT, WHITE)
			case (7, 1) : (KNIGHT, WHITE)
			case (2, 8) : (KNIGHT, BLACK)
			case (7, 8) : (KNIGHT, BLACK)
					
			case (3, 1) : (BISHOP, WHITE)
			case (6, 1) : (BISHOP, WHITE)
			case (3, 8) : (BISHOP, BLACK)
			case (6, 8) : (BISHOP, BLACK)
			
			case (4, 1) : (QUEEN, WHITE)
			case (4, 8) : (QUEEN, BLACK)
			
			case (5, 1) : (KING, WHITE)
			case (5, 8) : (KING, BLACK)
			
		endswitch
	function status = SETUP	