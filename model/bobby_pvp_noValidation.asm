asm bobby_pvp_noValidation

import StandardLibrary
import CTLlibrary

signature:
	// DOMAINS
	domain Rank subsetof Integer
	domain File subsetof Integer
	
	enum domain Piece = { PAWN | BISHOP | KNIGHT | ROOK | QUEEN | KING }
	enum domain Color = { WHITE | BLACK }
	enum domain Status = { IN_PROGRESS, CHECKMATE, AGREEMENT }
	
	// FUNCTIONS
	
	controlled boardPiece: Prod(File, Rank) -> Piece
	controlled boardColor: Prod(File, Rank) -> Color
	controlled status: Status
	controlled turn: Color
	
	monitored fromFile: File
	monitored fromRank: Rank
	monitored toFile: File
	monitored toRank: Rank

	static swap: Color -> Color

definitions:
	// DOMAIN DEFINITIONS

	domain Rank = { 1 : 8 }
	domain File = { 1 : 8 }

	function swap($c in Color) = if $c = WHITE then BLACK else WHITE endif
		
	// RULE DEFINITIONS	
	rule r_doMove($fromF in File, $fromR in Rank, $toF in File, $toR in Rank, $p in Piece) = 
		par
			boardPiece($toF, $toR) := $p
			boardColor($toF, $toR) := boardColor($fromF, $fromR)
			boardPiece($fromF, $fromR) := undef
			boardColor($fromF, $fromR) := undef
		endpar
	
	rule r_movePlayer($fromFile in File, $fromRank in Rank, $toFile in File, $toRank in Rank) =
			par
				r_doMove[$fromFile, $fromRank, $toFile, $toRank, boardPiece($fromFile, $fromRank)]
				turn := swap(turn)
			endpar

	CTLSPEC ag(status = IN_PROGRESS)

	// MAIN RULE
	main rule r_main = 
		if status = IN_PROGRESS then
			r_movePlayer[fromFile, fromRank, toFile, toRank]
		else
			skip
		endif

// INITIAL STATE
default init s0:
//	function boardPiece($f in File, $r in Rank) = 
//		switch ($f, $r)
//			case ($f, 2) : PAWN
//			case ($f, 7) : PAWN
//			
//			case (1, 1) : ROOK
//			case (8, 1) : ROOK
//			case (1, 8) : ROOK
//			case (8, 8) : ROOK
//			
//			case (2, 1) : KNIGHT
//			case (7, 1) : KNIGHT
//			case (2, 8) : KNIGHT
//			case (7, 8) : KNIGHT
//					
//			case (3, 1) : BISHOP
//			case (6, 1) : BISHOP
//			case (3, 8) : BISHOP
//			case (6, 8) : BISHOP
//			
//			case (4, 1) : QUEEN
//			case (4, 8) : QUEEN
//			
//			case (5, 1) : KING
//			case (5, 8) : KING
//			
//		endswitch
//	function boardColor($f in File, $r in Rank) = 
//		if $r = 1 or $r = 2 then
//			WHITE
//		else
//			if $r = 7 or $r = 8 then
//				BLACK
//			else
//				undef
//			endif	
//		endif	
		
	function status = IN_PROGRESS
	function turn = WHITE