asm bobby_pvp_silvermanVariation

import StandardLibrary

signature:
	// DOMAINS
	domain Rank subsetof Integer
	domain File subsetof Integer
	
	enum domain Piece = { PAWN | ROOK | QUEEN | KING }
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
	monitored proposeDraw: Color -> Boolean
	monitored isCheckmate: Color -> Boolean
	
	controlled kingPositionFile: Color -> File
	controlled kingPositionRank: Color -> Rank
		
	static swap: Color -> Color
	static between: Prod(Integer, Integer, Integer) -> Boolean
		
	static isLegalMove: Prod(Color, File, Rank, File, Rank) -> Boolean
	
	static isValidMove: Prod(Color, File, Rank, File, Rank) -> Boolean
	static isValidStraightMove: Prod(File, Rank, File, Rank, Integer) -> Boolean
	static isValidDiagonalMove: Prod(File, Rank, File, Rank, Integer) -> Boolean
	static isValidPawnMove: Prod(Color, File, Rank, File, Rank) -> Boolean

	static pawnStartingRank: Color -> Rank
	static advancePawnRank: Prod(Color, Rank) -> Rank
	static boardRankEdge: Color -> Rank
	
	derived endOfGame : Boolean
	
definitions:
	// DOMAIN DEFINITIONS

	domain Rank = { 1 : 4 }
	domain File = { 1 : 4 }
	
	// FUNCTION DEFINITIONS
		
	function swap($c in Color) = if $c = WHITE then BLACK else WHITE endif
	
	function between($x in Integer, $a in Integer, $b in Integer) =
		if $a < $b then
			$a < $x and $x < $b
		else
			$b < $x and $x < $a 
		endif

	function isLegalMove($c in Color, $fromF in File, $fromR in Rank, $toF in File, $toR in Rank) = 
		isDef(boardPiece($fromF, $fromR)) and 
		boardColor($fromF, $fromR) = turn and 
		($fromF != $toF or $fromR != $toR) and 
		(isDef(boardColor($toF, $toR)) implies boardColor($toF, $toR) != turn) and 
		($toF != kingPositionFile(swap($c)) or $toR != kingPositionRank(swap($c))) and 
		(boardPiece($fromF, $fromR) = KING implies max(abs(kingPositionFile(swap($c)) - $toF), abs(kingPositionRank(swap($c)) - $toR) ) > 1)
			
	function isValidDiagonalMove($fromF in File, $fromR in Rank, $toF in File, $toR in Rank, $limit in Integer) =
		abs($fromF - $toF) = abs($fromR - $toR) and abs($fromF - $toF) <= $limit and 
		(forall $f1 in File, $r1 in Rank with  
			(between($f1, $fromF, $toF) and between($r1, $fromR, $toR) and abs($fromF - $f1) = abs($fromR - $r1)) 
			implies (isUndef(boardPiece($f1, $r1)))
		)
	

	function isValidStraightMove($fromF in File, $fromR in Rank, $toF in File, $toR in Rank, $limit in Integer) =
		($fromF - $toF = 0 or $fromR - $toR = 0) and ($fromF - $toF) + ($fromR - $toR) <= $limit and
		(forall $f1 in File, $r1 in Rank with 
			((between($f1, $fromF, $toF) or between($r1, $fromR, $toR)) and ($fromF - $f1 = 0 or $fromR - $r1 = 0)) 
			implies (isUndef(boardPiece($f1, $r1)))
		)

	function pawnStartingRank($c in Color) = if $c = WHITE then 2 else 4 endif
	function advancePawnRank($c in Color, $r in Rank) = if $c = WHITE then $r + 1 else $r - 1 endif
	function boardRankEdge($c in Color) = if $c = WHITE then 5 else 1 endif

	function isValidPawnMove($c in Color, $fromF in File, $fromR in Rank, $toF in File, $toR in Rank) = 
		(between($fromR, 1, 5) and $fromF = $toF and $toR = advancePawnRank($c, $fromR)) or
		($fromR = pawnStartingRank($c) and $fromF = $toF and $toR = advancePawnRank($c, advancePawnRank($c, $fromR))) or
		(isDef(boardPiece($fromF + 1, advancePawnRank($c, $fromR))) and $toF = $fromF + 1 and $toR = advancePawnRank($c, $fromR)) or
		(isDef(boardPiece($fromF - 1, advancePawnRank($c, $fromR))) and $toF = $fromF - 1 and $toR = advancePawnRank($c, $fromR))
		
	function isValidMove($c in Color, $fromF in File, $fromR in Rank, $toF in File, $toR in Rank) =
		switch boardPiece($fromF, $fromR)
			case PAWN : isValidPawnMove($c, $fromF, $fromR, $toF, $toR)
   			case ROOK : isValidStraightMove($fromF, $fromR, $toF, $toR, 5)
   			case QUEEN : isValidDiagonalMove($fromF, $fromR, $toF, $toR, 5) or isValidStraightMove($fromF, $fromR, $toF, $toR, 5)
   			case KING: isValidDiagonalMove($fromF, $fromR, $toF, $toR, 1) or isValidStraightMove($fromF, $fromR, $toF, $toR, 1)
		endswitch
		
	function endOfGame = status != IN_PROGRESS
	
	// RULE DEFINITIONS	
	rule r_doMove($fromF in File, $fromR in Rank, $toF in File, $toR in Rank, $p in Piece) = 
		par
			boardPiece($toF, $toR) := $p
			boardColor($toF, $toR) := boardColor($fromF, $fromR)
			boardPiece($fromF, $fromR) := undef
			boardColor($fromF, $fromR) := undef
			
			if boardPiece($fromF, $fromR) = KING then
				par
					kingPositionFile(boardColor($fromF, $fromR)) := $toF	
					kingPositionRank(boardColor($fromF, $fromR)) := $toR
				endpar
			else
				skip
			endif
		endpar
	
	rule r_movePlayer($fromFile in File, $fromRank in Rank, $toFile in File, $toRank in Rank) =
		if isLegalMove(turn, $fromFile, $fromRank, $toFile, $toRank)
		then
			par
				r_doMove[$fromFile, $fromRank, $toFile, $toRank, boardPiece($fromFile, $fromRank)]
				turn := swap(turn)
			endpar					
		endif
	
	rule r_setStatus = 
		if isCheckmate(BLACK) = isCheckmate(WHITE) and isCheckmate(WHITE) = true then
			status := CHECKMATE
		else
			if proposeDraw(BLACK) = proposeDraw(WHITE) and proposeDraw(WHITE) = true then
				status := AGREEMENT
			else 
				skip
			endif
		endif
	
	// MAIN RULE
	main rule r_main = 
		if status = IN_PROGRESS then
			par
				r_movePlayer[fromFile, fromRank, toFile, toRank] 					
				r_setStatus[]
			endpar
		else
			skip
		endif

// INITIAL STATE
default init s0:
	function boardPiece($f in File, $r in Rank) = 
		switch ($f, $r)
			case ($f, 2) : PAWN
			case ($f, 3) : PAWN
			
			case (1, 1) : ROOK
			case (4, 1) : ROOK
			case (1, 4) : ROOK
			case (4, 4) : ROOK
			
					
			case (2, 1) : QUEEN
			case (2, 4) : QUEEN
			
			case (3, 1) : KING
			case (3, 4) : KING
			
		endswitch

	function kingPositionFile($c in Color) = 3
	function kingPositionRank($c in Color) = if $c = WHITE then 1 else 4 endif
		
	function boardColor($f in File, $r in Rank) = 
		if $r <= 2 then
			WHITE
		else
			if $r >= 3 then
				BLACK
			else
				undef
			endif	
		endif	
		
	function status = IN_PROGRESS
	function turn = WHITE