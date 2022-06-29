asm bobby_PC

import StandardLibrary
import CTLlibrary

signature:
	// DOMAINS
	domain Rank subsetof Integer
	domain File subsetof Integer
	
	enum domain Piece = { PAWN | BISHOP | KNIGHT | ROOK | QUEEN | KING }

	enum domain Color = { WHITE | BLACK }
	
	enum domain Status = { SETUP, IN_PROGRESS, CHECKMATE, STALEMATE, AGREEMENT }
	
	// FUNCTIONS
	
	controlled boardPiece: Prod(File, Rank) -> Piece
	controlled boardColor: Prod(File, Rank) -> Color
	controlled status: Status
	controlled turn: Color
	
	controlled lastMoveFromFile: File
	controlled lastMoveFromRank: Rank	
	controlled lastMoveToFile: File
	controlled lastMoveToRank: Rank	
	controlled movedPiece: Piece
	controlled tookPiece: Piece	
	
	controlled playerColor: Color
	monitored playerChosenColor: Color
	
	monitored fromFile: File
	monitored fromRank: Rank
	monitored toFile: File
	monitored toRank: Rank
	monitored chosenPromotionPiece: Piece
	monitored proposeDrawUser: Boolean
	
	controlled kingPositionFile: Color -> File
	controlled kingPositionRank: Color -> Rank
	controlled winner : Color
		
	static file:  Prod(File, Rank) -> File
	static rank:  Prod(File, Rank) -> Rank
		
	static swap: Color -> Color
	static between: Prod(Integer, Integer, Integer) -> Boolean
		
	static isLegalMove: Prod(File, Rank, File, Rank) -> Boolean
	static isPromotionMove: Prod(File, Rank, Rank, Color) -> Boolean
	
	static computeMoves: Prod(Color, File, Rank) -> Powerset(Prod(File, Rank))
	static filterLegalMoves: Prod(Color, File, Rank, Powerset(Prod(File, Rank))) -> Powerset(Prod(File, Rank))
	static computeStraightMoves: Prod(File, Rank, Integer) -> Powerset(Prod(File, Rank))
	static computeDiagonalMoves: Prod(File, Rank, Integer) -> Powerset(Prod(File, Rank))
	static computeLShapeMoves: Prod(File, Rank) -> Powerset(Prod(File, Rank))
	static computePawnMoves: Prod(Color, File, Rank) -> Powerset(Prod(File, Rank))

	derived computeQueenMoves: Prod(File, Rank) -> Powerset(Prod(File, Rank))
	derived computeKingMoves: Prod(File, Rank) -> Powerset(Prod(File, Rank))

	static pawnStartingRank: Color -> Rank
	static advancePawnRank: Prod(Color, Rank) -> Rank
	static boardRankEdge: Color -> Rank
	
	static isInCheckAfterMove: Prod(Color, File, Rank, File, Rank) -> Boolean
	
	static canMove: Prod(Color, File, Rank) -> Boolean
	static canMove: Color -> Boolean
	
	derived endOfGame : Boolean
	
definitions:
	// DOMAIN DEFINITIONS

	domain Rank = { 1 : 8 }
	domain File = { 1 : 8 }
		
	// FUNCTION DEFINITIONS
	
	function file($f in File, $r in Rank) = $f
	function rank($f in File, $r in Rank) = $r
	
	function swap($c in Color) = if $c = WHITE then BLACK else WHITE endif
	
	function between($x in Integer, $a in Integer, $b in Integer) =
		if $a < $b then
			$a < $x and $x < $b
		else
			$b < $x and $x < $a 
		endif

	function isLegalMove($fromF in File, $fromR in Rank, $toF in File, $toR in Rank) = 
		isDef(boardPiece($fromF, $fromR)) and boardColor($fromF, $fromR) = turn and ($fromF != $toF or $fromR != $toR)
			and ( isDef(boardColor($toF, $toR)) implies boardColor($toF, $toR) != turn)
			
	function isPromotionMove($fromF in File, $fromR in Rank, $toR in Rank, $c in Color) =
		boardPiece($fromF, $fromR) = PAWN and $toR = boardRankEdge($c)
	
	function computeDiagonalMoves($fromF in File, $fromR in Rank, $limit in Integer) =
		{ 
			$toF in File, $toR in Rank | abs($fromF - $toF) = abs($fromR - $toR) and abs($fromF - $toF) <= $limit and
				(forall $f1 in File, $r1 in Rank with 
					(between($f1, $fromF, $toF) and between($r1, $fromR, $toR) and abs($fromF - $f1) = abs($fromR - $r1)) 
						implies (isUndef(boardPiece($f1, $r1)))
				): ($toF, $toR)
		}

	function computeStraightMoves($fromF in File, $fromR in Rank, $limit in Integer) =
		{ 
			$toF in File, $toR in Rank | ($fromF - $toF = 0 or $fromR - $toR = 0) and ($fromF - $toF) + ($fromR - $toR) <= $limit and
				(forall $f1 in File, $r1 in Rank with 
					((between($f1, $fromF, $toF) or between($r1, $fromR, $toR)) and ($fromF - $f1 = 0 or $fromR - $r1 = 0)) 
						implies (isUndef(boardPiece($f1, $r1)))
				): ($toF, $toR)
		}

	function computeLShapeMoves($fromF in File, $fromR in Rank) =
		{ $toF in File, $toR in Rank | abs($fromF - $toF) * abs($fromR- $toR) = 2: ($toF, $toR) }
	
	function pawnStartingRank($c in Color) = if $c = WHITE then 2 else 7 endif
	function advancePawnRank($c in Color, $r in Rank) = if $c = WHITE then $r + 1 else $r - 1 endif
	function boardRankEdge($c in Color) = if $c = WHITE then 8 else 1 endif

	function computePawnMoves($c in Color, $fromF in File, $fromR in Rank) = 
		{
			$toF in File, $toR in Rank | 
				(between($fromR, 0, 9) and $fromF = $toF and $toR = advancePawnRank($c, $fromR)) or
				($fromR = pawnStartingRank($c) and $fromF = $toF and $toR = advancePawnRank($c, advancePawnRank($c, $fromR))) or
				(isDef(boardPiece($fromF + 1, advancePawnRank($c, $fromR))) and $toF = $fromF + 1 and $toR = advancePawnRank($c, $fromR)) or
				(isDef(boardPiece($fromF - 1, advancePawnRank($c, $fromR))) and $toF = $fromF - 1 and $toR = advancePawnRank($c, $fromR))				 							
				: ($toF, $toR) 
		}


	function computeQueenMoves($f in File, $r in Rank) =  union(computeDiagonalMoves($f, $r, 8), computeStraightMoves($f, $r, 8))
	function computeKingMoves($f in File, $r in Rank) =  union(computeDiagonalMoves($f, $r, 1), computeStraightMoves($f, $r, 1))

	function filterLegalMoves($c in Color, $fromF in File, $fromR in Rank, $moves in Powerset(Prod(File, Rank))) = 
		let ($kingFile = kingPositionFile(swap($c)), $kingRank = kingPositionRank(swap($c))) in 
			{
				$f in File, $r in Rank | contains($moves,($f, $r)) and ($f != $kingFile or $r != $kingRank) and 
				(boardPiece($fromF, $fromR) = KING implies max(abs($kingFile - $f), abs($kingRank - $r) ) > 1) and
				not isInCheckAfterMove($c, $fromF, $fromR, $f, $r) : ($f, $r)
			}
		endlet
	
	function isInCheckAfterMove($c in Color, $fromF in File, $fromR in Rank, $toF in File, $toR in Rank) =
		let ($kingFile = kingPositionFile($c), $kingRank = kingPositionRank($c)) in
			(exist $fN in File, $rN in Rank with contains(computeLShapeMoves($kingFile, $kingRank), ($fN, $rN))
				and (
					(isDef(boardPiece($fN, $rN)) and boardPiece($fN, $rN) = KNIGHT and boardColor($fN, $rN) = swap($c) ) or
					($fN = $toF and $rN = $toR and boardPiece($fromF, $fromR) = KNIGHT and boardColor($fromF, $fromR) = swap($c))
				)			
			) or
			(exist $fB in File, $rB in Rank with contains(computeDiagonalMoves($kingFile, $kingRank, 8), ($fB, $rB))
				and (
					(isDef(boardPiece($fB, $rB)) and (boardPiece($fB, $rB) = BISHOP or boardPiece($fB, $rB) = QUEEN) and boardColor($fB, $rB) = swap($c) ) or
					($fB = $toF and $rB = $toR and (boardPiece($fromF, $fromR) = QUEEN or boardPiece($fromF, $fromR) = BISHOP) and boardColor($fromF, $fromR) = swap($c))
				)			
			) or
			(exist $fR in File, $rR in Rank with contains(computeStraightMoves($kingFile, $kingRank, 8), ($fR, $rR))
				and (
					(isDef(boardPiece($fR, $rR)) and (boardPiece($fR, $rR) = ROOK or boardPiece($fR, $rR) = QUEEN) and boardColor($fR, $rR) = swap($c) ) or
					($fR = $toF and $rR = $toR and (boardPiece($fromF, $fromR) = ROOK or boardPiece($fromF, $fromR) = QUEEN) and boardColor($fromF, $fromR) = swap($c))
				)			
			) or
			(exist $fP in File, $rP in Rank with contains(computePawnMoves($c, $kingFile, $kingRank), ($fP, $rP))
				and (
					(isDef(boardPiece($fP, $rP)) and boardPiece($fP, $rP) = PAWN and boardColor($fP, $rP) = swap($c) ) or
					($fP = $toF and $rP = $toR and boardPiece($fromF, $fromR) = PAWN and boardColor($fromF, $fromR) = swap($c))
				)			
			)
		endlet
		
	function computeMoves($c in Color, $f in File, $r in Rank) = filterLegalMoves($c, $f, $r,
		switch boardPiece($f, $r)
			case PAWN : computePawnMoves($c, $f, $r)
   			case KNIGHT : computeLShapeMoves($f,$r)
   			case BISHOP : computeDiagonalMoves($f, $r, 8)
   			case ROOK : computeStraightMoves($f, $r, 8)
   			case QUEEN : computeQueenMoves($f, $r)
   			case KING: computeKingMoves($f, $r)
		endswitch
	)
	
	function canMove($c in Color, $f in File, $r in Rank) = notEmpty(computeMoves($c, $f, $r))
	function canMove($c in Color) = (exist $f in File, $r in Rank with isDef(boardColor($f, $r)) and boardColor($f, $r) = $c and canMove($c, $f, $r))
	
	function endOfGame = status != SETUP and status != IN_PROGRESS
	
	// RULE DEFINITIONS
	rule r_setup($c in Color) = 
		par
			turn := WHITE
			playerColor := $c
			status := IN_PROGRESS
		endpar
	
	rule r_updateLastMove($fromF in File, $fromR in Rank, $toF in File, $toR in Rank) = 
		par
			lastMoveFromFile := $fromF
			lastMoveFromRank := $fromR
			lastMoveToFile := $toF
			lastMoveToRank := $toR
			movedPiece := boardPiece($fromF, $fromR)
			tookPiece := boardPiece($toF, $toR)
		endpar
	
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
			
			r_updateLastMove[$fromF, $fromR, $toF, $toR]
		endpar
	
	rule r_movePlayer($fromFile in File, $fromRank in Rank, $toFile in File, $toRank in Rank) =
		if isLegalMove($fromFile, $fromRank, $toFile, $toRank) and (exist $f in File, $r in Rank
			with contains(computeMoves(turn, $fromFile, $fromRank), ($toFile, $toRank))) 
		then
			par
				if isPromotionMove($fromFile, $fromRank, $toRank, turn) then
					r_doMove[$fromFile, $fromRank, $toFile, $toRank, 
						if chosenPromotionPiece != PAWN and chosenPromotionPiece != KING then 
							chosenPromotionPiece 
						else 
							QUEEN 
						endif
					]
				else 
					r_doMove[$fromFile, $fromRank, $toFile, $toRank, boardPiece($fromFile, $fromRank)]
				endif
				turn := swap(turn)
			endpar					
		endif
	
	rule r_movePC = 
		choose $fromF in File, $fromR in Rank with canMove(turn, $fromF, $fromR) do
			let ($to = chooseone(computeMoves(turn, $fromF, $fromR))) in
				par
					if isPromotionMove($fromF, $fromR, rank($to), turn) then
						r_doMove[$fromF, $fromR, file($to), rank($to), QUEEN]
					else 
						r_doMove[$fromF, $fromR, file($to), rank($to), boardPiece($fromF, $fromR)]
					endif
					turn := swap(turn)
				endpar
			endlet

	
	rule r_setStatus = 
		if not canMove(turn) then
			if isInCheckAfterMove(turn, lastMoveFromFile, lastMoveFromRank, lastMoveToFile, lastMoveToRank) then
				par
					status := CHECKMATE
					winner := swap(turn)
				endpar
			else
				status := STALEMATE
			endif
		else
			choose $draw in Boolean with true do
				if $draw = proposeDrawUser and $draw = true then
					status := AGREEMENT
				else 
					skip
				endif
		endif
		
	
	CTLSPEC ef(winner = WHITE) // VERO -> il bianco può vincere
	CTLSPEC ef(winner = BLACK) // VERO -> il nero può vincere
	CTLSPEC not ef(winner = playerColor) // FALSO -> trovo un controesempio di partita in cui vince l'utente
	CTLSPEC af(endOfGame) // VERO -> la partita finisce sempre
	CTLSPEC ag(endOfGame implies ag(endOfGame)) // VERO -> se la partità è finita, non si può fare altro
	
	CTLSPEC ag((exist $fW in File, $rW in Rank with boardPiece($fW, $rW) = KING and boardColor($fW, $rW) = WHITE) and 
			(exist $fB in File, $rB in Rank with boardPiece($fB,$rB) = KING and boardColor($fB, $rB) = BLACK)) // VERO -> i due re non possono mai essere mangiati
			
	CTLSPEC not ef(status = STALEMATE) // FALSO -> trovo un controesempio di partita che finisce in stallo
	CTLSPEC ef(status = AGREEMENT) // VERO -> c'è la possibilità che la partita finisca in un pareggio accordato
	CTLSPEC aw(not endOfGame, ef(status = AGREEMENT) and not endOfGame) // VERO -> è sempre possibile che la partita finisca in pareggio (prima che la partita finisca)

	CTLSPEC ag((movedPiece = PAWN and turn = WHITE and lastMoveToRank = 8 and lastMoveToFile = 1) implies ax(boardPiece(1, 8) != PAWN)) // VERO -> se la mossa scelta porta un pedone bianco al bordo, allora dev'essere promosso

	CTLSPEC ag(turn != playerColor implies ax(turn = playerColor)) // VERO -> il PC esegue una mossa sempre valida
	CTLSPEC ag(turn != playerColor implies ax(turn = playerColor)) // FALSO -> se sceglie una mossa non valida il turno resta in mano sua

	// MAIN RULE
	main rule r_main = 
		switch status
			case SETUP : r_setup[playerChosenColor]
			case IN_PROGRESS : 
				par
					if turn = playerColor then 
						r_movePlayer[fromFile, fromRank, toFile, toRank] 
					else
						r_movePC[]
					endif
										
					r_setStatus[]
				endpar
		endswitch

// INITIAL STATE
default init s0:
	function boardPiece($f in File, $r in Rank) =
		switch ($f, $r)
			case ($f, 2) : PAWN
			case ($f, 7) : PAWN
			
			case (1, 1) : ROOK
			case (8, 1) : ROOK
			case (1, 8) : ROOK
			case (8, 8) : ROOK
			
			case (2, 1) : KNIGHT
			case (7, 1) : KNIGHT
			case (2, 8) : KNIGHT
			case (7, 8) : KNIGHT
					
			case (3, 1) : BISHOP
			case (6, 1) : BISHOP
			case (3, 8) : BISHOP
			case (6, 8) : BISHOP
			
			case (4, 1) : QUEEN
			case (4, 8) : QUEEN
			
			case (5, 1) : KING
			case (5, 8) : KING
			
		endswitch
	
	function kingPositionFile($c in Color) = 5
	function kingPositionRank($c in Color) = if $c = WHITE then 1 else 8 endif
		
	function boardColor($f in File, $r in Rank) = 
		if $r = 1 or $r = 2 then
			WHITE
		else
			if $r = 7 or $r = 8 then
				BLACK
			else
				undef
			endif	
		endif	
		
	function status = SETUP	