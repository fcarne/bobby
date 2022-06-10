package ch.teemoo.bobby.models.moves;

import java.util.Objects;

import ch.teemoo.bobby.models.pieces.Pawn;

public class EnPassantMove extends Move {
	private final int tookPiecePosX;
	private final int tookPiecePosY;

	public EnPassantMove(Move move, int tookPiecePosX, int tookPiecePosY) {
		super(move.getPiece(), move.getFromX(), move.getFromY(), move.getToX(), move.getToY());
		
		assert getPiece() instanceof Pawn : "Only pawns can make an en passant move";
		assert move.isTaking(): "En passant move must be a taking move";
		
		this.tookPiecePosX = tookPiecePosX;
		this.tookPiecePosY = tookPiecePosY;
		setChecking(move.isChecking());
		setTookPiece(move.getTookPiece());
	}

	public int getTookPiecePosX() {
		return tookPiecePosX;
	}

	public int getTookPiecePosY() {
		return tookPiecePosY;
	}

	public String getPrettyNotation() {
		return super.getPrettyNotation() + " (en passant)";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + Objects.hash(tookPiecePosX, tookPiecePosY);
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		EnPassantMove other = (EnPassantMove) obj;
		return tookPiecePosX == other.tookPiecePosX && tookPiecePosY == other.tookPiecePosY;
	}
	
	

}
