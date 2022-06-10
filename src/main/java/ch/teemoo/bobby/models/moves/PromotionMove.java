package ch.teemoo.bobby.models.moves;

import java.util.Objects;

import ch.teemoo.bobby.models.pieces.King;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;

public class PromotionMove extends Move {
	private final Piece promotedPiece;

	public PromotionMove(Move move, Piece promotedPiece) {
		super(move.getPiece(), move.getFromX(), move.getFromY(), move.getToX(), move.getToY());

		assert getPiece() instanceof Pawn : "Promoted piece must be a pawn";
		assert promotedPiece.getColor() == getPiece().getColor() : "Promoted piece must be of the same color";
		assert !(promotedPiece instanceof King) && !(promotedPiece instanceof Pawn) : "Choosen piece must not be a king or a pawn";

		this.promotedPiece = promotedPiece;
		setChecking(move.isChecking());
		setTookPiece(move.getTookPiece());
	}

	public Piece getPromotedPiece() {
		return promotedPiece;
	}

	public String getPrettyNotation() {
		return super.getPrettyNotation() + " (promoted to " + getPromotedPiece().getClass().getSimpleName() + ")";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + Objects.hash(promotedPiece);
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
		PromotionMove other = (PromotionMove) obj;
		return Objects.equals(promotedPiece, other.promotedPiece);
	}
	
	 

	
	
}
