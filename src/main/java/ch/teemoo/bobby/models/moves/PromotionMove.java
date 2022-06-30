package ch.teemoo.bobby.models.moves;

import ch.teemoo.bobby.models.pieces.King;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;

public class PromotionMove extends Move {
  private /*@ spec_public @*/ final Piece promotedPiece;

  //@ public invariant promotedPiece != null;
  
  //@ requires move.getPiece() instanceof Pawn;
  //@ requires move.getPiece().getColor() == promotedPiece.getColor();
  //@ requires !(promotedPiece instanceof King) && !(promotedPiece instanceof Pawn);
  //@ ensures this.getFromX() == move.getFromX() && this.getFromY() == move.getFromY();
  //@ ensures this.getToX() == move.getToX() && this.getToY() == move.getToY();
  //@ ensures this.isChecking() == move.isChecking();
  public PromotionMove(Move move, Piece promotedPiece) {
    super(move.getPiece(), move.getFromX(), move.getFromY(), move.getToX(), move.getToY());

    this.promotedPiece = promotedPiece;
    setChecking(move.isChecking());
    setTookPiece(move.getTookPiece());
  }

  //@ ensures \result == promotedPiece;
  //@ pure
  public Piece getPromotedPiece() {
    return promotedPiece;
  }

  @Override
  public String getPrettyNotation() {
    return super.getPrettyNotation()
        + " (promoted to "
        + getPromotedPiece().getClass().getSimpleName()
        + ")";
  }

}