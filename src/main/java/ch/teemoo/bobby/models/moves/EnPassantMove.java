package ch.teemoo.bobby.models.moves;

import ch.teemoo.bobby.models.pieces.Pawn;

public class EnPassantMove extends Move {
  private /*@ spec_public @*/ final int tookPiecePosX;
  private /*@ spec_public @*/ final int tookPiecePosY;

  //@ requires move.getPiece() instanceof Pawn;
  //@ requires move.isTaking();
  //@ ensures this.getFromX() == move.getFromX() && this.getFromY() == move.getFromY();
  //@ ensures this.getToX() == move.getToX() && this.getToY() == move.getToY();
  //@ ensures this.isChecking() == move.isChecking();
  //@ ensures this.tookPiecePosX == tookPiecePosX;
  //@ ensures this.tookPiecePosY == tookPiecePosY;
  public EnPassantMove(Move move, int tookPiecePosX, int tookPiecePosY) {
    super(move.getPiece(), move.getFromX(), move.getFromY(), move.getToX(), move.getToY());
    this.tookPiecePosX = tookPiecePosX;
    this.tookPiecePosY = tookPiecePosY;
    setChecking(move.isChecking());
    setTookPiece(move.getTookPiece());
  }

  //@ ensures \result == tookPiecePosX;
  //@ pure
  public int getTookPiecePosX() {
    return tookPiecePosX;
  }

  //@ ensures \result == tookPiecePosY;
  //@ pure
  public int getTookPiecePosY() {
    return tookPiecePosY;
  }
  
  @Override
  public String getPrettyNotation() {
    return super.getPrettyNotation() + " (en passant)";
  }

}
