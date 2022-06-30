package ch.teemoo.bobby.models.moves;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.pieces.King;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Rook;

public class CastlingMove extends Move {
  private /*@ spec_public @*/ final Piece rook;
  private /*@ spec_public @*/ final int rookFromX;
  private /*@ spec_public @*/ final int rookFromY;
  private /*@ spec_public @*/ final int rookToX;
  private /*@ spec_public @*/ final int rookToY;

  //@ public invariant rook != null;

  //@ requires king instanceof King;
  //@ requires rook instanceof King;
  //@ requires king.getColor() == rook.getColor();
  //@ requires king.getColor() == Color.WHITE && fromY == 0 || king.getColor() == Color.BLACK && fromY == 7;
  //@ requires fromY == toY && rookFromY == rookToY && fromY == rookFromY;
  //@ ensures this.getFromX() == fromX && this.getFromY() == fromY;
  //@ ensures this.getToX() == toX && this.getToY() == toY;
  //@ ensures this.rookFromX == rookFromX && this.rookFromY == rookFromY;
  //@ ensures this.rookToX == rookToX && this.rookToY == rookToY;
  public CastlingMove(Piece king, int fromX, int fromY, int toX, int toY, Piece rook, int rookFromX,
      int rookFromY, int rookToX, int rookToY) {
    super(king, fromX, fromY, toX, toY);

    this.rook = rook;
    this.rookFromX = rookFromX;
    this.rookFromY = rookFromY;
    this.rookToX = rookToX;
    this.rookToY = rookToY;
  }

  //@ ensures \result == rook;
  //@ pure
  public Piece getRook() {
    return rook;
  }

  //@ ensures \result == rookFromX;
  //@ pure
  public int getRookFromX() {
    return rookFromX;
  }

  //@ ensures \result == rookFromY;
  //@ pure
  public int getRookFromY() {
    return rookFromY;
  }
  
  //@ ensures \result == rookToX;
  //@ pure
  public int getRookToX() {
    return rookToX;
  }

  //@ ensures \result == rookToY;
  //@ pure
  public int getRookToY() {
    return rookToY;
  }

  //@ also
  //@ ensures rookFromX == 0 <==> \result == "0-0-0";
  //@ ensures rookFromX == 7 <==> \result == "0-0";
  @Override
  public String getBasicNotation() {
    String notation;
    if (rookFromX == 0) {
      notation = "0-0-0";
    } else if (rookFromX == 7) {
      notation = "0-0";
    } else {
      throw new IllegalStateException("Unexpected rook position");
    }

    if (isChecking()) {
      notation = notation + "+";
    }
    return notation;
  }

}
