package ch.teemoo.bobby.models.moves;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.pieces.King;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Rook;

public class CastlingMove extends Move {
  private final Piece rook;
  private final int rookFromX;
  private final int rookFromY;
  private final int rookToX;
  private final int rookToY;

  public CastlingMove(Piece king, int fromX, int fromY, int toX, int toY, Piece rook, int rookFromX,
      int rookFromY, int rookToX, int rookToY) {
    super(king, fromX, fromY, toX, toY);

    assert king instanceof King : "First moving piece must be a King";
    assert rook instanceof Rook : "Second moving piece must be a Rook";
    assert king.getColor() == rook.getColor() : "King & Rook must be of the same color";
    assert king.getColor() == Color.WHITE && fromY == 0
        || king.getColor() == Color.BLACK && fromY == 7;

    this.rook = rook;
    this.rookFromX = rookFromX;
    this.rookFromY = rookFromY;
    this.rookToX = rookToX;
    this.rookToY = rookToY;
  }

  public Piece getRook() {
    return rook;
  }

  public int getRookFromX() {
    return rookFromX;
  }

  public int getRookFromY() {
    return rookFromY;
  }

  public int getRookToX() {
    return rookToX;
  }

  public int getRookToY() {
    return rookToY;
  }

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
