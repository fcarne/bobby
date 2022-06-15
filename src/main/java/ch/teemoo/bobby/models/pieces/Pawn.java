package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;

public class Pawn extends Piece {
  public Pawn(final Color color) {
    super(color, 1, "♙", "♟");
  }

  @Override
  public Piece copy() {
    return new Pawn(color);
  }

}
