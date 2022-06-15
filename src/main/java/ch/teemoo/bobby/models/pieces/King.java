package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;

public class King extends Piece {
  public King(final Color color) {
    super(color, 100, "♔", "♚");
  }

  @Override
  public Piece copy() {
    return new King(color);
  }
}
