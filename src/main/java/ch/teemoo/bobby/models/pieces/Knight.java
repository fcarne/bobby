package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;

public class Knight extends Piece {
  public Knight(final Color color) {
    super(color, 3, "♘", "♞");
  }

  @Override
  public Piece copy() {
    return new Knight(color);
  }
}
