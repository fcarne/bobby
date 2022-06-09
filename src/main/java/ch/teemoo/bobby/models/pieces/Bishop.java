package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;

public class Bishop extends Piece {
	public Bishop(final Color color) {
		super(color, 3);
	}

	@Override
	public String getUnicode() {
		String unicode;
		if (color == Color.WHITE) {
			unicode = "\u2657";
		} else {
			unicode = "\u265D";
		}
		return unicode;
	}

	@Override
	public Piece copy() {
		return new Bishop(color);
	}
}
