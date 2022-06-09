package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;

public class Knight extends Piece {
	public Knight(final Color color) {
		super(color, 3);
	}

	@Override
	public String getUnicode() {
		String unicode;
		if (color == Color.WHITE) {
			unicode = "\u2658";
		} else {
			unicode = "\u265E";
		}
		return unicode;
	}

	@Override
	public Piece copy() {
		return new Knight(color);
	}
}
