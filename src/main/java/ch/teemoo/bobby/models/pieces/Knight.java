package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;

public class Knight extends Piece {
	public Knight(final Color color) {
		super(color, 3, "\u2658", "\u265E");
	}

	@Override
	public Piece copy() {
		return new Knight(color);
	}
}
