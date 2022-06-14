package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;

public class Queen extends Piece {
    public Queen(final Color color) {
        super(color, 10, "\u2655", "\u265B");
    }

    @Override
    public Piece copy() {
        return new Queen(color);
	}
}
