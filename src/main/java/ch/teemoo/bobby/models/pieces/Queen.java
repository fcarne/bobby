package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;

public class Queen extends Piece {
    public Queen(final Color color) {
        super(color, 10);
    }

    @Override
    public String getUnicode() {
    	String unicode;
        if (color == Color.WHITE) {
        	unicode = "\u2655";
        } else {
        	unicode = "\u265B";
        }
        return unicode;
    }

    @Override
    public Piece copy() {
        return new Queen(color);
	}
}
