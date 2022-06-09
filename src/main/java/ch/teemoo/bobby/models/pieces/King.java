package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;

public class King extends Piece {
    public King(final Color color) {
        super(color, 100);
    }

    @Override
    public String getUnicode() {
    	String unicode;
        if (color == Color.WHITE) {
            unicode = "\u2654";
        } else {
        	unicode ="\u265A";
        }
        return unicode;
    }

    @Override
    public Piece copy() {
        return new King(color);
	}
}
