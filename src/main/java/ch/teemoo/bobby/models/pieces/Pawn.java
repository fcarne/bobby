package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;

public class Pawn extends Piece {
    public Pawn(final Color color) {
        super(color, 1);
    }

    @Override
    public String getUnicode() {
    	String unicode;
        if (color == Color.WHITE) {
        	unicode = "\u2659";
        } else {
        	unicode = "\u265F";
        }
        return unicode;
    }

    @Override
    public Piece copy() {
        return new Pawn(color);
	}
    
    
}
