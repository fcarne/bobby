package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;

public class Rook extends Piece {
    public Rook(Color color) {
        super(color, 5, "\u2656", "\u265C");
    }

    @Override
    public Piece copy() {
        return new Rook(color);
	}
}
