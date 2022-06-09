package ch.teemoo.bobby.models;

public enum Color {
	WHITE, BLACK;

	public Color opposite() {
		switch (this) {
		case WHITE:
			return BLACK;
		default:
			assert this == BLACK;
			return WHITE;
		}
	}
}
