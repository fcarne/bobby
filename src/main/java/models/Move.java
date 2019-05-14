package models;

import java.util.Objects;

import models.pieces.Piece;

public class Move {
	private final Piece piece;
	private final int fromX;
	private final int fromY;
	private final int toX;
	private final int toY;
	private boolean isTaking;
	private boolean isChecking;

	public Move(Piece piece, int fromX, int fromY, int toX, int toY) {
		this.piece = piece;
		this.fromX = fromX;
		this.fromY = fromY;
		this.toX = toX;
		this.toY = toY;
	}

	public Piece getPiece() {
		return piece;
	}

	public int getFromX() {
		return fromX;
	}

	public int getFromY() {
		return fromY;
	}

	public int getToX() {
		return toX;
	}

	public int getToY() {
		return toY;
	}

	public boolean isTaking() {
		return isTaking;
	}

	public void setTaking(boolean taking) {
		isTaking = taking;
	}

	public boolean isChecking() {
		return isChecking;
	}

	public void setChecking(boolean checking) {
		isChecking = checking;
	}

	public String getPrettyNotation() {
		StringBuilder builder = new StringBuilder()
			.append(piece.getColor())
			.append(" ")
			.append(getBasicNotation())
			.append(" (")
			.append(piece.getClass().getSimpleName())
			.append(")");
		return builder.toString();
	}

	public String getBasicNotation() {
		StringBuilder builder = new StringBuilder();
		builder.append(convertXToChar(fromX))
			.append(fromY + 1)
			.append("-")
			.append(convertXToChar(toX))
			.append(toY + 1);
		if (isChecking) {
			builder.append("+");
		}
		return builder.toString();
	}

	public static Move fromBasicNotation(String notation) {
		if (notation == null || notation.length() < 5) {
			//todo: improve with regex
			throw new RuntimeException("Unexpected format for basic notation move: " + notation);
		}
		char fromXChar = notation.charAt(0);
		char fromYChar = notation.charAt(1);
		char toXChar = notation.charAt(3);
		char toYChar = notation.charAt(4);

		Move move = new Move(null, convertCharToX(fromXChar), Character.getNumericValue(fromYChar) - 1,
				convertCharToX(toXChar), Character.getNumericValue(toYChar) - 1);

		if (notation.length() > 5) {
			char checkChar = notation.charAt(5);
			if (checkChar == '!') {
				move.setChecking(true);
			}
		}

		return move;
	}

	private static String convertXToChar(int x) {
		final int aAscii = (int) 'a';
		return String.valueOf((char) (aAscii + x));
	}

	private static int convertCharToX(char character) {
		final int aAscii = (int) 'a';
		final int charAscii = (int) character;
		return charAscii - aAscii;
	}

	public boolean equalsForPositions(Move move) {
		return fromX == move.fromX && fromY == move.fromY && toX == move.toX && toY == move.toY;
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Move move = (Move) o;
		return equalsForPositions(move)
			&& isTaking == move.isTaking && isChecking == move.isChecking && Objects.equals(piece, move.piece);
	}

	@Override
	public int hashCode() {
		return Objects.hash(piece, fromX, fromY, toX, toY, isTaking, isChecking);
	}

	@Override
	public String toString() {
		return getPrettyNotation();
	}
}
