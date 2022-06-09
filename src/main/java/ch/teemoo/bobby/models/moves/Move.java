package ch.teemoo.bobby.models.moves;

import java.util.Objects;

import ch.teemoo.bobby.models.Board;
import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;

public class Move {
	private final Piece piece;
	private final int fromX;
	private final int fromY;
	private final int toX;
	private final int toY;
	private Piece tookPiece;
	private boolean isChecking;

	public Move(Piece piece, int fromX, int fromY, int toX, int toY) {
		this.piece = piece;
		this.fromX = fromX;
		this.fromY = fromY;
		this.toX = toX;
		this.toY = toY;
		this.tookPiece = null;
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
		return tookPiece != null;
	}

	public Piece getTookPiece() {
		return tookPiece;
	}

	public void setTookPiece(Piece tookPiece) {
		this.tookPiece = tookPiece;
	}

	public boolean isChecking() {
		return isChecking;
	}

	public void setChecking(boolean checking) {
		isChecking = checking;
	}

	public String getPrettyNotation() {
		StringBuilder builder = new StringBuilder().append(piece.getColor()).append(" ").append(getBasicNotation())
				.append(" (").append(piece.getClass().getSimpleName()).append(")");
		return builder.toString();
	}

	public String getBasicNotation() {
		StringBuilder builder = new StringBuilder();
		builder.append(convertXToChar(fromX)).append(fromY + 1).append(isTaking() ? "x" : "-")
				.append(convertXToChar(toX)).append(toY + 1);
		if (isChecking) {
			builder.append("+");
		}
		return builder.toString();
	}

	public static Move fromBasicNotation(String notation, Color color, Board board) {
		if (notation == null || color == null) {
			throw new IllegalArgumentException(
					"Unexpected format for basic notation move: " + notation + " (" + color + ")");
		}

		Move move;
		if (notation.contains("0-0-0")) {
			int y = color == Color.WHITE ? 0 : 7;
			Piece king = board.getPiece(4, y).orElseThrow(() -> new RuntimeException("There is no king at (4, " + y + ")"));
			Piece rook = board.getPiece(0, y).orElseThrow(() -> new RuntimeException("There is no rook at (0, " + y + ")"));
			move = new CastlingMove(king, 4, y, 2, y, rook, 0, y, 3, y);
			
			if (notation.indexOf('+') > -1) {
				move.setChecking(true);
			}
			return move;
		} else if (notation.contains("0-0")) {
			int y = color == Color.WHITE ? 0 : 7;
			Piece king = board.getPiece(4, y).orElseThrow(() -> new RuntimeException("There is no king at (4, " + y + ")"));
			Piece rook = board.getPiece(0, y).orElseThrow(() -> new RuntimeException("There is no rook at (7, " + y + ")"));
			move = new CastlingMove(king, 4, y, 6, y, rook, 7, y, 5, y);

			if (notation.indexOf('+') > -1) {
				move.setChecking(true);
			}
			return move;
		}

		if (notation.length() < 5) {
			// todo: improve with regex
			throw new IllegalArgumentException("Unexpected format for basic notation move: " + notation);
		}
		char fromXChar = notation.charAt(0);
		char fromYChar = notation.charAt(1);
		char takingChar = notation.charAt(2);
		char toXChar = notation.charAt(3);
		char toYChar = notation.charAt(4);

		int toX = convertCharToX(toXChar);
		int toY = Character.getNumericValue(toYChar) - 1;

		move = new Move(null, convertCharToX(fromXChar), Character.getNumericValue(fromYChar) - 1, toX, toY);

		if (notation.indexOf('+') > -1) {
			move.setChecking(true);
		}

		if (takingChar == 'x') {
			// fixme: do not know here what piece is on the board at this place but we must
			// mark the move as taking
			move.setTookPiece(board.getPiece(toX, toY).orElse(new Pawn(color.opposite())));
		}

		return move;
	}

	public static String convertXToChar(int x) {
		final int aAscii = (int) 'a';
		return String.valueOf((char) (aAscii + x));
	}

	public static int convertCharToX(char character) {
		final int aAscii = (int) 'a';
		final int charAscii = (int) character;
		return charAscii - aAscii;
	}

	public boolean equalsForPositions(Move move) {
		return fromX == move.fromX && fromY == move.fromY && toX == move.toX && toY == move.toY;
	}

	@Override
	public boolean equals(Object o) {
		if (this == o)
			return true;
		if (o == null || getClass() != o.getClass())
			return false;
		Move move = (Move) o;
		return equalsForPositions(move) && tookPiece == move.tookPiece && isChecking == move.isChecking
				&& Objects.equals(piece, move.piece);
	}

	@Override
	public int hashCode() {
		return Objects.hash(piece, fromX, fromY, toX, toY, tookPiece, isChecking);
	}

	@Override
	public String toString() {
		return getPrettyNotation();
	}
}
