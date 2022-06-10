package ch.teemoo.bobby.models.pieces;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatIllegalArgumentException;
import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.params.provider.Arguments.arguments;

import java.util.stream.Stream;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import ch.teemoo.bobby.models.Color;;

public class PieceTest {

	@ParameterizedTest
	@MethodSource("providePieces")
	public void pieceConstrucor_ok_returnsCorrectPiece(Piece piece, String unicode, int value) {
		assertAll(() -> assertThat(piece.getUnicode()).isEqualTo(unicode),
				() -> assertThat(piece.getValue()).isEqualTo(value));
	}

	@ParameterizedTest
	@MethodSource("providePieces")
	public void copy_ok_returnsEqual(Piece piece) {
		Piece copy = piece.copy();
		assertAll(() -> assertThat(copy.color).isEqualTo(piece.color),
				() -> assertThat(copy.getValue()).isEqualTo(piece.getValue()));
	}

	private static Stream<Arguments> providePieces() {
		return Stream.of(arguments(new Bishop(Color.BLACK), "♝", 3), arguments(new Bishop(Color.WHITE), "♗", 3),
				arguments(new King(Color.BLACK), "♚", 100), arguments(new King(Color.WHITE), "♔", 100),
				arguments(new Knight(Color.BLACK), "♞", 3), arguments(new Knight(Color.WHITE), "♘", 3),
				arguments(new Pawn(Color.BLACK), "♟", 1), arguments(new Pawn(Color.WHITE), "♙", 1),
				arguments(new Rook(Color.BLACK), "♜", 5), arguments(new Rook(Color.WHITE), "♖", 5),
				arguments(new Queen(Color.BLACK), "♛", 10), arguments(new Queen(Color.WHITE), "♕", 10));
	}

	@ParameterizedTest
	@MethodSource
	public void fromUnicodeChar_correctChar_returnsCorrectPiece(char c, Class<?> clazz, Color color) {
		assertThat(Piece.fromUnicodeChar(c)).isInstanceOf(clazz).hasFieldOrPropertyWithValue("color", color);
	}

	private static Stream<Arguments> fromUnicodeChar_correctChar_returnsCorrectPiece() {
		return Stream.of(arguments('♝', Bishop.class, Color.BLACK), arguments('♗', Bishop.class, Color.WHITE),
				arguments('♚', King.class, Color.BLACK), arguments('♔', King.class, Color.WHITE),
				arguments('♞', Knight.class, Color.BLACK), arguments('♘', Knight.class, Color.WHITE),
				arguments('♟', Pawn.class, Color.BLACK), arguments('♙', Pawn.class, Color.WHITE),
				arguments('♜', Rook.class, Color.BLACK), arguments('♖', Rook.class, Color.WHITE),
				arguments('♛', Queen.class, Color.BLACK), arguments('♕', Queen.class, Color.WHITE));
	}

	@Test
	public void fromUnicodeChar_unknownChar_throwsException() {
		char c = 'a';
		assertThatIllegalArgumentException().isThrownBy(() -> Piece.fromUnicodeChar(c));
	}

	@ParameterizedTest
	@MethodSource
	public void equals_sameOrEqual_returnTrue(Piece piece, Piece other) {
		assertThat(piece).isEqualTo(other).hasSameHashCodeAs(other);
	}

	private static Stream<Arguments> equals_sameOrEqual_returnTrue() {
		Piece pawn = new Pawn(Color.WHITE);
		Piece other = new Pawn(Color.WHITE);
		return Stream.of(arguments(pawn, pawn), arguments(pawn, other));
	}

	@ParameterizedTest
	@MethodSource
	public void equals_nullOrNotEqual_returnFalse(Piece piece, Piece other) {
		assertThat(piece).isNotEqualTo(other);
		if (other != null)
			assertThat(piece).doesNotHaveSameHashCodeAs(other);
	}

	private static Stream<Arguments> equals_nullOrNotEqual_returnFalse() {
		Piece pawn = new Pawn(Color.WHITE);
		Piece rook = new Rook(Color.WHITE);
		Piece blackPawn = new Pawn(Color.BLACK);

		return Stream.of(arguments(pawn, null), arguments(pawn, rook), arguments(pawn, blackPawn));
	}

}
