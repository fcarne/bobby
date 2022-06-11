package ch.teemoo.bobby.models.moves;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatIllegalArgumentException;
import static org.junit.jupiter.params.provider.Arguments.arguments;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.Mockito.when;

import java.util.Optional;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.MethodSource;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import ch.teemoo.bobby.models.Board;
import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.pieces.King;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Rook;

@ExtendWith(MockitoExtension.class)
class MoveTest {

	@Mock
	Board board;

	@Test
	public void moveConstructor_ok_returnsCorrect() {
		Piece rook = new Rook(Color.WHITE);
		Piece pawn = new Pawn(Color.BLACK);
		Move move = new Move(rook, 0, 0, 0, 5);

		assertThat(move.getPiece()).isEqualTo(rook);
		assertThat(move.getFromX()).isEqualTo(0);
		assertThat(move.getFromY()).isEqualTo(0);
		assertThat(move.getToX()).isEqualTo(0);
		assertThat(move.getToY()).isEqualTo(5);
		assertThat(move.isTaking()).isFalse();
		assertThat(move.isChecking()).isFalse();

		move.setTookPiece(pawn);
		assertThat(move.isTaking()).isTrue();
		assertThat(move.getTookPiece()).isEqualTo(pawn);

	}

	@Test
	public void convertCharToX_charA_returns0() {
		assertThat(Move.convertCharToX('a')).isEqualTo(0);
	}

	@Test
	public void convertXToChar_int0_returnsA() {
		assertThat(Move.convertXToChar(0)).isEqualTo("a");
	}

	@Test
	public void toString__returnsPrettyNotation() {
		Move move = new Move(new Rook(Color.WHITE), 0, 0, 0, 5);
		assertThat(move.toString()).isEqualTo(move.getPrettyNotation());
	}

	@Test
	public void equalsForPosition_equals_returnTrue() {
		Move move = new Move(new Rook(Color.WHITE), 0, 0, 0, 5);
		Move other = new Move(new Rook(Color.BLACK), move.getFromX(), move.getFromY(), move.getToX(), move.getToY());
		assertThat(move.equalsForPositions(other)).isTrue();
		assertThat(move.equals(other)).isFalse();
	}

	@ParameterizedTest
	@CsvSource({ "1,0,0,5", "0,1,0,5", "0,0,1,5", "0,0,0,6" })
	public void equalsForPosition_differentCoordinate_returnFalse(int fromX, int fromY, int toX, int toY) {
		Move move = new Move(new Rook(Color.WHITE), 0, 0, 0, 5);
		Move other = new Move(new Rook(Color.BLACK), fromX, fromY, toX, toY);
		assertThat(move.equalsForPositions(other)).isFalse();
	}

	@ParameterizedTest
	@MethodSource
	public void equals_equalOrSame_returnTrue(Move move, Move other) {
		assertThat(move).isEqualTo(other).hasSameHashCodeAs(other);
	}

	private static Stream<Arguments> equals_equalOrSame_returnTrue() {
		Piece rook = new Rook(Color.WHITE);
		Move move = new Move(rook, 0, 0, 0, 5);
		Move other = new Move(rook, 0, 0, 0, 5);
		return Stream.of(arguments(move, other), arguments(move, move));
	}

	@ParameterizedTest
	@MethodSource
	public void equals_nullOrDifferent_returnFalse(Move move, Object other) {
		assertThat(move).isNotEqualTo(other);
		if (other != null)
			assertThat(move).doesNotHaveSameHashCodeAs(other);
	}

	private static Stream<Arguments> equals_nullOrDifferent_returnFalse() {
		Piece rook = new Rook(Color.WHITE);
		Move move = new Move(rook, 0, 0, 0, 5);
		
		Move differentPosition = new Move(rook, 7, 0, 7, 5);
		
		Move differentTookPiece = new Move(rook, 0, 0, 0, 5);
		differentTookPiece.setTookPiece(new Pawn(Color.BLACK));
		
		Move differentChecking = new Move(rook, 0, 0, 0, 5);
		differentChecking.setChecking(true);
		
		Move differentPiece = new Move(new Pawn(Color.WHITE),0,0,0,5);
		
		return Stream.of(
				arguments(move, null), 
				arguments(move, new Object()), 
				arguments(move, differentPosition),
				arguments(move, differentTookPiece),
				arguments(move, differentChecking),
				arguments(move, differentPiece)
				);
	}

	@Test
	public void equals_differentPiece_returnFalse() {
		Piece rook1 = new Rook(Color.WHITE);
		Piece pawn = new Pawn(Color.WHITE);
		Move move = new Move(rook1, 0, 0, 0, 5);
		Move move2 = new Move(pawn, 0, 0, 1, 5);
		assertThat(move.equals(move2)).isFalse();
		assertThat(move).doesNotHaveSameHashCodeAs(move2);
	}

	@Test
	public void getBasicNotation_notTaking_returnsHyphen() {
		Piece rook = new Rook(Color.WHITE);
		Move move = new Move(rook, 0, 0, 0, 5);
		assertThat(move.getBasicNotation()).isEqualTo("a1-a6");
	}

	@Test
	public void getBasicNotation_isTaking_returnsX() {
		Piece rook = new Rook(Color.WHITE);
		Move move = new Move(rook, 0, 0, 0, 5);
		move.setTookPiece(new Pawn(Color.BLACK));
		assertThat(move.getBasicNotation()).isEqualTo("a1xa6");
	}

	@Test
	public void getBasicNotation_isChecking_returnsPlus() {
		Piece rook = new Rook(Color.WHITE);
		Move move = new Move(rook, 0, 0, 0, 5);
		move.setChecking(true);
		assertThat(move.getBasicNotation()).isEqualTo("a1-a6+");
	}

	@Test
	public void getPrettyNotation_notTakingNorChecking_returnsCorrect() {
		Piece rook = new Rook(Color.WHITE);
		Move move = new Move(rook, 0, 0, 0, 5);
		assertThat(move.getPrettyNotation()).isEqualTo("WHITE a1-a6 (Rook)");
	}

	@ParameterizedTest
	@CsvSource({ "a1-a6,0,0,0,5,false,false", "a1-a6+,0,0,0,5,false,true", "a1xa6,0,0,0,5,true,false" })
	public void fromBasicNotation_normalMove_returnsCorrect(String notation, int fromX, int fromY, int toX, int toY,
			boolean isTaking, boolean isChecking) {

		when(board.getPiece(anyInt(), anyInt())).thenReturn(Optional.of(new Pawn(Color.BLACK)));

		Move move = Move.fromBasicNotation(notation, Color.WHITE, board);

		assertThat(move.getBasicNotation()).isEqualTo(notation);
		assertThat(move.isChecking()).isEqualTo(isChecking);
		assertThat(move.isTaking()).isEqualTo(isTaking);

		if (!isTaking)
			assertThat(move.getTookPiece()).isNull();
		else
			assertThat(move.getTookPiece()).isNotNull();

		assertThat(move.getFromX()).isEqualTo(fromX);
		assertThat(move.getFromY()).isEqualTo(fromY);
		assertThat(move.getToX()).isEqualTo(toX);
		assertThat(move.getToY()).isEqualTo(toY);
	}

	@ParameterizedTest
	@CsvSource({ "0-0,WHITE,4,0,6,0,7,0,5,0,false", "0-0+,BLACK,4,7,6,7,7,7,5,7,true",
			"0-0-0+,WHITE,4,0,2,0,0,0,3,0,true", "0-0-0,BLACK,4,7,2,7,0,7,3,7,false" })
	public void fromBasicNotation_CastlingMove_returnsCastlingMove(String notation, Color color, int fromX, int fromY,
			int toX, int toY, int rookFromX, int rookFromY, int rookToX, int rookToY, boolean isChecking) {

		when(board.getPiece(fromX, fromY)).thenReturn(Optional.of(new King(color)));
		when(board.getPiece(rookFromX, rookFromY)).thenReturn(Optional.of(new Rook(color)));

		Move move = Move.fromBasicNotation(notation, color, board);

		assertThat(move).isInstanceOf(CastlingMove.class);
		assertThat(move.getBasicNotation()).isEqualTo(notation);
		assertThat(move.isChecking()).isEqualTo(isChecking);

		CastlingMove cmove = (CastlingMove) move;
		assertThat(cmove.getFromX()).isEqualTo(fromX);
		assertThat(cmove.getFromY()).isEqualTo(fromY);
		assertThat(cmove.getToX()).isEqualTo(toX);
		assertThat(cmove.getToY()).isEqualTo(toY);
		assertThat(cmove.getRookFromX()).isEqualTo(rookFromX);
		assertThat(cmove.getRookFromY()).isEqualTo(rookFromY);
		assertThat(cmove.getRookToX()).isEqualTo(rookToX);
		assertThat(cmove.getRookToY()).isEqualTo(rookToY);
	}

	@Test
	public void fromBasicNotation_nullNotationOrColor_throwsIllegalArgument() {
		assertThatIllegalArgumentException().isThrownBy(() -> Move.fromBasicNotation(null, Color.WHITE, board));
		assertThatIllegalArgumentException().isThrownBy(() -> Move.fromBasicNotation("a1-a6+", null, board));
	}

	@Test
	public void fromBasicNotation_tooShortNotation_throwsIllegalArgument() {
		assertThatIllegalArgumentException().isThrownBy(() -> Move.fromBasicNotation("a1-", Color.WHITE, board));
	}

}
