package ch.teemoo.bobby.models.moves;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatIllegalArgumentException;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.Mockito.when;

import java.util.Optional;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
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
		Move move2 = new Move(new Rook(Color.BLACK), move.getFromX(), move.getFromY(), move.getToX(), move.getToY());
		assertThat(move.equalsForPositions(move2)).isTrue();
		assertThat(move.equals(move2)).isFalse();
	}

	@Test
	public void equalsForPosition_differentFromX_returnFalse() {
		Move move = new Move(new Rook(Color.WHITE), 0, 0, 0, 5);
		Move move2 = new Move(new Rook(Color.BLACK), 1, 0, 0, 5);
		assertThat(move.equalsForPositions(move2)).isFalse();
	}

	@Test
	public void equalsForPosition_differentFromY_returnFalse() {
		Move move = new Move(new Rook(Color.WHITE), 0, 0, 0, 5);
		Move move2 = new Move(new Rook(Color.BLACK), 0, 1, 0, 5);
		assertThat(move.equalsForPositions(move2)).isFalse();
	}

	@Test
	public void equalsForPosition_differentToX_returnFalse() {
		Move move = new Move(new Rook(Color.WHITE), 0, 0, 0, 5);
		Move move2 = new Move(new Rook(Color.BLACK), 0, 0, 1, 5);
		assertThat(move.equalsForPositions(move2)).isFalse();
	}

	@Test
	public void equalsForPosition_differentToY_returnFalse() {
		Move move = new Move(new Rook(Color.WHITE), 0, 0, 0, 5);
		Move move2 = new Move(new Rook(Color.BLACK), 0, 0, 0, 6);
		assertThat(move.equalsForPositions(move2)).isFalse();
	}

	@Test
	public void equals_equalMove_returnTrue() {
		Piece rook1 = new Rook(Color.WHITE);
		Move move = new Move(rook1, 0, 0, 0, 5);
		Move move2 = new Move(rook1, move.getFromX(), move.getFromY(), move.getToX(), move.getToY());
		assertThat(move.equals(move2)).isTrue();
		assertThat(move).hasSameHashCodeAs(move2);
	}

	@Test
	public void equals_sameMove_returnTrue() {
		Piece rook1 = new Rook(Color.WHITE);
		Move move = new Move(rook1, 0, 0, 0, 5);
		assertThat(move.equals(move)).isTrue();
	}

	@Test
	public void equals_null_returnFalse() {
		Piece rook1 = new Rook(Color.WHITE);
		Move move = new Move(rook1, 0, 0, 0, 5);
		assertThat(move.equals(null)).isFalse();
	}

	@Test
	public void equals_differentClass_returnFalse() {
		Piece rook1 = new Rook(Color.WHITE);
		Move move = new Move(rook1, 0, 0, 0, 5);
		assertThat(move.equals(new Object())).isFalse();
	}

	@Test
	public void equals_differentPosition_returnFalse() {
		Piece rook1 = new Rook(Color.WHITE);
		Move move = new Move(rook1, 0, 0, 0, 5);
		Move move2 = new Move(rook1, 0, 0, 1, 5);

		assertThat(move.equals(move2)).isFalse();
		assertThat(move).doesNotHaveSameHashCodeAs(move2);
	}

	@Test
	public void equals_differentTookPiece_returnFalse() {
		Piece rook1 = new Rook(Color.WHITE);
		Move move = new Move(rook1, 0, 0, 0, 5);
		move.setTookPiece(rook1);
		Move move2 = new Move(rook1, 0, 0, 0, 5);

		assertThat(move.equals(move2)).isFalse();
		assertThat(move).doesNotHaveSameHashCodeAs(move2);
	}

	@Test
	public void equals_differentChecking_returnFalse() {
		Piece rook1 = new Rook(Color.WHITE);
		Move move = new Move(rook1, 0, 0, 0, 5);
		move.setChecking(true);
		Move move2 = new Move(rook1, 0, 0, 0, 5);

		assertThat(move.equals(move2)).isFalse();
		assertThat(move).doesNotHaveSameHashCodeAs(move2);
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
		
		if (isTaking)
			when(board.getPiece(anyInt(), anyInt())).thenReturn(Optional.of(new Pawn(Color.BLACK)));

		Move move = Move.fromBasicNotation(notation, Color.WHITE, board);

		assertThat(move.getBasicNotation()).isEqualTo(notation);
		assertThat(move.isChecking()).isEqualTo(isChecking);
		assertThat(move.isTaking()).isEqualTo(isTaking);
		if (!isTaking)
			assertThat(move.getPiece()).isNull();
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
