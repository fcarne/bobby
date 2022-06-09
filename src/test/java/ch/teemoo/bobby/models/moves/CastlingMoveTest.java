package ch.teemoo.bobby.models.moves;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatRuntimeException;
import static org.junit.jupiter.api.Assertions.assertThrows;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.pieces.King;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Rook;

class CastlingMoveTest {

	@Test
	public void moveConstructor_ok_returnsCorrect() {
		Piece rook = new Rook(Color.WHITE);
		Piece king = new King(Color.WHITE);
		CastlingMove move = new CastlingMove(king, 4, 0, 6, 0, rook, 7, 0, 5, 0);

		assertThat(move.getPiece()).isEqualTo(king);
		assertThat(move.getRook()).isEqualTo(rook);
		assertThat(move.getFromX()).isEqualTo(4);
		assertThat(move.getFromY()).isEqualTo(0);
		assertThat(move.getToX()).isEqualTo(6);
		assertThat(move.getToY()).isEqualTo(0);

		assertThat(move.getRookFromX()).isEqualTo(7);
		assertThat(move.getRookFromY()).isEqualTo(0);
		assertThat(move.getRookToX()).isEqualTo(5);
		assertThat(move.getRookToY()).isEqualTo(0);

		assertThat(move.isTaking()).isFalse();
		assertThat(move.isChecking()).isFalse();
	}
	
	@Test
	public void moveConstructor_notKing_throwsAssertionError() {
		Piece rook = new Rook(Color.WHITE);
		Piece pawn = new Pawn(Color.WHITE);
		
		assertThrows(AssertionError.class, () -> new CastlingMove(pawn, 4, 0, 6, 0, rook, 7, 0, 5, 0));
	}
	
	@Test
	public void moveConstructor_notRook_throwsAssertionError() {
		Piece king = new King(Color.WHITE);
		Piece pawn = new Pawn(Color.WHITE);
		
		assertThrows(AssertionError.class, () -> new CastlingMove(king, 4, 0, 6, 0, pawn, 7, 0, 5, 0));
	}

	@ParameterizedTest
	@CsvSource({ "0-0,4,0,6,0,7,0,5,0,false", "0-0+,4,7,6,7,7,7,5,7,true", "0-0-0+,4,0,2,0,0,0,3,0,true",
			"0-0-0,4,7,2,7,0,7,3,7,false" })
	public void getBasicNotation_ok_returnCorrect(String notation, int fromX, int fromY, int toX, int toY,
			int rookFromX, int rookFromY, int rookToX, int rookToY, boolean isChecking) {
		Piece rook = new Rook(Color.WHITE);
		Piece king = new King(Color.WHITE);
		Move move = new CastlingMove(king, fromX, fromY, toX, toX, rook, rookFromX, rookFromY, rookToX, rookToY);
		move.setChecking(isChecking);
		assertThat(move.getBasicNotation()).isEqualTo(notation);
		assertThat(move.isChecking()).isEqualTo(isChecking);
	}

	@Test
	public void getBasicNotation_wrongFrom_throwsRuntime() {
		Piece rook = new Rook(Color.WHITE);
		Piece king = new King(Color.WHITE);
		Move move = new CastlingMove(king, 4, 0, 2, 0, rook, 3, 0, 3, 0);
		assertThatRuntimeException().isThrownBy(() -> move.getBasicNotation());
	}

}
