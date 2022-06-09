package ch.teemoo.bobby.models.moves;

import static org.assertj.core.api.Assertions.assertThat;
import org.junit.jupiter.api.Test;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Queen;

class PromotionMoveTest {

	@Test
	public void moveConstructor_ok_returnsCorrect() {
		Piece pawn = new Pawn(Color.WHITE);
		Piece queen = new Queen(Color.WHITE);
		Move move = new Move(pawn, 5, 6, 5, 7);
		PromotionMove pmove = new PromotionMove(move, queen);

		assertThat(pmove.getPiece()).isEqualTo(pawn);
		assertThat(pmove.getPromotedPiece()).isEqualTo(queen);

		assertThat(move.isTaking()).isFalse();
		assertThat(move.isChecking()).isFalse();
	}
	
	@Test
	public void getPrettyNotation_ok_returnPromotedPostfix() {
		Piece pawn = new Pawn(Color.WHITE);
		Piece queen = new Queen(Color.WHITE);
		Move move = new Move(pawn, 5, 6, 5, 7);
		PromotionMove pmove = new PromotionMove(move, queen);

		assertThat(pmove.getPrettyNotation()).isEqualTo(move.getPrettyNotation() + " (promoted to Queen)");
	}

}
