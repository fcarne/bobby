package ch.teemoo.bobby.models.moves;

import static org.assertj.core.api.Assertions.assertThat;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.pieces.Bishop;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Queen;
import org.junit.jupiter.api.Test;

class PromotionMoveTest {

  @Test
  public void constructor_ok_returnsCorrect() {
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
  public void constructor_checkingAndTaking_returnsCheckingAndTaking_PIT() {
    Piece pawn = new Pawn(Color.WHITE);
    Piece queen = new Queen(Color.WHITE);
    Move move = new Move(pawn, 5, 6, 5, 7);
    move.setTookPiece(new Bishop(Color.BLACK));
    move.setChecking(true);
    
    PromotionMove pmove = new PromotionMove(move, queen);
    
    
    assertThat(pmove.isTaking()).isTrue();
    assertThat(pmove.isChecking()).isTrue();
  }

  @Test
  public void getPrettyNotation_ok_returnPromotedPostfix() {
    Piece pawn = new Pawn(Color.WHITE);
    Piece queen = new Queen(Color.WHITE);
    Move move = new Move(pawn, 5, 6, 5, 7);
    PromotionMove pmove = new PromotionMove(move, queen);

    assertThat(pmove.getPrettyNotation())
        .isEqualTo(move.getPrettyNotation() + " (promoted to Queen)");
  }

}
