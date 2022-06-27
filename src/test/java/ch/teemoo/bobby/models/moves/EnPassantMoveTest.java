package ch.teemoo.bobby.models.moves;

import static org.assertj.core.api.Assertions.assertThat;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;
import org.junit.jupiter.api.Test;

class EnPassantMoveTest {

  @Test
  void constructor_ok_returnsCorrect() {
    Piece pawn = new Pawn(Color.WHITE);
    Move move = new Move(pawn, 5, 3, 6, 4);
    move.setTookPiece(new Pawn(Color.BLACK));

    EnPassantMove emove = new EnPassantMove(move, 6, 4);

    assertThat(emove.getPiece()).isEqualTo(pawn);
    assertThat(emove.getTookPiecePosX()).isEqualTo(6);
    assertThat(emove.getTookPiecePosY()).isEqualTo(4);

    assertThat(emove.isTaking()).isTrue();
    assertThat(emove.isChecking()).isFalse();
  }

  @Test
  void constructor_checkingMove_returnsChecking_PIT() {
    Piece pawn = new Pawn(Color.WHITE);
    Move move = new Move(pawn, 5, 3, 6, 4);
    move.setChecking(true);
    move.setTookPiece(new Pawn(Color.BLACK));
    
    EnPassantMove emove = new EnPassantMove(move, 6, 4);

    assertThat(emove.isChecking()).isTrue();
  }

  @Test
  void getPrettyNotation_ok_returnEnPassantPostfix() {
    Piece pawn = new Pawn(Color.WHITE);
    Move move = new Move(pawn, 5, 6, 5, 7);
    move.setTookPiece(new Pawn(Color.BLACK));
    EnPassantMove emove = new EnPassantMove(move, 5, 7);

    assertThat(emove.getPrettyNotation()).isEqualTo(move.getPrettyNotation() + " (en passant)");
  }

}
