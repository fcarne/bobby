package ch.teemoo.bobby.gui;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.params.provider.Arguments.arguments;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.Position;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Queen;
import java.awt.Font;
import java.util.stream.Stream;
import javax.swing.SwingConstants;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

public class SquareTest {

  private Font font = Font.getFont("Serif");

  @Test
  void constructor_newSquare_hasDefaults() {
    Piece queen = new Queen(Color.BLACK);
    Position position = new Position(3, 0);
    Square square = new Square(queen, position, Background.DARK, font);

    assertThat(square.getText()).isEqualTo("♛");
    assertThat(square.getPiece()).isEqualTo(queen);
    assertThat(square.getPosition()).isEqualTo(position);
    assertThat(square.getHorizontalAlignment()).isEqualTo(SwingConstants.CENTER);
    assertThat(square.isOpaque()).isTrue();
    assertThat(square.getBackground()).isEqualTo(Background.DARK.getColor());
    assertThat(square.getFont()).isEqualTo(font);
  }

  @ParameterizedTest
  @MethodSource
  void setPiece_pieceOrNull_correctTextDisplay(Piece piece, String expected) {
    Square square = new Square(null, null, Background.LIGHT, font);
    square.setPiece(piece);
    assertThat(square.getPiece()).isEqualTo(piece);
    assertThat(square.getText()).isEqualTo(expected);
  }

  private static Stream<Arguments> setPiece_pieceOrNull_correctTextDisplay() {
    return Stream.of(arguments(new Pawn(Color.WHITE), "♙"), arguments(null, ""));

  }
}
