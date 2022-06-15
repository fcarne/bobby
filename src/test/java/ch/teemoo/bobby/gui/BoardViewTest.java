package ch.teemoo.bobby.gui;

import static ch.teemoo.bobby.gui.BoardView.GREEN_BORDER;
import static org.assertj.core.api.Assertions.assertThat;

import ch.teemoo.bobby.helpers.GuiHelper;
import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Queen;
import ch.teemoo.bobby.models.pieces.Rook;
import com.google.common.base.Supplier;
import java.awt.Cursor;
import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.Arrays;
import java.util.stream.Stream;
import javax.swing.JFrame;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

public class BoardViewTest {
  private GuiHelper guiHelper = new GuiHelper();

  private BoardView view;

  @BeforeEach
  public void setup() {
    view = new BoardView("Test board", guiHelper, false);
  }

  @Test
  public void constructor_newBoardView_hasDefaults() {
    assertThat(view.getTitle()).isEqualTo("Test board");
    assertThat(view.getContentPane().getLayout()).isInstanceOf(GridLayout.class);
    GridLayout gridLayout = (GridLayout) view.getContentPane().getLayout();
    assertThat(gridLayout.getColumns()).isEqualTo(gridLayout.getRows()).isEqualTo(10);
    assertThat(view.getDefaultCloseOperation()).isEqualTo(JFrame.DISPOSE_ON_CLOSE);
    assertThat(view.getSize()).isEqualTo(new Dimension(800, 800));
    assertThat(view.getJMenuBar()).isNotNull();
  }

  @ParameterizedTest
  @CsvSource({ "false,a", "true,h" })
  public void display_onlyRook_boardHasCorrectSetup(boolean reversed, String letter) {
    Piece[][] pieces = new Piece[8][8];
    Piece rook = new Rook(Color.WHITE);
    pieces[2][4] = rook;
    view.display(pieces, reversed);
    Square[][] squares = view.getSquares();
    Square rookSquare = squares[2][4];
    Square emptySquare = squares[2][3];
    assertThat(rookSquare.getPiece()).isEqualTo(rook);
    assertThat(emptySquare.getPiece()).isNull();

    assertThat(rookSquare.getBackground()).isEqualTo(Background.DARK.getColor());
    assertThat(rookSquare.getBackground()).isNotEqualTo(emptySquare.getBackground());
    assertThat(rookSquare.getBackground()).isNotEqualTo(squares[1][4].getBackground());
    assertThat(rookSquare.getBackground()).isEqualTo(squares[1][3].getBackground());

    assertThat(view.getContentPane().getComponent(1)).isInstanceOf(SideLabel.class);
    assertThat(((SideLabel) view.getContentPane().getComponent(1)).getText()).isEqualTo(letter);
    assertThat(view.isVisible()).isFalse();

    Supplier<Stream<SideLabel>> supplier = () -> Arrays
        .stream(view.getContentPane().getComponents())
        .filter(SideLabel.class::isInstance)
        .map(it -> (SideLabel) it)
        .filter(it -> !it.getText().isEmpty());

    assertThat(supplier.get()).hasSize(8 * 4);
    assertThat(
        supplier.get().filter(it -> it.getText().charAt(0) >= 'a' && it.getText().charAt(0) <= 'h'))
        .hasSize(8 * 2);
    assertThat(
        supplier.get().filter(it -> it.getText().charAt(0) >= '1' && it.getText().charAt(0) <= '8'))
        .hasSize(8 * 2);
    assertThat(
        Arrays.stream(view.getContentPane().getComponents()).filter(Square.class::isInstance))
        .hasSize(64);
  }

  @Test
  public void refresh_oneRookToEmpty_squareIsBlank() {
    Piece[][] pieces = new Piece[8][8];
    Piece rook = new Rook(Color.WHITE);
    pieces[2][4] = rook;
    view.display(pieces, false);
    assertThat(view.getSquares()[2][4].getPiece()).isEqualTo(rook);
    assertThat(view.getSquares()[2][4].getText()).isEqualTo(rook.getUnicode());

    Piece[][] noPieces = new Piece[8][8];
    view.refresh(noPieces);
    assertThat(view.getSquares()[2][4].getPiece()).isNull();
    assertThat(view.getSquares()[2][4].getText()).isEqualTo("");
  }

  @Test
  public void resetAllClickables_listenerAdded_clearAllListeners() {
    Piece[][] noPieces = new Piece[8][8];
    view.display(noPieces, false);
    view.getSquares()[2][4].addMouseListener(new MouseAdapter() {
      @Override
      public void mouseClicked(MouseEvent e) {
        super.mouseClicked(e);
      }
    });
    assertThat(view.getSquares()[2][4].getMouseListeners()).hasSize(1);

    view.resetAllClickables();
    assertThat(view.getSquares()[2][4].getMouseListeners()).hasSize(0);
    assertThat(view.getSquares()[2][4].getCursor()).isEqualTo(Cursor.getDefaultCursor());
  }

  @Test
  public void cleanSquareBorder_addedGreenBorder_squareHasNoBorder() {
    Piece[][] noPieces = new Piece[8][8];
    view.display(noPieces, false);
    view.getSquares()[2][4].setBorder(GREEN_BORDER);
    assertThat(view.getSquares()[2][4].getBorder()).isEqualTo(BoardView.GREEN_BORDER);

    view.cleanSquaresBorder();
    assertThat(view.getSquares()[2][4].getBorder()).isEqualTo(BoardView.NO_BORDER);
  }

  @Test
  public void addBorderToLastMoveSquares_moveFromE3ToE4_squaresHaveGreenBorder() {
    Piece[][] noPieces = new Piece[8][8];
    view.display(noPieces, false);

    // assertThat(view.getSquares()[2][4].getBorder()).isNull();
    // assertThat(view.getSquares()[3][4].getBorder()).isNull();

    view.addBorderToLastMoveSquares(new Move(new Queen(Color.WHITE), 4, 2, 4, 3));

    assertThat(view.getSquares()[2][4].getBorder()).isEqualTo(GREEN_BORDER);
    assertThat(view.getSquares()[3][4].getBorder()).isEqualTo(GREEN_BORDER);
  }
}
