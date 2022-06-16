package ch.teemoo.swing;

import static com.github.stefanbirkner.systemlambda.SystemLambda.tapSystemOutNormalized;
import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.swing.finder.WindowFinder.findFrame;
import static org.assertj.swing.launcher.ApplicationLauncher.application;
import static org.awaitility.Awaitility.await;

import ch.teemoo.bobby.Bobby;
import ch.teemoo.bobby.GameController;
import ch.teemoo.bobby.gui.Square;
import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.Position;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.swing.extension.GUITestExtension;
import java.awt.Dialog;
import java.awt.Frame;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JMenuItem;
import org.assertj.swing.core.BasicRobot;
import org.assertj.swing.core.GenericTypeMatcher;
import org.assertj.swing.core.Robot;
import org.assertj.swing.edt.FailOnThreadViolationRepaintManager;
import org.assertj.swing.fixture.DialogFixture;
import org.assertj.swing.fixture.FrameFixture;
import org.assertj.swing.fixture.JLabelFixture;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;

@ExtendWith(GUITestExtension.class)
public class BobbySwingTest {

  private FrameFixture frame;

  @BeforeAll
  static void setupOnce() {
    FailOnThreadViolationRepaintManager.install();
  }

  @AfterAll
  public static final void teardownOnce() {
    FailOnThreadViolationRepaintManager.uninstall();
  }

  @BeforeEach
  public void setup() {
    Robot robot = BasicRobot.robotWithNewAwtHierarchy();
    robot.settings().timeoutToFindPopup(20000);
    application(Bobby.class).withArgs("default").start();
    frame = findFrame(new GenericTypeMatcher<Frame>(Frame.class) {
      protected boolean isMatching(Frame frame) {
        return "Bobby chess game".equals(frame.getTitle()) && frame.isShowing();
      }
    }).using(robot);
  }

  @AfterEach
  protected void teardown() {
    frame.cleanUp();
  }

  @Test
  public void newGameDialog_clickClose_dialogAppears() throws InterruptedException {
    frame.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
      @Override
      protected boolean isMatching(JMenuItem menuItem) {
        return "New".equals(menuItem.getText());
      }
    }).click();

    frame.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
      @Override
      protected boolean isMatching(Dialog dialog) {
        return "Game setup".equals(dialog.getTitle());
      }
    }).close();
  }

  @Test
  public void newGameDialog_clickOk_dialogAppears() {
    frame.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
      @Override
      protected boolean isMatching(JMenuItem menuItem) {
        return "New".equals(menuItem.getText());
      }
    }).click();

    DialogFixture dialogFixture = frame.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
      @Override
      protected boolean isMatching(Dialog dialog) {
        return "Game setup".equals(dialog.getTitle());
      }
    });

    dialogFixture.button(new GenericTypeMatcher<JButton>(JButton.class) {
      @Override
      protected boolean isMatching(JButton button) {
        return button.isDefaultButton();
      }
    }).click();
  }

  @Test
  public void suggestMoveDialog_initialBoard_suggestedPopup() {
    frame.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
      @Override
      protected boolean isMatching(JMenuItem menuItem) {
        return "Suggest move".equals(menuItem.getText());
      }
    }).click();

    DialogFixture dialog = frame.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
      @Override
      protected boolean isMatching(Dialog dialog) {
        return "Info".equals(dialog.getTitle());
      }
    });

    dialog.label(new GenericTypeMatcher<JLabel>(JLabel.class) {
      @Override
      protected boolean isMatching(JLabel label) {
        return label.getText() != null
            && label.getText().contains("Brilliantly, I recommend you to play:");
      }
    });
    dialog.requireVisible().close();
  }

  @Test
  public void proposeDrawDialog_initialBoard_drawRefused() {
    frame.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
      @Override
      protected boolean isMatching(JMenuItem menuItem) {
        return "Propose draw".equals(menuItem.getText());
      }
    }).click();

    DialogFixture dialog = frame.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
      @Override
      protected boolean isMatching(Dialog dialog) {
        return "Info".equals(dialog.getTitle());
      }
    });
    dialog.label(new GenericTypeMatcher<JLabel>(JLabel.class) {
      @Override
      protected boolean isMatching(JLabel label) {
        return label.getText() != null && label.getText().contains("Are you kidding me?");
      }
    });

    dialog.requireVisible().close();
  }

  @Test
  public void printToConsole_initialBoard_boardLogged() throws Exception {

    String text = tapSystemOutNormalized(
        () -> frame.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
          @Override
          protected boolean isMatching(JMenuItem menuItem) {
            return "Print to console".equals(menuItem.getText());
          }
        }).click());

    assertThat(text).contains(" - Current board: \n"
        + "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n"
        + "♟ ♟ ♟ ♟ ♟ ♟ ♟ ♟ \n"
        + "                \n"
        + "                \n"
        + "                \n"
        + "                \n"
        + "♙ ♙ ♙ ♙ ♙ ♙ ♙ ♙ \n"
        + "♖ ♘ ♗ ♕ ♔ ♗ ♘ ♖ \n");
  }

  @Test
  public void loadGameDialog_click_dialogAppears() {
    frame.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
      @Override
      protected boolean isMatching(JMenuItem menuItem) {
        return "Load".equals(menuItem.getText());
      }
    }).click();

    frame.fileChooser().cancel();
  }

  @Test
  public void saveGameDialog_click_dialogAppears() {
    frame.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
      @Override
      protected boolean isMatching(JMenuItem menuItem) {
        return "Save".equals(menuItem.getText());
      }
    }).click();

    frame.fileChooser().cancel();
  }

  @Test
  public void boardClick_moveWhitePawn_pawnMoved() throws Exception {
    JLabelFixture whitePawn = frame.label(new GenericTypeMatcher<Square>(Square.class) {
      @Override
      protected boolean isMatching(Square square) {
        Position position = square.getPosition();
        return position.getFile() == 4 && position.getRank() == 1;
      }
    });
    whitePawn.click();

    JLabelFixture emptySquare = frame.label(new GenericTypeMatcher<Square>(Square.class) {
      @Override
      protected boolean isMatching(Square square) {
        Position position = square.getPosition();
        return position.getFile() == 4 && position.getRank() == 3;
      }
    });

    assertThat(whitePawn.target().getText()).isEqualTo(new Pawn(Color.WHITE).getUnicode());
    assertThat(emptySquare.target().getText()).isEmpty();

    await().untilAsserted(() -> assertThat(whitePawn.target().getBorder()).isNotNull()
        .isEqualTo(GameController.RED_BORDER));
    await().untilAsserted(
        () -> assertThat(emptySquare.target().getBorder()).isEqualTo(GameController.BLUE_BORDER));

    emptySquare.click();

    await().untilAsserted(() -> assertThat(emptySquare.target().getText())
        .isEqualTo(new Pawn(Color.WHITE).getUnicode()));
    await().untilAsserted(() -> assertThat(whitePawn.target().getText()).isEmpty());
  }

  @Test
  public void boardClick_reclickSquare_pawnNotMovedBoardResetted() throws Exception {
    JLabelFixture whitePawn = frame.label(new GenericTypeMatcher<Square>(Square.class) {
      @Override
      protected boolean isMatching(Square square) {
        Position position = square.getPosition();
        return position.getFile() == 4 && position.getRank() == 1;
      }
    });
    whitePawn.click().click();

    await().untilAsserted(() -> assertThat(whitePawn.target().getText())
        .isEqualTo(new Pawn(Color.WHITE).getUnicode()));
    await().untilAsserted(
        () -> assertThat(whitePawn.target().getBorder()).isNotEqualTo(GameController.RED_BORDER));
  }

  @Test
  public void undeMoveClick_pawnToC4_boardRestored() throws Exception {
    JLabelFixture originalSquare = frame.label(new GenericTypeMatcher<Square>(Square.class) {
      @Override
      protected boolean isMatching(Square square) {
        Position position = square.getPosition();
        return position.getFile() == 2 && position.getRank() == 1;
      }
    });

    JLabelFixture toSquare = frame.label(new GenericTypeMatcher<Square>(Square.class) {
      @Override
      protected boolean isMatching(Square square) {
        Position position = square.getPosition();
        return position.getFile() == 2 && position.getRank() == 3;
      }
    });

    originalSquare.click();
    toSquare.click();

    frame.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
      @Override
      protected boolean isMatching(JMenuItem menuItem) {
        return "Undo move".equals(menuItem.getText());
      }
    }).click();

    assertThat(originalSquare.target().getText()).isEqualTo(new Pawn(Color.WHITE).getUnicode());
    assertThat(toSquare.target().getText()).isEmpty();
  }

}
