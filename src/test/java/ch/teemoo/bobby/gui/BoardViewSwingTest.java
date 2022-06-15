package ch.teemoo.bobby.gui;

import static com.github.stefanbirkner.systemlambda.SystemLambda.catchSystemExit;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.params.provider.Arguments.arguments;

import ch.teemoo.bobby.extension.GUITestExtension;
import ch.teemoo.bobby.helpers.BotFactory;
import ch.teemoo.bobby.helpers.GuiHelper;
import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.games.GameSetup;
import ch.teemoo.bobby.models.pieces.Bishop;
import ch.teemoo.bobby.models.pieces.Knight;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Queen;
import ch.teemoo.bobby.models.pieces.Rook;
import ch.teemoo.bobby.models.players.ExperiencedBot;
import ch.teemoo.bobby.models.players.Human;
import ch.teemoo.bobby.models.players.RandomBot;
import ch.teemoo.bobby.models.players.TraditionalBot;
import java.awt.Dialog;
import java.io.File;
import java.io.IOException;
import java.util.Optional;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;
import java.util.concurrent.RunnableFuture;
import java.util.stream.Stream;
import javax.swing.JLabel;
import javax.swing.JMenuItem;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;
import javax.swing.UnsupportedLookAndFeelException;
import org.assertj.swing.core.BasicRobot;
import org.assertj.swing.core.GenericTypeMatcher;
import org.assertj.swing.core.Robot;
import org.assertj.swing.edt.FailOnThreadViolationRepaintManager;
import org.assertj.swing.edt.GuiActionRunner;
import org.assertj.swing.fixture.DialogFixture;
import org.assertj.swing.fixture.FrameFixture;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

@ExtendWith(GUITestExtension.class)
public class BoardViewSwingTest {
  private BoardView frame;
  private FrameFixture window;

  @BeforeAll
  static void setupOnce() throws ClassNotFoundException, InstantiationException,
      IllegalAccessException, UnsupportedLookAndFeelException {
    FailOnThreadViolationRepaintManager.install();
    UIManager.setLookAndFeel(UIManager.getCrossPlatformLookAndFeelClassName());
  }

  @BeforeEach
  protected void setup() {
    Robot robot = BasicRobot.robotWithNewAwtHierarchy();
    frame = GuiActionRunner.execute(() -> new BoardView("Test board", new GuiHelper(), true));
    window = new FrameFixture(robot, frame);
    window.show(); // shows the frame to test
  }

  @AfterEach
  protected void teardown() {
    window.cleanUp();
  }

  @AfterAll
  public static final void teardownOnce() {
    FailOnThreadViolationRepaintManager.uninstall();
  }

  @ParameterizedTest
  @MethodSource
  public void promotionDialog_clickRadioButton_returnChosenPiece(String name, Class<?> clazz)
      throws InterruptedException, ExecutionException {
    // given
    Color color = Color.BLACK;

    // when
    RunnableFuture<Piece> rf = new FutureTask<>(() -> frame.promotionDialog(color));
    SwingUtilities.invokeLater(rf);

    // then
    DialogFixture dialog = window.dialog();
    dialog.radioButton(name).focus().click();
    dialog.label(new GenericTypeMatcher<JLabel>(JLabel.class) {
      @Override
      protected boolean isMatching(JLabel label) {
        return "Promote pawn to".equals(label.getText());
      }
    }).font().requireBold();
    dialog.close();

    Piece piece = rf.get();
    assertThat(piece).isInstanceOf(clazz);
    assertThat(piece.getColor()).isEqualTo(Color.BLACK);
  }

  private static Stream<Arguments> promotionDialog_clickRadioButton_returnChosenPiece() {
    return Stream.of(arguments("queenRadioButton", Queen.class),
        arguments("rookRadioButton", Rook.class), arguments("bishopRadioButton", Bishop.class),
        arguments("knightRadioButton", Knight.class));
  }

  @Test
  public void loadGameDialog_approve_returnSelectedFile()
      throws InterruptedException, ExecutionException, IOException {

    // when
    RunnableFuture<Optional<File>> rf = new FutureTask<>(() -> frame.loadGameDialog());
    SwingUtilities.invokeLater(rf);

    File temp = File.createTempFile("test", ".txt");
    temp.deleteOnExit();

    // then
    window.fileChooser().selectFile(temp).approve();

    Optional<File> file = rf.get();
    assertThat(file).isPresent().get().isEqualTo(temp);
  }

  @Test
  public void loadGameDialog_cancel_returnEmpty()
      throws InterruptedException, ExecutionException, IOException {

    // when
    RunnableFuture<Optional<File>> rf = new FutureTask<>(() -> frame.loadGameDialog());
    SwingUtilities.invokeLater(rf);

    // then
    window.fileChooser().cancel();

    Optional<File> file = rf.get();
    assertThat(file).isEmpty();
  }

  @Test
  public void saveGameDialog_approve_returnSelectedFile()
      throws InterruptedException, ExecutionException, IOException {

    // when
    RunnableFuture<Optional<File>> rf = new FutureTask<>(() -> frame.saveGameDialog());
    SwingUtilities.invokeLater(rf);

    File temp = File.createTempFile("test", ".txt");
    temp.deleteOnExit();

    // then
    window.fileChooser().selectFile(temp).approve();

    Optional<File> file = rf.get();
    assertThat(file).isPresent().get().isEqualTo(temp);
  }

  @Test
  public void saveGameDialog_cancel_returnEmpty()
      throws InterruptedException, ExecutionException, IOException {

    // when
    RunnableFuture<Optional<File>> rf = new FutureTask<>(() -> frame.saveGameDialog());
    SwingUtilities.invokeLater(rf);

    // then
    window.fileChooser().cancel();

    Optional<File> file = rf.get();
    assertThat(file).isEmpty();
  }

  @Test
  public void popupInfo_normalBehaviour_popupShown() {
    SwingUtilities.invokeLater(() -> frame.popupInfo("An info here"));
    DialogFixture dialog = window.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
      @Override
      protected boolean isMatching(Dialog dialog) {
        return "Info".equals(dialog.getTitle());
      }
    });

    dialog.label(new GenericTypeMatcher<JLabel>(JLabel.class) {
      @Override
      protected boolean isMatching(JLabel label) {
        return "An info here".equals(label.getText());
      }
    });
    dialog.close();
  }

  @Test
  public void popupError_normalBehaviour_popupShown() {
    SwingUtilities.invokeLater(() -> frame.popupError("An error here"));
    DialogFixture dialog = window.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
      @Override
      protected boolean isMatching(Dialog dialog) {
        return "Error".equals(dialog.getTitle());
      }
    });

    dialog.label(new GenericTypeMatcher<JLabel>(JLabel.class) {
      @Override
      protected boolean isMatching(JLabel label) {
        return "An error here".equals(label.getText());
      }
    });

    dialog.close();
  }

  @Test
  public void showAboutDialog_clickMenuItem_popupShown() {
    window.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
      @Override
      protected boolean isMatching(JMenuItem menuItem) {
        return "Help".equals(menuItem.getText());
      }
    }).click();

    window.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
      @Override
      protected boolean isMatching(JMenuItem menuItem) {
        return "About".equals(menuItem.getText());
      }
    }).focus().click();

    window.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
      @Override
      protected boolean isMatching(Dialog dialog) {
        return "About Bobby".equals(dialog.getTitle());
      }
    }).close();
  }

  @Test
  public void exit_clickMenuItem_disposed() throws Exception {
    int statusCode = catchSystemExit(() -> {

      window.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
        @Override
        protected boolean isMatching(JMenuItem menuItem) {
          return "File".equals(menuItem.getText());
        }
      }).focus().click();

      window.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
        @Override
        protected boolean isMatching(JMenuItem menuItem) {
          return "Exit".equals(menuItem.getText());
        }
      }).focus().click();
    });
    assertEquals(0, statusCode);
  }

  @ParameterizedTest
  @MethodSource
  public void gameSetupDialog_notExitOnClose_setupHasCorrectPlayers(boolean okOption,
      boolean timeoutSelected, Object timeoutValue, int sliderLevel, boolean openings,
      boolean white, boolean shouldBeNull, Class<?> whitePlayerClass, Class<?> blackPlayerClass)
      throws InterruptedException, ExecutionException {
    // when
    RunnableFuture<GameSetup> rf = new FutureTask<>(
        () -> frame.gameSetupDialog(new BotFactory(null, null), false));
    SwingUtilities.invokeLater(rf);

    DialogFixture dialog = window.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
      @Override
      protected boolean isMatching(Dialog dialog) {
        return "Game setup".equals(dialog.getTitle());
      }
    });

    dialog.checkBox("timeoutCheckBox").focus().check(timeoutSelected);
    if (timeoutSelected) {
      dialog.spinner("timeoutSpinner").select(timeoutValue);
    }
    dialog.slider("levelSlider").slideTo(sliderLevel);
    dialog.checkBox("openingsCheckBox").check(openings);

    dialog.radioButton(white ? "whiteRadioButton" : "blackRadioButton").click();

    if (okOption) {
      dialog.button("OptionPane.button").click();
    } else {
      dialog.close();
    }

    GameSetup setup = rf.get();

    if (shouldBeNull) {
      assertThat(setup).isNull();
    } else {
      assertThat(setup.getWhitePlayer()).isInstanceOf(whitePlayerClass);
      assertThat(setup.getBlackPlayer()).isInstanceOf(blackPlayerClass);
    }
  }

  private static Stream<Arguments> gameSetupDialog_notExitOnClose_setupHasCorrectPlayers() {
    return Stream.of(arguments(true, false, 0, 0, false, true, false, Human.class, RandomBot.class),
        arguments(false, false, 0, 0, false, true, true, null, null),
        arguments(true, false, 0, 0, false, false, false, RandomBot.class, Human.class),
        arguments(true, true, 5, 2, false, true, false, Human.class, TraditionalBot.class),
        arguments(true, true, 4.5, 2, false, true, false, Human.class, TraditionalBot.class),
        arguments(true, false, 0, 2, true, true, false, Human.class, ExperiencedBot.class));
  }

  @Test
  public void gameSetupDialog_exitOnClose_disposed() throws Exception {
    int statusCode = catchSystemExit(() -> {
      RunnableFuture<GameSetup> rf = new FutureTask<>(
          () -> frame.gameSetupDialog(new BotFactory(null, null), true));
      SwingUtilities.invokeLater(rf);

      window.dialog().close();

    });
    assertEquals(0, statusCode);
  }

}
