package ch.teemoo.bobby;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.swing.finder.WindowFinder.findFrame;
import static org.assertj.swing.launcher.ApplicationLauncher.application;
import static org.junit.jupiter.params.provider.Arguments.arguments;

import ch.teemoo.bobby.extension.GUITestExtension;
import com.formdev.flatlaf.FlatIntelliJLaf;
import java.awt.Frame;
import java.util.stream.Stream;
import javax.swing.UIManager;
import org.assertj.swing.core.BasicRobot;
import org.assertj.swing.core.GenericTypeMatcher;
import org.assertj.swing.core.Robot;
import org.assertj.swing.edt.FailOnThreadViolationRepaintManager;
import org.assertj.swing.fixture.FrameFixture;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

@ExtendWith(GUITestExtension.class)
class BobbyLaFTest {

  @BeforeAll
  static void setupOnce() {
    FailOnThreadViolationRepaintManager.install();
  }

  @AfterAll
  public static final void teardownOnce() {
    FailOnThreadViolationRepaintManager.uninstall();
  }

  @ParameterizedTest
  @MethodSource
  public void main_argsPassed_lookAndFeelChanged(String[] args, String expected) {
    Robot robot = BasicRobot.robotWithNewAwtHierarchy();

    application(Bobby.class).withArgs(args).start();
    FrameFixture frame = findFrame(new GenericTypeMatcher<Frame>(Frame.class) {
      protected boolean isMatching(Frame frame) {
        return "Bobby chess game".equals(frame.getTitle()) && frame.isShowing();
      }
    }).using(robot);

    if (args.length == 0 || !"default".equalsIgnoreCase(args[0])) {
      frame.dialog().button("OptionPane.button").click();
    }

    frame.cleanUp();

    assertThat(UIManager.getLookAndFeel().getClass().getName()).isEqualTo(expected);
  }

  private static Stream<Arguments> main_argsPassed_lookAndFeelChanged() {
    return Stream.of(
        arguments(new String[] { "default" }, UIManager.getSystemLookAndFeelClassName()),
        arguments(new String[] {}, FlatIntelliJLaf.class.getName()),
        arguments(new String[] { "random" }, FlatIntelliJLaf.class.getName()));
  }

}
