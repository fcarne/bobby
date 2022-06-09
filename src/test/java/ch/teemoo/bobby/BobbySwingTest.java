package ch.teemoo.bobby;

import static com.github.stefanbirkner.systemlambda.SystemLambda.catchSystemExit;
import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.swing.finder.WindowFinder.findFrame;
import static org.assertj.swing.launcher.ApplicationLauncher.application;
import static org.junit.jupiter.api.Assertions.assertEquals;

import java.awt.Dialog;
import java.awt.Frame;

import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JMenuItem;

import org.assertj.swing.annotation.GUITest;
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
	@GUITest
	public void testFileExitMenu() {
		int statusCode = -1;
		try {
			statusCode = catchSystemExit(() -> {

				frame.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
					@Override
					protected boolean isMatching(JMenuItem menuItem) {
						return "Exit".equals(menuItem.getText());
					}
				}).click();
			});
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assertEquals(0, statusCode);
	}

	@Test
	@GUITest
	public void testHelpAboutMenu() {
		frame.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
			@Override
			protected boolean isMatching(JMenuItem menuItem) {
				return "About".equals(menuItem.getText());
			}
		}).click();

		frame.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
			@Override
			protected boolean isMatching(Dialog dialog) {
				return "About Bobby".equals(dialog.getTitle());
			}
		}).close();
	}

	@Test
	@GUITest
	public void testNewGameMenuWithSetupClose() {
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
	@GUITest
	public void testNewGameMenuOk() {
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
	@GUITest
	public void testLoadGameMenu() {
		frame.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
			@Override
			protected boolean isMatching(JMenuItem menuItem) {
				return "Load".equals(menuItem.getText());
			}
		}).click();

		frame.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
			@Override
			protected boolean isMatching(Dialog dialog) {
				return true;
			}
		}).close();
	}

	@Test
	@GUITest
	public void testSaveGameMenu() {
		frame.menuItem(new GenericTypeMatcher<JMenuItem>(JMenuItem.class) {
			@Override
			protected boolean isMatching(JMenuItem menuItem) {
				return "Save".equals(menuItem.getText());
			}
		}).click();

		frame.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
			@Override
			protected boolean isMatching(Dialog dialog) {
				return true;
			}
		}).close();
	}

	@Test
	@GUITest
	public void testSelectWhiteKingPiece() throws Exception {
		JLabelFixture whiteKing = frame.label(new GenericTypeMatcher<JLabel>(JLabel.class) {
			@Override
			protected boolean isMatching(JLabel label) {
				return "♔".equals(label.getText());
			}
		});
		//assertThat(whiteKing.target().getBorder()).isNull();
		whiteKing.click();
		Thread.sleep(1000);
		assertThat(whiteKing.target().getBorder()).isNotNull();
	}

}
