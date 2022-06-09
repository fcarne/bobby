package ch.teemoo.bobby.gui;

import static org.assertj.core.api.Assertions.assertThat;

import java.awt.Dialog;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;
import java.util.concurrent.RunnableFuture;

import javax.swing.SwingUtilities;

import org.assertj.swing.core.BasicRobot;
import org.assertj.swing.core.GenericTypeMatcher;
import org.assertj.swing.core.Robot;
import org.assertj.swing.edt.FailOnThreadViolationRepaintManager;
import org.assertj.swing.edt.GuiActionRunner;
import org.assertj.swing.fixture.FrameFixture;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;

import ch.teemoo.bobby.GUITestExtension;
import ch.teemoo.bobby.helpers.GuiHelper;
import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Queen;

@ExtendWith(GUITestExtension.class)
public class BoardViewSwingTest {
	private BoardView frame;
	private FrameFixture window;

	@BeforeAll
	static void setupOnce() {
		FailOnThreadViolationRepaintManager.install();
	}

	@AfterAll
	public static final void teardownOnce() {
		FailOnThreadViolationRepaintManager.uninstall();
	}

	@BeforeEach
	protected void setup() {
		Robot robot = BasicRobot.robotWithNewAwtHierarchy();
		frame = GuiActionRunner.execute(() -> new BoardView("test", new GuiHelper(), true));
		window = new FrameFixture(robot, frame);
		window.show(); // shows the frame to test
	}

	@AfterEach
	protected void teardown() {
		window.cleanUp();
	}

	@Test
	public void testPromotionDialog() throws InterruptedException, ExecutionException {
		// given
		Color color = Color.BLACK;

		// when
		RunnableFuture<Piece> rf = new FutureTask<>(() -> frame.promotionDialog(color));
		SwingUtilities.invokeLater(rf);

		// then
		window.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
			@Override
			protected boolean isMatching(Dialog dialog) {
				return "Promotion".equals(dialog.getTitle());
			}
		}).close();
		Piece piece = rf.get();
		assertThat(piece).isInstanceOf(Queen.class);
		assertThat(piece.getColor()).isEqualTo(Color.BLACK);
	}

	@Test
	public void testPopupInfo() {
		SwingUtilities.invokeLater(() -> frame.popupInfo("An info here"));
		window.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
			@Override
			protected boolean isMatching(Dialog dialog) {
				return "Info".equals(dialog.getTitle());
			}
		}).close();
	}

	@Test
	public void testPopupError() {
		SwingUtilities.invokeLater(() -> frame.popupError("An info here"));
		window.dialog(new GenericTypeMatcher<Dialog>(Dialog.class) {
			@Override
			protected boolean isMatching(Dialog dialog) {
				return "Error".equals(dialog.getTitle());
			}
		}).close();
	}
}
