package ch.teemoo.bobby;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.swing.launcher.ApplicationLauncher.application;
import static org.junit.jupiter.params.provider.Arguments.arguments;

import java.util.stream.Stream;

import javax.swing.UIManager;

import org.assertj.swing.edt.FailOnThreadViolationRepaintManager;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import com.formdev.flatlaf.FlatIntelliJLaf;

import ch.teemoo.bobby.extension.GUITestExtension;

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
		application(Bobby.class).withArgs(args).start(); 
		assertThat(UIManager.getLookAndFeel().getClass().getName()).isEqualTo(expected);
	}

	private static Stream<Arguments> main_argsPassed_lookAndFeelChanged() {
		return Stream.of(arguments(new String[] { "default" }, UIManager.getSystemLookAndFeelClassName()),
				arguments(new String[] { "random" }, FlatIntelliJLaf.class.getName()),
				arguments(new String[] {}, FlatIntelliJLaf.class.getName())
				);
	}

}
