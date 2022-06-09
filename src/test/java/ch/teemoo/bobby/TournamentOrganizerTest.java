package ch.teemoo.bobby;

import static com.github.stefanbirkner.systemlambda.SystemLambda.tapSystemOutNormalized;
import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.api.Test;

public class TournamentOrganizerTest {

	@Test
	public void testTournamentOrganizer() throws Exception {
		TournamentOrganizer tournamentOrganizer = new TournamentOrganizer(true);
		String text = tapSystemOutNormalized(() -> {
			tournamentOrganizer.run();
		});
		assertThat(text).contains("2 players has registered")
				.contains("There will be 2 rounds per match, participants play against each other")
				.contains("Tournament is open!").contains("Tournament is over!").contains("Here is the scoreboard");
	}
}
