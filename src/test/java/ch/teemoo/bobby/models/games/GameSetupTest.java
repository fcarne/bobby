package ch.teemoo.bobby.models.games;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.api.Test;

import ch.teemoo.bobby.models.players.Human;
import ch.teemoo.bobby.models.players.Player;

public class GameSetupTest {

	@Test
	public void constructor_ok_returnSetup() {
		// given
		Player white = new Human("White");
		Player black = new Human("Black");

		// when
		GameSetup gameSetup = new GameSetup(white, black);

		// then
		assertThat(gameSetup.getWhitePlayer()).isEqualTo(white);
		assertThat(gameSetup.getBlackPlayer()).isEqualTo(black);
	}
}
