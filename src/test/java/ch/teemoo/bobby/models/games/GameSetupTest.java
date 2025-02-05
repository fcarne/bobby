package ch.teemoo.bobby.models.games;

import static org.assertj.core.api.Assertions.assertThat;

import ch.teemoo.bobby.models.players.Human;
import ch.teemoo.bobby.models.players.Player;
import org.junit.jupiter.api.Test;

public class GameSetupTest {

  @Test
  void constructor_ok_returnSetup() {
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
