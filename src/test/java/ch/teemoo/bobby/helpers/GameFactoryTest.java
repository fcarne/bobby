package ch.teemoo.bobby.helpers;

import static org.assertj.core.api.Assertions.assertThat;

import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.games.GameSetup;
import ch.teemoo.bobby.models.players.Human;
import ch.teemoo.bobby.models.players.Player;
import org.junit.jupiter.api.Test;

public class GameFactoryTest {

  private GameFactory gameFactory = new GameFactory();

  @Test
  public void createGame_withSetup_returnSamePlayers() {
    // given
    Player whitePlayer = new Human("White");
    Player blackPlayer = new Human("Black");
    GameSetup gameSetup = new GameSetup(whitePlayer, blackPlayer);

    // when
    Game game = gameFactory.createGame(gameSetup);

    // then
    assertThat(game.getWhitePlayer()).isEqualTo(whitePlayer);
    assertThat(game.getBlackPlayer()).isEqualTo(blackPlayer);
  }

  @Test
  public void emptyGame_newGame_nullPlayers() {
    // given

    // when
    Game game = gameFactory.emptyGame();

    // then
    assertThat(game.getWhitePlayer()).isNull();
    assertThat(game.getBlackPlayer()).isNull();
  }
}
