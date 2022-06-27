package ch.teemoo.bobby.models.tournaments;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatRuntimeException;

import ch.teemoo.bobby.models.players.Player;
import ch.teemoo.bobby.models.players.RandomBot;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestInstance;
import org.junit.jupiter.api.TestInstance.Lifecycle;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

@TestInstance(Lifecycle.PER_CLASS)
public class MatchTest {
  private Player player1;
  private Player player2;
  private Match match;

  @BeforeEach
  void setup() {
    this.player1 = new RandomBot(null);
    this.player2 = new RandomBot(null);
    this.match = new Match(player1, player2);
  }

  @Test
  void constructor_newMatch_hasDefault() {
    assertThat(match.getPlayer1()).isEqualTo(player1);
    assertThat(match.getPlayer2()).isEqualTo(player2);
  }

  @Test
  void toString_ok_returnMatchDescription() {
    assertThat(match.toString()).contains("Players:")
        .contains("Score:")
        .contains("Games:")
        .contains("Moves:")
        .contains("Avg m/g:");
  }

  @Test
  void getScoreByPlayer_matchPlayers_return0() {
    assertThat(match.getScoreByPlayer(player1)).isEqualTo(0);
    assertThat(match.getScoreByPlayer(player2)).isEqualTo(0);
  }

  @Test
  void getScoreByPlayer_nonParticipant_throwRuntimeException() {
    assertThatRuntimeException().isThrownBy(() -> match.getScoreByPlayer(new RandomBot(null)))
        .withMessage("Given player does not take part to this match");
  }

  @Test
  void isPlayerTakingPartToTheMatch_participant_returnTrue() {
    assertThat(match.isPlayerTakingPartToTheMatch(player1)).isTrue();
    assertThat(match.isPlayerTakingPartToTheMatch(player2)).isTrue();
  }

  @Test
  void isPlayerTakingPartToTheMatch_nonParticipant_returnFalse() {
    assertThat(match.isPlayerTakingPartToTheMatch(new RandomBot(null))).isFalse();
  }

  @Test
  void addDraw_newMatch_halfPointEach() {
    // given
    float score1 = match.getScoreByPlayer(player1);
    float score2 = match.getScoreByPlayer(player2);

    // when
    match.addDraw(34);

    // then
    assertThat(match.getScoreByPlayer(player1)).isEqualTo(score1 + 0.5f);
    assertThat(match.getScoreByPlayer(player2)).isEqualTo(score2 + 0.5f);
  }

  @ParameterizedTest
  @ValueSource(ints = { 1, 2 })
  void addWin_playerWins_onePointAdded(int winning) {
    // given
    Player winningPlayer;
    Player losingPlayer;

    if (winning == 1) {
      winningPlayer = player1;
      losingPlayer = player2;
    } else {
      winningPlayer = player2;
      losingPlayer = player1;
    }

    final float score1 = match.getScoreByPlayer(winningPlayer);
    final float score2 = match.getScoreByPlayer(losingPlayer);

    // when
    match.addWin(winningPlayer, 65);

    // then
    assertThat(match.getScoreByPlayer(winningPlayer)).isEqualTo(score1 + 1f);
    assertThat(match.getScoreByPlayer(losingPlayer)).isEqualTo(score2);
  }

  @Test
  void addWin_nonParticipant_throwsRuntime() {
    assertThatRuntimeException().isThrownBy(() -> match.addWin(new RandomBot(null), 21))
        .withMessage("Player not found");
  }
  
  @Test
  void toString_addDrawAndWin_returnUpdatedStats_PIT() {
    match.addDraw(50);
    match.addWin(player1, 10);
    
    assertThat(match.toString()).contains("Avg m/g: \t30.0");
  }
}
