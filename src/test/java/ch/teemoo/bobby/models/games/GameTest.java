package ch.teemoo.bobby.models.games;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.params.provider.Arguments.arguments;

import ch.teemoo.bobby.models.Board;
import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.pieces.Bishop;
import ch.teemoo.bobby.models.pieces.King;
import ch.teemoo.bobby.models.pieces.Knight;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Queen;
import ch.teemoo.bobby.models.pieces.Rook;
import ch.teemoo.bobby.models.players.Human;
import ch.teemoo.bobby.models.players.Player;
import java.util.stream.Stream;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.EnumSource;
import org.junit.jupiter.params.provider.MethodSource;

public class GameTest {

  Player whitePlayer;
  Player blackPlayer;

  @BeforeEach
  public void setupPlayers() {
    whitePlayer = new Human("White");
    blackPlayer = new Human("Black");
  }

  @Test
  public void constructor_newGame_hasDefault() {
    Game game = new Game(whitePlayer, blackPlayer);
    game.setOpening("Sicilian Defense");

    assertThat(game.getToPlay()).isEqualTo(Color.WHITE);
    assertThat(game.getPlayerToPlay()).isEqualTo(whitePlayer);
    assertThat(game.getHistory()).isEmpty();
    assertThat(game.getState()).isEqualTo(GameState.IN_PROGRESS);

    assertThat(game.getWhitePlayer()).isEqualTo(whitePlayer);
    assertThat(game.getBlackPlayer()).isEqualTo(blackPlayer);
    assertThat(game.getOpening()).isEqualTo("Sicilian Defense");
  }

  @Test
  public void constructor_newGame_correctBoardSetup() {
    Game game = new Game(whitePlayer, blackPlayer);
    Board board = game.getBoard();
    Piece[][] pieces = board.getBoard();

    // White pieces
    assertThat(pieces[0][0]).isInstanceOf(Rook.class)
        .hasFieldOrPropertyWithValue("color", Color.WHITE);
    assertThat(pieces[0][1]).isInstanceOf(Knight.class)
        .hasFieldOrPropertyWithValue("color", Color.WHITE);
    assertThat(pieces[0][2]).isInstanceOf(Bishop.class)
        .hasFieldOrPropertyWithValue("color", Color.WHITE);
    assertThat(pieces[0][3]).isInstanceOf(Queen.class)
        .hasFieldOrPropertyWithValue("color", Color.WHITE);
    assertThat(pieces[0][4]).isInstanceOf(King.class)
        .hasFieldOrPropertyWithValue("color", Color.WHITE);
    assertThat(pieces[0][5]).isInstanceOf(Bishop.class)
        .hasFieldOrPropertyWithValue("color", Color.WHITE);
    assertThat(pieces[0][6]).isInstanceOf(Knight.class)
        .hasFieldOrPropertyWithValue("color", Color.WHITE);
    assertThat(pieces[0][7]).isInstanceOf(Rook.class)
        .hasFieldOrPropertyWithValue("color", Color.WHITE);
    for (int i = 0; i < 8; i++) {
      assertThat(pieces[1][i]).isInstanceOf(Pawn.class)
          .hasFieldOrPropertyWithValue("color", Color.WHITE);
    }

    // Black pieces
    assertThat(pieces[7][0]).isInstanceOf(Rook.class)
        .hasFieldOrPropertyWithValue("color", Color.BLACK);
    assertThat(pieces[7][1]).isInstanceOf(Knight.class)
        .hasFieldOrPropertyWithValue("color", Color.BLACK);
    assertThat(pieces[7][2]).isInstanceOf(Bishop.class)
        .hasFieldOrPropertyWithValue("color", Color.BLACK);
    assertThat(pieces[7][3]).isInstanceOf(Queen.class)
        .hasFieldOrPropertyWithValue("color", Color.BLACK);
    assertThat(pieces[7][4]).isInstanceOf(King.class)
        .hasFieldOrPropertyWithValue("color", Color.BLACK);
    assertThat(pieces[7][5]).isInstanceOf(Bishop.class)
        .hasFieldOrPropertyWithValue("color", Color.BLACK);
    assertThat(pieces[7][6]).isInstanceOf(Knight.class)
        .hasFieldOrPropertyWithValue("color", Color.BLACK);
    assertThat(pieces[7][7]).isInstanceOf(Rook.class)
        .hasFieldOrPropertyWithValue("color", Color.BLACK);
    for (int i = 0; i < 8; i++) {
      assertThat(pieces[6][i]).isInstanceOf(Pawn.class)
          .hasFieldOrPropertyWithValue("color", Color.BLACK);
    }

    // Empty places
    for (int j = 2; j < 6; j++) {
      for (int i = 0; i < 8; i++) {
        assertThat(pieces[j][i]).isNull();
      }
    }
  }

  @Test
  public void addMoveToHistory_newMove_moveAdded() {
    Game game = new Game(whitePlayer, blackPlayer);
    assertThat(game.getHistory()).isEmpty();

    Move move = new Move(new Pawn(Color.WHITE), 4, 1, 4, 2);

    game.addMoveToHistory(move);
    assertThat(game.getHistory()).hasSize(1).containsExactly(move);
  }

  @Test
  public void testRemoveLastMoveFromHistory() {
    Game game = new Game(new Human("Player 1"), new Human("Player 2"));
    Move move = new Move(new Pawn(Color.WHITE), 4, 1, 4, 2);
    game.addMoveToHistory(move);

    assertThat(game.getHistory()).containsExactly(move);

    game.removeLastMoveFromHistory();

    assertThat(game.getHistory()).isEmpty();
  }

  @Test
  public void getPlayerByColor_whiteAndBlack_returnRightPlayer() {
    Game game = new Game(whitePlayer, blackPlayer);
    assertThat(game.getPlayerByColor(Color.WHITE)).isEqualTo(whitePlayer);
    assertThat(game.getPlayerByColor(Color.BLACK)).isEqualTo(blackPlayer);
  }

  @ParameterizedTest
  @MethodSource
  public void canBePlayed_newGame_returnExpected(Player whitePlayer, Player blackPlayer,
      GameState state, boolean expected) {
    Game game = new Game(whitePlayer, blackPlayer);
    game.setState(state);

    assertThat(game.canBePlayed()).isEqualTo(expected);
  }

  private static Stream<Arguments> canBePlayed_newGame_returnExpected() {
    Player player1 = new Human("White");
    Player player2 = new Human("Black");

    return Stream.of(arguments(player1, player2, GameState.IN_PROGRESS, true),
        arguments(null, player2, GameState.IN_PROGRESS, false),
        arguments(player1, null, GameState.IN_PROGRESS, false),
        arguments(player1, player2, GameState.LOSS, false));
  }

  @ParameterizedTest
  @EnumSource(Color.class)
  public void getPlayerToPlayAndWaiting_whiteAndBlack_returnsColorAsToPlay(Color color) {
    Game game = new Game(whitePlayer, blackPlayer);
    game.setToPlay(color);

    Player waiting;
    Player toPlay;

    switch (color) {
      case WHITE:
        toPlay = whitePlayer;
        waiting = blackPlayer;
        break;
      default:
        toPlay = blackPlayer;
        waiting = whitePlayer;
    }

    assertThat(game.getPlayerToPlay()).isEqualTo(toPlay);
    assertThat(game.getPlayerWaiting()).isEqualTo(waiting);
  }

}
