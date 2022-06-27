package ch.teemoo.bobby.models.players;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.ArgumentMatchers.isNull;
import static org.mockito.ArgumentMatchers.notNull;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.services.MoveService;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

@ExtendWith(MockitoExtension.class)
public class TraditionalBotTest {
  @Mock
  MoveService moveService;

  @Mock
  Game game;

  @ParameterizedTest
  @ValueSource(ints = { 2 })
  @NullSource
  void selectMove_timeout_selectMoveCalled(Integer timeout) {
    int level = 2;
    Bot bot = new TraditionalBot(level, timeout, moveService);

    bot.selectMove(game);
    verify(moveService, times(1)).selectMove(any(), eq(level),
        timeout != null ? notNull() : isNull());
  }

  @Test
  void isDrawAcceptable_drawNotAcceptable_returnFalse() {
    Bot bot = new TraditionalBot(1, null, moveService);
    
    bot.isDrawAcceptable(game);
    verify(moveService).isDrawAcceptable(eq(game));
  }
  
  @Test
  void isDrawAcceptable_bothCases_returnTrueAndFalse_PIT() {
    when(moveService.isDrawAcceptable(any())).thenReturn(false);
    Bot bot = new TraditionalBot(1, null, moveService);

    boolean accepted = bot.isDrawAcceptable(game);
    assertThat(accepted).isFalse();

    when(moveService.isDrawAcceptable(any())).thenReturn(true);

    accepted = bot.isDrawAcceptable(game);
    assertThat(accepted).isTrue();
  }

  @Test
  void selectMove_moveIsPawnE4_returnSelectedMove_PIT() {
    Move move = new Move(new Pawn(Color.WHITE), 4, 1, 4, 3);
    Bot bot = new TraditionalBot(1, null, moveService);
    when(moveService.selectMove(eq(game), anyInt(), isNull())).thenReturn(move);

    Move selected = bot.selectMove(game);

    assertThat(selected).isNotNull().isEqualTo(move);
  }
}
