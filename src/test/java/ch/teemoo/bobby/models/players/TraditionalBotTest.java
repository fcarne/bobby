package ch.teemoo.bobby.models.players;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.ArgumentMatchers.isNull;
import static org.mockito.ArgumentMatchers.notNull;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;

import ch.teemoo.bobby.models.games.Game;
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
  public void selectMove_timeout_selectMoveCalled(Integer timeout) {
    int level = 2;
    Bot bot = new TraditionalBot(level, timeout, moveService);

    bot.selectMove(game);
    verify(moveService, times(1)).selectMove(any(), eq(level),
        timeout != null ? notNull() : isNull());
  }

  @Test
  public void testIsDrawAcceptable() {
    Bot bot = new TraditionalBot(1, null, moveService);
    bot.isDrawAcceptable(game);
    verify(moveService).isDrawAcceptable(eq(game));
  }
}
