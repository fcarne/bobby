package ch.teemoo.bobby.models.players;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.ArgumentMatchers.isNull;
import static org.mockito.ArgumentMatchers.notNull;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.services.MoveService;
import ch.teemoo.bobby.services.OpeningService;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

@ExtendWith(MockitoExtension.class)
public class ExperiencedBotTest {
  @Mock
  MoveService moveService;

  @Mock
  OpeningService openingService;

  @Mock
  Game game;

  @Test
  void selectMove_noOpening_callSuperSelectMove() {
    int level = 2;
    Integer timeout = 3;
    Bot bot = new ExperiencedBot(level, timeout, moveService, openingService);

    when(openingService.findPossibleMovesForHistory(any())).thenReturn(Collections.emptyList());

    bot.selectMove(game);
    verify(moveService, times(1)).selectMove(any(), eq(level), notNull());
  }

  @Test
  void selectMove_withOpenings_returnRandomOpening() {
    Move openingMove1 = new Move(new Pawn(Color.WHITE), 4, 1, 4, 3);
    Move openingMove2 = new Move(new Pawn(Color.WHITE), 4, 1, 4, 3);
    Move openingMove3 = new Move(new Pawn(Color.WHITE), 4, 1, 4, 3);
    List<Move> moves = new ArrayList<>();
    moves.add(openingMove1);
    moves.add(openingMove2);
    moves.add(openingMove3);

    when(openingService.findPossibleMovesForHistory(any())).thenReturn(moves);

    int level = 2;
    Integer timeout = 3;
    Bot bot = new ExperiencedBot(level, timeout, moveService, openingService);
    Move move = bot.selectMove(game);

    verify(moveService, never()).selectMove(any(), anyInt(), any());
    assertThat(move).isIn(moves);
  }
  
  @Test
  void selectMove_moveIsPawnE4_returnSameMove_PIT() {
    Move move = new Move(new Pawn(Color.WHITE), 4, 1, 4, 3);
    Bot bot = new ExperiencedBot(1, null, moveService, openingService);
    when(moveService.selectMove(eq(game), anyInt(), isNull())).thenReturn(move);

    Move selected = bot.selectMove(game);

    assertThat(selected).isNotNull().isEqualTo(move);
  }

}
