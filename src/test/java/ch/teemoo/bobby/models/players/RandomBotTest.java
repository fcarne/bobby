package ch.teemoo.bobby.models.players;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyList;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.when;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.pieces.Knight;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Rook;
import ch.teemoo.bobby.services.MoveService;
import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

@ExtendWith(MockitoExtension.class)
public class RandomBotTest {
  @Mock
  Game game;

  @Mock
  MoveService moveService;

  @Test
  void selectMove_moveList_returnElementOfList() {

    Move move1 = new Move(new Rook(Color.WHITE), 3, 4, 4, 4);
    Move move2 = new Move(new Knight(Color.WHITE), 2, 4, 5, 5);
    Move move3 = new Move(new Pawn(Color.WHITE), 4, 5, 4, 6);
    List<Move> moves = new ArrayList<>();
    moves.add(move1);
    moves.add(move2);
    moves.add(move3);
    Bot bot = new RandomBot(moveService);

    when(moveService.computeAllMoves(any(), any(), anyList(), eq(true))).thenReturn(moves);

    assertThat(bot.selectMove(game)).isIn(moves);
  }

  @Test
  void isDrawAcceptable_ok_returnsRandomBoolean() {
    Bot bot = new RandomBot(null);
    assertThat(bot.isDrawAcceptable(null)).isInstanceOf(Boolean.class);
  }

  @Test
  void isDrawAcceptable_ok_returnsTrueAndFalse_PIT() {
    Bot bot = new RandomBot(null);
    boolean accepted = bot.isDrawAcceptable(game);
    boolean opposite;
    
    do {
      opposite = bot.isDrawAcceptable(game);
    } while (opposite == accepted);
    
    assertThat(accepted).isNotEqualTo(opposite);
  }
}
