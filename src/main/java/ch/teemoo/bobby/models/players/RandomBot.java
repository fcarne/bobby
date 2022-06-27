package ch.teemoo.bobby.models.players;

import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.services.MoveService;
import java.security.SecureRandom;
import java.util.List;

public class RandomBot extends Bot {
  private static final SecureRandom RANDOM = new SecureRandom();

  public RandomBot(MoveService moveService) {
    super(moveService);
  }

  @Override
  public Move selectMove(Game game) {
    List<Move> moves = moveService.computeAllMoves(game.getBoard(), game.getToPlay(),
        game.getHistory(), true);
    return moves.get(RANDOM.nextInt(moves.size()));
  }
  
  @Override
  public boolean isDrawAcceptable(Game game) {
    return RANDOM.nextBoolean();
  }
}
