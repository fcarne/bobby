package ch.teemoo.bobby.models.players;

import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.services.MoveService;
import ch.teemoo.bobby.services.OpeningService;
import java.security.SecureRandom;
import java.util.List;

public class ExperiencedBot extends TraditionalBot {
  private static final SecureRandom RANDOM = new SecureRandom();
  private final OpeningService openingService;

  public ExperiencedBot(int level, Integer timeout, MoveService moveService,
      OpeningService openingService) {
    super(level, timeout, moveService);
    this.openingService = openingService;
  }

  @Override
  public Move selectMove(Game game) {
    List<Move> openingMoves = openingService.findPossibleMovesForHistory(game.getHistory());
    Move move;
    if (openingMoves.isEmpty()) {
      move = super.selectMove(game);
    } else {
      move = openingMoves.get(RANDOM.nextInt(openingMoves.size()));
    }
    
    return move;
  }
}
