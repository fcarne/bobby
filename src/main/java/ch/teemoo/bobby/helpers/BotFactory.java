package ch.teemoo.bobby.helpers;

import ch.teemoo.bobby.models.players.Bot;
import ch.teemoo.bobby.models.players.ExperiencedBot;
import ch.teemoo.bobby.models.players.RandomBot;
import ch.teemoo.bobby.models.players.TraditionalBot;
import ch.teemoo.bobby.services.MoveService;
import ch.teemoo.bobby.services.OpeningService;

public class BotFactory {
  private static final int LEVEL_MAX = 2;
  private static final int LEVEL_MIN = 0;
  private static final int TIMEOUT_MAX = 10;

  private final MoveService moveService;
  private final OpeningService openingService;

  public BotFactory(MoveService moveService, OpeningService openingService) {
    this.moveService = moveService;
    this.openingService = openingService;
  }

  public Bot getRandomBot() {
    return new RandomBot(moveService);
  }

  public Bot getTraditionalBot(int level, Integer timeout) {
    checkLevel(level);
    checkTimeout(timeout);
    return new TraditionalBot(level, timeout, moveService);
  }

  public Bot getExperiencedBot(int level, Integer timeout) {
    checkLevel(level);
    checkTimeout(timeout);
    return new ExperiencedBot(level, timeout, moveService, openingService);
  }

  public Bot getStrongestBot() {
    return getExperiencedBot(LEVEL_MAX, TIMEOUT_MAX);
  }

  private void checkLevel(int level) {
    boolean okLevel = level >= LEVEL_MIN && level <= LEVEL_MAX;
    if (!okLevel) {
      throw new RuntimeException("Bot level must be between " + LEVEL_MIN + " and " + LEVEL_MAX);
    }
  }

  private void checkTimeout(Integer timeout) {
    boolean okTimeout = timeout == null || timeout <= TIMEOUT_MAX;
    if(!okTimeout) {
      throw new RuntimeException("Bot timeout must be less than" + TIMEOUT_MAX);
    }
  }
}
