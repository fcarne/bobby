package ch.teemoo.bobby.helpers;

import ch.teemoo.bobby.models.players.Bot;
import ch.teemoo.bobby.models.players.ExperiencedBot;
import ch.teemoo.bobby.models.players.RandomBot;
import ch.teemoo.bobby.models.players.TraditionalBot;
import ch.teemoo.bobby.services.MoveService;
import ch.teemoo.bobby.services.OpeningService;

public class BotFactory {
  private static /*@ spec_public @*/ final int LEVEL_MAX = 2;
  private static /*@ spec_public @*/ final int TIMEOUT_MAX = 10;

  private final MoveService moveService;
  private final OpeningService openingService;

  public BotFactory(MoveService moveService, OpeningService openingService) {
    this.moveService = moveService;
    this.openingService = openingService;
  }

  //@ ensures \result instanceof RandomBot;
  public Bot getRandomBot() {
    return new RandomBot(moveService);
  }

  //@ requires 0 <= level <= LEVEL_MAX;
  //@ requires timeout == null || 0 <= timeout <= TIMEOUT_MAX;
  //@ ensures \result instanceof TraditionalBot;
  public Bot getTraditionalBot(int level, Integer timeout) {
    return new TraditionalBot(level, timeout, moveService);
  }

  //@ requires 0 <= level <= LEVEL_MAX;
  //@ requires timeout == null || 0 <= timeout <= TIMEOUT_MAX;
  //@ ensures \result instanceof ExperiencedBot;
  public Bot getExperiencedBot(int level, Integer timeout) {
    return new ExperiencedBot(level, timeout, moveService, openingService);
  }

  //@ ensures \result instanceof ExperiencedBot;
  public Bot getStrongestBot() {
    return getExperiencedBot(LEVEL_MAX, TIMEOUT_MAX);
  }

}
