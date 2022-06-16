package ch.teemoo.benchmark.services;

import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.players.Human;
import ch.teemoo.bobby.services.MoveService;
import ch.teemoo.bobby.services.PortableGameNotationService;
import java.io.BufferedReader;
import java.io.StringReader;
import java.time.LocalDateTime;
import java.util.Arrays;
import java.util.stream.Collectors;
import org.apache.commons.math3.stat.descriptive.DescriptiveStatistics;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class SelectMoveBenchmark {
  private static final Logger LOGGER = LoggerFactory.getLogger(SelectMoveBenchmark.class);

  private static final int MAX_DEPTH = 2;
  private static final int RUNS = 10;
  private static final String PGN_GAME_CONTENT = "[Event \"F/S Return Match\"]\n"
      + "[Site \"Belgrade, Serbia JUG\"]\n"
      + "[Date \"1992.11.04\"]\n"
      + "[Round \"29\"]\n"
      + "[White \"Fischer, Robert J.\"]\n"
      + "[Black \"Spassky, Boris V.\"]\n"
      + "[Result \"1/2-1/2\"]\n"
      + "\n"
      + "1. e4 e5 2. Nf3 Nc6 3. Bb5 a6 {This opening is called the Ruy Lopez.}\n"
      + "4. Ba4 Nf6 5. O-O Be7 6. Re1 b5 7. Bb3 d6 8. c3 O-O 9. h3 Nb8 10. d4 Nbd7\n"
      + "11. c4 c6 12. cxb5 axb5 13. Nc3 Bb7 14. Bg5 b4 15. Nb1 h6 16. Bh4 c5 17. dxe5\n"
      + "Nxe4 18. Bxe7 Qxe7 19. exd6 Qf6 20. Nbd2 Nxd6 21. Nc4 Nxc4 22. Bxc4 Nb6";

  private MoveService moveService = new MoveService();
  private PortableGameNotationService portableGameNotationService = new PortableGameNotationService(
      moveService);

  @Test
  public void selectMove_initialGame() {
    Game game = new Game(new Human("Player 1"), new Human("Player 2"));
    measureComputation(game, "Initial game", null);
  }

  @Test
  public void selectMove_midGame() {
    BufferedReader reader = new BufferedReader(new StringReader(PGN_GAME_CONTENT));

    Game game = portableGameNotationService
        .readPgnFile(reader.lines().collect(Collectors.toList()));

    measureComputation(game, "Mid game", null);
  }

  @Test
  public void selectMove_midGameWithTimeout() {
    BufferedReader reader = new BufferedReader(new StringReader(PGN_GAME_CONTENT));

    Game game = portableGameNotationService
        .readPgnFile(reader.lines().collect(Collectors.toList()));

    measureComputation(game, "Mid game with timeout", LocalDateTime.now().plusSeconds(2));
  }

  private void measureComputation(Game game, String testInfo, LocalDateTime timeout) {
    DescriptiveStatistics stats = computeWithStats(game, timeout);
    String prettyPrint = statsToString(stats);
    LOGGER.info("Stats for {}:\n{}", testInfo, prettyPrint);
  }

  private DescriptiveStatistics computeWithStats(Game game, LocalDateTime timeout) {
    DescriptiveStatistics descriptiveStatistics = new DescriptiveStatistics();
    for (int i = 0; i < RUNS; i++) {
      long start = System.currentTimeMillis();
      moveService.selectMove(game, MAX_DEPTH, timeout);
      descriptiveStatistics.addValue(System.currentTimeMillis() - start);
    }
    return descriptiveStatistics;
  }

  private String statsToString(DescriptiveStatistics descriptiveStatistics) {
    StringBuilder builder = new StringBuilder();
    builder.append("95%:     ").append(descriptiveStatistics.getPercentile(95)).append("\n");
    builder.append("90%:     ").append(descriptiveStatistics.getPercentile(90)).append("\n");
    builder.append("75%:     ").append(descriptiveStatistics.getPercentile(75)).append("\n");
    builder.append("50%:     ").append(descriptiveStatistics.getPercentile(50)).append("\n");
    builder.append("Mean:    ").append(descriptiveStatistics.getMean()).append("\n");
    builder.append("Std dev: ").append(descriptiveStatistics.getStandardDeviation()).append("\n");
    builder.append("Min:     ").append(descriptiveStatistics.getMin()).append("\n");
    builder.append("Max:     ").append(descriptiveStatistics.getMax()).append("\n");
    builder.append("Values:  ")
        .append(Arrays.toString(descriptiveStatistics.getSortedValues()))
        .append("\n");
    return builder.toString();
  }
}
