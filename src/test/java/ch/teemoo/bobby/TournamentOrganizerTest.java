package ch.teemoo.bobby;

import static com.github.stefanbirkner.systemlambda.SystemLambda.tapSystemOutNormalized;
import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.doReturn;
import static org.mockito.Mockito.spy;

import ch.teemoo.bobby.gui.IBoardView;
import ch.teemoo.bobby.gui.NoBoardView;
import ch.teemoo.bobby.helpers.BotFactory;
import ch.teemoo.bobby.helpers.GameFactory;
import ch.teemoo.bobby.models.games.GameResult;
import ch.teemoo.bobby.models.players.Bot;
import ch.teemoo.bobby.models.players.ExperiencedBot;
import ch.teemoo.bobby.models.players.Player;
import ch.teemoo.bobby.models.players.RandomBot;
import ch.teemoo.bobby.models.players.TraditionalBot;
import ch.teemoo.bobby.models.tournaments.Match;
import ch.teemoo.bobby.services.FileService;
import ch.teemoo.bobby.services.MoveService;
import ch.teemoo.bobby.services.OpeningService;
import ch.teemoo.bobby.services.PortableGameNotationService;
import java.util.List;
import java.util.concurrent.ExecutionException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.mockito.junit.jupiter.MockitoExtension;

@ExtendWith(MockitoExtension.class)
public class TournamentOrganizerTest {

  TournamentOrganizer tournamentOrganizer;
  final MoveService moveService = new MoveService();

  @BeforeEach
  void setup() {
    tournamentOrganizer = new TournamentOrganizer(true);
  }

  @Test
  void getAllPlayers_none_returns5Players() {
    List<Player> players = tournamentOrganizer.getAllPlayers();
    assertThat(players).hasSize(5);
    assertThat(players.stream().filter(RandomBot.class::isInstance)).hasSize(1);
    assertThat(players.stream().filter(TraditionalBot.class::isInstance)).hasSize(4);
    assertThat(players.stream().filter(ExperiencedBot.class::isInstance)).hasSize(1);
  }

  @Test
  void getOnlyTwoFastPlayers_none_returns2Players() {
    List<Player> players = tournamentOrganizer.getOnlyTwoFastPlayers();
    assertThat(players).hasSize(2);
    assertThat(players).first().isInstanceOf(RandomBot.class);
    assertThat(players).last().isInstanceOf(TraditionalBot.class);
  }

  @ParameterizedTest
  @CsvSource({ "WHITE_WINS,1,0", "BLACK_WINS,0,1", "DRAW,0.5,0.5" })
  void playRound_newMatch_pointsCorrectlyAssigned(GameResult.Result result,
      float whitePoints, float blackPoints) throws InterruptedException, ExecutionException {
    final FileService fileService = new FileService();
    final PortableGameNotationService pgnService = new PortableGameNotationService(moveService);
    final OpeningService openingService = new OpeningService(pgnService, fileService);
    final GameFactory gameFactory = new GameFactory();
    final BotFactory botFactory = new BotFactory(moveService, openingService);
    IBoardView boardView = new NoBoardView();
    GameController controller = spy(new GameController(boardView, gameFactory, botFactory,
        moveService, fileService, pgnService));

    doReturn(new GameResult(0, result)).when(controller).getResult(any(), any());

    Bot bot1 = new TraditionalBot(0, null, moveService);
    Bot bot2 = new RandomBot(moveService);
    Match match = new Match(bot1, bot2);

    tournamentOrganizer.playRound(controller, match, false);

    assertThat(match.getScoreByPlayer(bot1)).isEqualTo(whitePoints);
    assertThat(match.getScoreByPlayer(bot2)).isEqualTo(blackPoints);

  }

  @Test
  void run_fastTournament_resultsLogged() throws Exception {
    String text = tapSystemOutNormalized(() -> {
      tournamentOrganizer.run();
    });
    assertThat(text).contains("2 players has registered")
        .contains("There will be 2 rounds per match, participants play against each other")
        .contains("Tournament is open!")
        .contains("Tournament is over!")
        .contains("Here is the scoreboard");
  }

  @Test
  void run_longTournament_resultsLogged() throws Exception {
    TournamentOrganizer organizer = spy(new TournamentOrganizer(false));

    doReturn(organizer.getOnlyTwoFastPlayers()).when(organizer).getAllPlayers();

    String text = tapSystemOutNormalized(() -> {
      organizer.run();
    });

    assertThat(text)
        .contains("There will be 4 rounds per match, participants play against each other")
        .contains("Tournament is open!")
        .contains("Tournament is over!")
        .contains("Here is the scoreboard");
  }
}
