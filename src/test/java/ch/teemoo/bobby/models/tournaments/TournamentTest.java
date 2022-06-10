package ch.teemoo.bobby.models.tournaments;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import ch.teemoo.bobby.models.players.Player;
import ch.teemoo.bobby.models.players.RandomBot;
import ch.teemoo.bobby.services.MoveService;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import org.mockito.Mock;

public class TournamentTest {
	private Player player1;
	private Player player2;
	private Player player3;
	private List<Player> participants;
	private Tournament tournament;

	@Mock
	MoveService moveService;

	@BeforeEach
	public void setup() {
		player1 = new RandomBot(moveService);
		player2 = new RandomBot(moveService);
		player3 = new RandomBot(moveService);
		participants = Arrays.asList(player1, player2, player3);
		tournament = new Tournament(participants);
	}

	@Test
	public void constructor_newTournament_matchesGenerated() {
		List<Match> matches = tournament.getMatches();
		assertThat(matches).hasSize(3);
		assertThat(matches.stream().filter(m -> m.getPlayer1() == player1 || m.getPlayer2() == player1)
				.collect(Collectors.toList())).hasSize(participants.size() - 1);
		assertThat(matches.stream().filter(m -> m.getPlayer1() == player2 || m.getPlayer2() == player2)
				.collect(Collectors.toList())).hasSize(participants.size() - 1);
		assertThat(matches.stream().filter(m -> m.getPlayer1() == player3 || m.getPlayer2() == player3)
				.collect(Collectors.toList())).hasSize(participants.size() - 1);
	}

	@Test
	public void getParticipantScores_newTournament_return0ForAll() {
		Map<Player, Float> scores = tournament.getParticipantScores();

		assertThat(scores).hasSize(participants.size());
		assertThat(new ArrayList<>(scores.keySet())).containsExactlyInAnyOrderElementsOf(participants);
		assertThat(scores.values().stream().allMatch(score -> score == 0f)).isTrue();
	}

	@Test
	public void getScoreboard_newTournament_allParticipantArePresent() {
		assertThat(tournament.getScoreboard())
				.contains(player1.getDescription())
				.contains(player2.getDescription())
				.contains(player3.getDescription())
				.contains("1.", "2.", "3.");
	}

	@Test
	public void toString_newTournament_returnScoreboard() {
		assertThat(tournament.toString()).isEqualTo(tournament.getScoreboard());
	}
}
