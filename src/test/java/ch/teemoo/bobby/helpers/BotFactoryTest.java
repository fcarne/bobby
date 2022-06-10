package ch.teemoo.bobby.helpers;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatExceptionOfType;

import ch.teemoo.bobby.models.players.Bot;
import ch.teemoo.bobby.models.players.ExperiencedBot;
import ch.teemoo.bobby.models.players.RandomBot;
import ch.teemoo.bobby.models.players.TraditionalBot;
import ch.teemoo.bobby.services.MoveService;
import ch.teemoo.bobby.services.OpeningService;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import org.mockito.Mock;

public class BotFactoryTest {

	private BotFactory botFactory;

	@Mock
	MoveService moveService;

	@Mock
	OpeningService openingService;

	@BeforeEach
	public void setup() {
		this.botFactory = new BotFactory(moveService, openingService);
	}

	@Test
	public void getRandomBot_returnsRandomBot() {
		Bot bot = botFactory.getRandomBot();
		assertThat(bot).isInstanceOf(RandomBot.class);
	}

	@Test
	public void getTraditionalBot_noError_returnsTraditionalWithLevel2() {
		Bot bot = botFactory.getTraditionalBot(2, null);
		assertThat(bot).isInstanceOf(TraditionalBot.class);
		assertThat(bot.getDescription()).contains("level 2");
	}

	@Test
	public void getTraditionalBot_wrongLevel_throwsAssertionError() {
		assertThatExceptionOfType(AssertionError.class).isThrownBy(() -> botFactory.getTraditionalBot(-1, null));
		assertThatExceptionOfType(AssertionError.class).isThrownBy(() -> botFactory.getTraditionalBot(3, null));
	}

	@Test
	public void getTraditionalBot_wrongTimeout_throwsAssertionError() {
		assertThatExceptionOfType(AssertionError.class).isThrownBy(() -> botFactory.getTraditionalBot(1, 60));
	}

	@Test
	public void getExperiencedBot_noError_returnsExperiencedWithLevel2() {
		Bot bot = botFactory.getExperiencedBot(2, null);
		assertThat(bot).isInstanceOf(ExperiencedBot.class);
		assertThat(bot.getDescription()).contains("level 2");
	}

	@Test
	public void getExperiencedBot_wrongLevel_throwsAssertionError() {
		assertThatExceptionOfType(AssertionError.class).isThrownBy(() -> botFactory.getExperiencedBot(-1, null));
		assertThatExceptionOfType(AssertionError.class).isThrownBy(() -> botFactory.getExperiencedBot(3, null));
	}

	@Test
	public void getExperiencedBot_wrongTimeout_throwsAssertionError() {
		assertThatExceptionOfType(AssertionError.class).isThrownBy(() -> botFactory.getExperiencedBot(1, 60));
	}

	@Test
	public void getStrongestBot_returnsExperiencedBot() {
		Bot bot = botFactory.getStrongestBot();
		assertThat(bot).isInstanceOf(ExperiencedBot.class);
	}

}
