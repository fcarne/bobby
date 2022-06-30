package ch.teemoo.bobby.helpers;

import static org.assertj.core.api.Assertions.assertThat;

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
  void setup() {
    this.botFactory = new BotFactory(moveService, openingService);
  }

  @Test
  void getRandomBot_returnsRandomBot() {
    Bot bot = botFactory.getRandomBot();
    assertThat(bot).isInstanceOf(RandomBot.class);
  }

  @Test
  void getTraditionalBot_noError_returnsTraditionalWithLevel2() {
    Bot bot = botFactory.getTraditionalBot(2, null);
    assertThat(bot).isInstanceOf(TraditionalBot.class);
    assertThat(bot.getDescription()).contains("level 2");
  }

  /* @Test
  void getTraditionalBot_wrongLevel_throwsRuntime() {
    assertThatRuntimeException().isThrownBy(() -> botFactory.getTraditionalBot(-1, null));
    assertThatRuntimeException().isThrownBy(() -> botFactory.getTraditionalBot(3, null));
  }

  @Test
  void getTraditionalBot_wrongTimeout_throwsRuntime() {
    assertThatRuntimeException().isThrownBy(() -> botFactory.getTraditionalBot(1, 60));
  }*/

  @Test
  void getExperiencedBot_noError_returnsExperiencedWithLevel0() {
    Bot bot = botFactory.getExperiencedBot(0, null);
    assertThat(bot).isInstanceOf(ExperiencedBot.class);
    assertThat(bot.getDescription()).contains("level 0");
  }

  /*@Test
  void getExperiencedBot_wrongLevel_throwsRuntime() {
    assertThatRuntimeException().isThrownBy(() -> botFactory.getExperiencedBot(-1, null));
    assertThatRuntimeException().isThrownBy(() -> botFactory.getExperiencedBot(3, null));
  }

  @Test
  void getExperiencedBot_wrongTimeout_throwsRuntime() {
    assertThatRuntimeException().isThrownBy(() -> botFactory.getExperiencedBot(1, 60));
  }*/

  @Test
  void getStrongestBot_returnsExperiencedBot() {
    Bot bot = botFactory.getStrongestBot();
    assertThat(bot).isInstanceOf(ExperiencedBot.class);
  }

}
