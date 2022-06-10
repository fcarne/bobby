package ch.teemoo.bobby.models.players;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.params.provider.Arguments.arguments;

import java.util.stream.Stream;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

class BotTest {
	
	@ParameterizedTest
	@MethodSource
    public void constructor_ok_returnBot(Player bot, String name, String description) {

		assertThat(bot.getName()).isEqualTo(name);
        assertThat(bot.getDescription()).isEqualTo(description);
        assertThat(bot.isBot()).isTrue();
    }
	
	private static Stream<Arguments> constructor_ok_returnBot() {
		return Stream.of(
				arguments(new RandomBot(null), "Bobby", "RandomBot Bobby"),
				arguments(new TraditionalBot(1, 5, null), "Bobby", "TraditionalBot Bobby (level 1)"),
				arguments(new ExperiencedBot(3, 5, null, null), "Bobby", "ExperiencedBot Bobby (level 3)")
			);
	}

}
