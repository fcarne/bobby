package ch.teemoo.bobby.models.players;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.api.Test;

public class HumanTest {

    @Test
    public void constructor_ok_returnHuman() {
        String name = "Player's Name";
        Player human = new Human(name);
        
        assertThat(human.getName()).isEqualTo(name);
        assertThat(human.getDescription()).isEqualTo("Human Player's Name");
        assertThat(human.isBot()).isFalse();
    }
}
