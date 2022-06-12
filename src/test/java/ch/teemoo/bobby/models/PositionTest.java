package ch.teemoo.bobby.models;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.api.Test;

public class PositionTest {
    @Test
    public void positionConstructor_ok_returnsCorrect() {
        Position position = new Position(4, 5);
        assertThat(position.getFile()).isEqualTo(4);
        assertThat(position.getRank()).isEqualTo(5);
    }
}
