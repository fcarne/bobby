package ch.teemoo.bobby.models;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

public class PositionTest {
    @Test
    public void positionConstructor_ok_returnsCorrect() {
        Position position = new Position(4, 5);
        assertThat(position.getFile()).isEqualTo(4);
        assertThat(position.getRank()).isEqualTo(5);
    }
}
