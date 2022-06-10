package ch.teemoo.bobby.models;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.api.Test;

class ColorTest {

	@Test
	void opposite_white_returnBlack() {
		assertThat(Color.WHITE.opposite()).isEqualTo(Color.BLACK);
	}
	
	@Test
	void opposite_black_returnWhite() {
		assertThat(Color.BLACK.opposite()).isEqualTo(Color.WHITE);
	}

}
