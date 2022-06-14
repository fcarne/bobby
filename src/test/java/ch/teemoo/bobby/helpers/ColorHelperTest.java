package ch.teemoo.bobby.helpers;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

import ch.teemoo.bobby.models.Color;

public class ColorHelperTest {

    @ParameterizedTest
    @EnumSource(Color.class)
    public void swap_swapTwice_returnSameColor(Color color) {
		Color other = color == Color.WHITE ? Color.BLACK : Color.WHITE;
        Color swapColor = ColorHelper.swap(color);
        
        assertThat(swapColor).isEqualTo(other);
        assertThat(ColorHelper.swap(swapColor)).isEqualTo(color);
    }

}
