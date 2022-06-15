package ch.teemoo.bobby.helpers;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.junit.jupiter.MockitoExtension;

@ExtendWith(MockitoExtension.class)
class GuiHelperTest {

  @Test
  void constructor_normalBehaviour_returnHelper() {
    GuiHelper helper = new GuiHelper();
    assertThat(helper.getVersion()).isEqualTo("1.0.0");
    assertThat(helper.getPieceFont()).hasFieldOrPropertyWithValue("name", "Free Serif");
    assertThat(helper.getPieceFont()).hasFieldOrPropertyWithValue("size", 72);
  }

}
