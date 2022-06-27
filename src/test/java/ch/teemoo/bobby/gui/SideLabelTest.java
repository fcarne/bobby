package ch.teemoo.bobby.gui;

import static org.assertj.core.api.Assertions.assertThat;

import javax.swing.SwingConstants;
import org.junit.jupiter.api.Test;

public class SideLabelTest {

  @Test
  void constructor_newLabel_hasDefault() {
    SideLabel sideLabel = new SideLabel("A");
    assertThat(sideLabel.getText()).isEqualTo("A");
    assertThat(sideLabel.getHorizontalAlignment()).isEqualTo(SwingConstants.CENTER);
    assertThat(sideLabel.isOpaque()).isTrue();
  }
}
