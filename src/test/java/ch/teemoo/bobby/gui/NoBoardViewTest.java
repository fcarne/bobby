package ch.teemoo.bobby.gui;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class NoBoardViewTest {

  private NoBoardView view;

  @BeforeEach
  void setup() {
    view = new NoBoardView();
  }

  @Test
  void getSquares_none_returnsEmpty() {
    assertThat(view.getSquares()).hasNumberOfRows(0);
  }

  @Test
  void saveGameDialog_none_doesNothing() {
    assertThat(view.saveGameDialog()).isEmpty();
  }

  @Test
  void loadGameDialog_none_doesNothing() {
    assertThat(view.loadGameDialog()).isEmpty();
  }

  @Test
  void gameSetupDialog_none_doesNothing() {
    assertThat(view.gameSetupDialog(null, false)).isNull();
  }

  @Test
  void promotionDialog_none_doesNothing() {
    assertThat(view.promotionDialog(null)).isNull();
  }

}
