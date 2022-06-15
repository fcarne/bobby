package ch.teemoo.bobby.gui;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class NoBoardViewTest {

  private NoBoardView view;

  @BeforeEach
  public void setup() {
    view = new NoBoardView();
  }

  @Test
  public void getSquares_none_returnsEmpty() {
    assertThat(view.getSquares()).hasNumberOfRows(0);
  }

  @Test
  public void saveGameDialog_none_doesNothing() {
    assertThat(view.saveGameDialog()).isEmpty();
  }

  @Test
  public void loadGameDialog_none_doesNothing() {
    assertThat(view.loadGameDialog()).isEmpty();
  }

  @Test
  public void gameSetupDialog_none_doesNothing() {
    assertThat(view.gameSetupDialog(null, false)).isNull();
  }

  @Test
  public void promotionDialog_none_doesNothing() {
    assertThat(view.promotionDialog(null)).isNull();
  }

}
