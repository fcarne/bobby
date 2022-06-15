package ch.teemoo.bobby.models.games;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;
import org.junit.jupiter.params.provider.EnumSource.Mode;

public class GameStateTest {

  @ParameterizedTest
  @EnumSource(value = GameState.class, mode = Mode.EXCLUDE, names = { "IN_PROGRESS", "LOSS" })
  public void isDraw_drawState_returnTrue(GameState state) {
    assertThat(state.isDraw()).isTrue();
  }

  @ParameterizedTest
  @EnumSource(value = GameState.class, mode = Mode.INCLUDE, names = { "IN_PROGRESS", "LOSS" })
  public void isDraw_notDrawState_returnFalse(GameState state) {
    assertThat(state.isDraw()).isFalse();
  }

  @ParameterizedTest
  @EnumSource(value = GameState.class, mode = Mode.INCLUDE, names = { "LOSS" })
  public void isLost_lossState_returnTrue(GameState state) {
    assertThat(state.isLost()).isTrue();
  }

  @ParameterizedTest
  @EnumSource(value = GameState.class, mode = Mode.EXCLUDE, names = { "LOSS" })
  public void isLost_notLossState_returnFalse(GameState state) {
    assertThat(state.isLost()).isFalse();
  }

  @ParameterizedTest
  @EnumSource(value = GameState.class, mode = Mode.INCLUDE, names = { "IN_PROGRESS" })
  public void isInProgress_inProgressState_returnTrue(GameState state) {
    assertThat(state.isInProgress()).isTrue();
  }

  @ParameterizedTest
  @EnumSource(value = GameState.class, mode = Mode.EXCLUDE, names = { "IN_PROGRESS" })
  public void isInProgress_notInProgressState_returnFalse(GameState state) {
    assertThat(state.isInProgress()).isFalse();
  }

}
