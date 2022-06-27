package ch.teemoo.bobby.models.games;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;
import org.junit.jupiter.params.provider.EnumSource.Mode;

public class GameStateTest {

  @ParameterizedTest
  @EnumSource(value = GameState.class, mode = Mode.EXCLUDE, names = { "IN_PROGRESS", "LOSS" })
  void isDraw_drawState_returnTrue(GameState state) {
    assertThat(state.isDraw()).isTrue();
  }

  @ParameterizedTest
  @EnumSource(value = GameState.class, mode = Mode.INCLUDE, names = { "IN_PROGRESS", "LOSS" })
  void isDraw_notDrawState_returnFalse(GameState state) {
    assertThat(state.isDraw()).isFalse();
  }

  @ParameterizedTest
  @EnumSource(value = GameState.class, mode = Mode.INCLUDE, names = { "LOSS" })
  void isLost_lossState_returnTrue(GameState state) {
    assertThat(state.isLost()).isTrue();
  }

  @ParameterizedTest
  @EnumSource(value = GameState.class, mode = Mode.EXCLUDE, names = { "LOSS" })
  void isLost_notLossState_returnFalse(GameState state) {
    assertThat(state.isLost()).isFalse();
  }

  @ParameterizedTest
  @EnumSource(value = GameState.class, mode = Mode.INCLUDE, names = { "IN_PROGRESS" })
  void isInProgress_inProgressState_returnTrue(GameState state) {
    assertThat(state.isInProgress()).isTrue();
  }

  @ParameterizedTest
  @EnumSource(value = GameState.class, mode = Mode.EXCLUDE, names = { "IN_PROGRESS" })
  void isInProgress_notInProgressState_returnFalse(GameState state) {
    assertThat(state.isInProgress()).isFalse();
  }

}
