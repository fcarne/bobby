package ch.teemoo.bobby;

import static com.github.stefanbirkner.systemlambda.SystemLambda.assertNothingWrittenToSystemOut;
import static com.github.stefanbirkner.systemlambda.SystemLambda.tapSystemOut;
import static com.github.stefanbirkner.systemlambda.SystemLambda.tapSystemOutNormalized;
import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatRuntimeException;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyBoolean;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.anyList;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.atLeastOnce;
import static org.mockito.Mockito.atMostOnce;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

import ch.teemoo.bobby.gui.BoardView;
import ch.teemoo.bobby.gui.Square;
import ch.teemoo.bobby.helpers.BotFactory;
import ch.teemoo.bobby.helpers.GameFactory;
import ch.teemoo.bobby.models.Board;
import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.games.GameSetup;
import ch.teemoo.bobby.models.games.GameState;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.moves.PromotionMove;
import ch.teemoo.bobby.models.pieces.Bishop;
import ch.teemoo.bobby.models.pieces.Knight;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Queen;
import ch.teemoo.bobby.models.pieces.Rook;
import ch.teemoo.bobby.models.players.Human;
import ch.teemoo.bobby.models.players.Player;
import ch.teemoo.bobby.models.players.RandomBot;
import ch.teemoo.bobby.models.players.TraditionalBot;
import ch.teemoo.bobby.services.FileService;
import ch.teemoo.bobby.services.MoveService;
import ch.teemoo.bobby.services.PortableGameNotationService;
import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

@ExtendWith(MockitoExtension.class)
public class GameControllerTest {

  @Mock
  BoardView view;

  @Mock
  Game game;

  @Mock
  GameFactory gameFactory;

  @Mock
  BotFactory botFactory;

  @Mock
  Board board;

  @Mock
  MoveService moveService;

  @Mock
  FileService fileService;

  @Mock
  PortableGameNotationService pgnService;

  private GameController controller;

  @BeforeEach
  public void setup() {
    when(gameFactory.emptyGame()).thenReturn(new Game(null, null));
    when(gameFactory.createGame(any())).thenReturn(game);
    when(botFactory.getStrongestBot()).thenReturn(new TraditionalBot(0, null, moveService));
    when(game.getBoard()).thenReturn(board);
    controller = new GameController(view, gameFactory, botFactory, moveService, fileService,
        pgnService);
    controller.newGame(null, true, r -> {});
  }

  @Test
  public void init_newGameController_actionListener_set() {
    verify(view, times(2)).display(any(), anyBoolean());
    verify(view).setItemLoadActionListener(any());
    verify(view).setItemPrintToConsoleActionListener(any());
    verify(view).setItemSaveActionListener(any());
    verify(view).setItemSuggestMoveActionListener(any());
    verify(view).setItemUndoMoveActionListener(any());
  }

  @Test
  public void newGame_withSetup_dialogComesUp() {
    GameSetup gameSetup = new GameSetup(new Human("test1"), new Human("test2"));

    controller.newGame(gameSetup, true, gameResult -> {});

    verify(view, atMostOnce()).gameSetupDialog(any(), eq(true));
  }

  @Test
  public void refreshBoardView_normal_displayCalledWithFalse() {
    controller.refreshBoardView(board);
    verify(view, atLeastOnce()).display(any(), eq(false));
  }

  @Test
  public void refreshBoardView_reversed_displayCalledWithTrue() {
    when(game.getWhitePlayer()).thenReturn(new RandomBot(moveService));
    when(game.canBePlayed()).thenReturn(true);
    when(board.getBoard()).thenReturn(new Piece[][] {});

    controller.refreshBoardView(board);

    verify(view, atLeastOnce()).display(any(), eq(true));
  }

  @Test
  public void getAllowedMove_normal_returnMove() {
    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);
    Move computedMove = new Move(new Queen(Color.WHITE), move.getFromX(), move.getFromY(),
        move.getToX(), move.getToY());

    Move allowedMove = controller.getAllowedMove(move, null,
        Collections.singletonList(computedMove));

    assertThat(allowedMove).isEqualTo(computedMove);
  }

  @Test
  public void getAllowedMove_unauthorizedMove_throwRuntime() {
    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);
    assertThatRuntimeException()
        .isThrownBy(() -> controller.getAllowedMove(move, null, Collections.emptyList()))
        .withMessageContaining("Unauthorized move");
  }

  @Test
  public void getAllowedMove_ambiguousMove_throwRuntime() {
    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);
    Move computedMove1 = new Move(new Queen(Color.WHITE), move.getFromX(), move.getFromY(),
        move.getToX(), move.getToY());
    Move computedMove2 = new Move(new Queen(Color.WHITE), move.getFromX(), move.getFromY(),
        move.getToX(), move.getToY());

    assertThatRuntimeException().isThrownBy(
        () -> controller.getAllowedMove(move, null, Arrays.asList(computedMove1, computedMove2)))
        .withMessageContaining("Ambiguous move");
  }

  @Test
  public void getAllowedMove_humanPromotion_returnKnightPromotion() {
    Move move = new Move(new Pawn(Color.WHITE), 3, 6, 3, 7);
    Move computedMove = new Move(new Pawn(Color.WHITE), move.getFromX(), move.getFromY(),
        move.getToX(), move.getToY());
    PromotionMove computedMovePromotionQ = new PromotionMove(computedMove, new Queen(Color.WHITE));
    PromotionMove computedMovePromotionR = new PromotionMove(computedMove, new Rook(Color.WHITE));
    PromotionMove computedMovePromotionK = new PromotionMove(computedMove, new Knight(Color.WHITE));
    PromotionMove computedMovePromotionB = new PromotionMove(computedMove, new Bishop(Color.WHITE));
    Player player = new Human("Player 1");
    when(view.promotionDialog(any())).thenReturn(new Knight(Color.WHITE));

    Move allowedMove = controller.getAllowedMove(move, player, Arrays.asList(computedMovePromotionB,
        computedMovePromotionK, computedMovePromotionQ, computedMovePromotionR));

    assertThat(allowedMove).isInstanceOf(PromotionMove.class);
    assertThat(((PromotionMove) allowedMove).getPromotedPiece()).isInstanceOf(Knight.class);
    assertThat(allowedMove).isEqualTo(computedMovePromotionK);
  }

  @Test
  public void getAllowedMove_botPromotion_returnQueenPromotion() {
    Move move = new Move(new Pawn(Color.WHITE), 3, 6, 3, 7);
    Move computedMove = new Move(new Pawn(Color.WHITE), move.getFromX(), move.getFromY(),
        move.getToX(), move.getToY());
    PromotionMove computedMovePromotionQ = new PromotionMove(computedMove, new Queen(Color.WHITE));
    PromotionMove computedMovePromotionR = new PromotionMove(computedMove, new Rook(Color.WHITE));
    PromotionMove computedMovePromotionK = new PromotionMove(computedMove, new Knight(Color.WHITE));
    PromotionMove computedMovePromotionB = new PromotionMove(computedMove, new Bishop(Color.WHITE));
    Player player = new RandomBot(moveService);

    Move allowedMove = controller.getAllowedMove(move, player, Arrays.asList(computedMovePromotionB,
        computedMovePromotionK, computedMovePromotionQ, computedMovePromotionR));

    assertThat(allowedMove).isInstanceOf(PromotionMove.class);
    assertThat(((PromotionMove) allowedMove).getPromotedPiece()).isInstanceOf(Queen.class);
    assertThat(allowedMove).isEqualTo(computedMovePromotionQ);
    verify(view, never()).promotionDialog(any());
  }

  @Test
  public void getAllowedMove_promotionAlreadySet_returnKnightPromotion() {
    // given
    PromotionMove move = new PromotionMove(new Move(new Pawn(Color.WHITE), 3, 6, 3, 7),
        new Knight(Color.WHITE));
    Move computedMove = new Move(new Pawn(Color.WHITE), move.getFromX(), move.getFromY(),
        move.getToX(), move.getToY());
    PromotionMove computedMovePromotionQ = new PromotionMove(computedMove, new Queen(Color.WHITE));
    PromotionMove computedMovePromotionR = new PromotionMove(computedMove, new Rook(Color.WHITE));
    PromotionMove computedMovePromotionK = new PromotionMove(computedMove, new Knight(Color.WHITE));
    PromotionMove computedMovePromotionB = new PromotionMove(computedMove, new Bishop(Color.WHITE));
    Player player = new Human("Player 1");

    // when
    Move allowedMove = controller.getAllowedMove(move, player, Arrays.asList(computedMovePromotionB,
        computedMovePromotionK, computedMovePromotionQ, computedMovePromotionR));

    // then
    assertThat(allowedMove).isInstanceOf(PromotionMove.class);
    assertThat(((PromotionMove) allowedMove).getPromotedPiece()).isInstanceOf(Knight.class);
    assertThat(allowedMove).isEqualTo(computedMovePromotionK);
    verify(view, never()).promotionDialog(any());
  }

  @Test
  public void doMove_humanPlayer_moveDoneAndAddedToHistory() {
    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);
    Move computedMove = new Move(new Queen(Color.WHITE), move.getFromX(), move.getFromY(),
        move.getToX(), move.getToY());
    Player player = new Human("test");
    when(game.getWhitePlayer()).thenReturn(player);
    when(game.getPlayerByColor(eq(Color.WHITE))).thenReturn(player);
    when(moveService.getGameState(any(), any(), anyList())).thenReturn(GameState.IN_PROGRESS);
    when(moveService.computeMoves(any(), any(), anyInt(), anyInt(), anyList(), anyBoolean(),
        anyBoolean())).thenReturn(Collections.singletonList(computedMove));
    controller.doMove(move);
    verify(view).cleanSquaresBorder();
    verify(view).resetAllClickables();
    verify(board).doMove(eq(computedMove));
    verify(view).refresh(any());
    verify(view).addBorderToLastMoveSquares(eq(computedMove));
    verify(game).addMoveToHistory(eq(computedMove));
    verify(game).setToPlay(eq(Color.BLACK));
  }

  @Test
  public void doMove_unauthorizedBotMove_throwRuntime() {
    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);

    when(game.getPlayerByColor(eq(Color.WHITE))).thenReturn(new RandomBot(moveService));
    when(moveService.computeMoves(any(), any(), anyInt(), anyInt(), anyList(), anyBoolean(),
        anyBoolean())).thenReturn(Collections.emptyList());

    assertThatRuntimeException().isThrownBy(() -> controller.doMove(move))
        .withMessageContaining("Unauthorized move");
  }

  @Test
  public void undoLastMove_humanPlayer_moveUndoneAndRemovedFromHistory() {
    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);
    when(game.getPlayerByColor(eq(Color.WHITE))).thenReturn(new Human("test"));
    controller.undoLastMove(move);
    verify(view).cleanSquaresBorder();
    verify(view).resetAllClickables();
    verify(board).undoMove(eq(move));
    verify(view).refresh(any());
    verify(game).removeLastMoveFromHistory();
    verify(game).setToPlay(eq(Color.WHITE));
  }

  @Test
  public void undoLastMove_botPlayer_moveUndoneAndRemovedFromHistory() {
    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);
    when(game.getPlayerByColor(eq(Color.WHITE))).thenReturn(new RandomBot(moveService));
    controller.undoLastMove(move);
    verify(board).undoMove(eq(move));
    verify(view).refresh(any());
    verify(game).removeLastMoveFromHistory();
    verify(game).setToPlay(eq(Color.WHITE));
  }

  @Test
  public void displayGameInfo_inProgressNoCheck_noOutput() throws Exception {
    Player player = new Human("test");
    when(game.getWhitePlayer()).thenReturn(player);
    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);
    when(moveService.getGameState(any(), any(), any())).thenReturn(GameState.IN_PROGRESS);

    assertNothingWrittenToSystemOut(() -> {
      controller.displayGameInfo(move);
    });
  }

  @Test
  public void displayGameInfo_inProgressCheck_checkLogged() throws Exception {
    Player player = new RandomBot(moveService);
    when(game.getWhitePlayer()).thenReturn(player);
    when(game.getBlackPlayer()).thenReturn(player);

    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);
    move.setChecking(true);
    when(moveService.getGameState(any(), any(), any())).thenReturn(GameState.IN_PROGRESS);

    String text = tapSystemOut(() -> {
      controller.displayGameInfo(move);
    });
    assertThat(text).contains("Check!");
    verify(view, never()).popupInfo(anyString());
  }

  @Test
  public void displayGameInfo_drawThreefold_drawLogged() throws Exception {
    Player player = new Human("test");
    when(game.getWhitePlayer()).thenReturn(player);
    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);
    when(moveService.getGameState(any(), any(), any())).thenReturn(GameState.DRAW_THREEFOLD);
    when(game.getHistory()).thenReturn(Collections.emptyList());

    String text = tapSystemOut(() -> {
      controller.displayGameInfo(move);
    });

    assertThat(text).contains("1/2-1/2 (0 moves)").contains("Draw (threefold). The game is over.");
  }

  @Test
  public void displayGameInfo_draw50Moves_drawLogged() throws Exception {
    Player player = new Human("test");
    when(game.getWhitePlayer()).thenReturn(player);
    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);
    when(moveService.getGameState(any(), any(), any())).thenReturn(GameState.DRAW_50_MOVES);
    when(game.getHistory()).thenReturn(Collections.emptyList());

    String text = tapSystemOut(() -> {
      controller.displayGameInfo(move);
    });

    assertThat(text).contains("1/2-1/2 (0 moves)").contains("Draw (50 moves). The game is over.");
  }

  @Test
  public void displayGameInfo_drawStalemate_drawLogged() throws Exception {
    Player player = new Human("test");
    when(game.getWhitePlayer()).thenReturn(player);
    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);
    when(moveService.getGameState(any(), any(), any())).thenReturn(GameState.DRAW_STALEMATE);
    when(game.getHistory()).thenReturn(Collections.emptyList());

    String text = tapSystemOut(() -> {
      controller.displayGameInfo(move);
    });

    assertThat(text).contains("1/2-1/2 (0 moves)").contains("Draw (Stalemate). The game is over.");
  }

  @Test
  public void displayGameInfo_whiteBotWin_10Logged() throws Exception {
    Player player = new RandomBot(moveService);
    when(game.getWhitePlayer()).thenReturn(player);
    when(game.getBlackPlayer()).thenReturn(new Human("test"));
    Move move = new Move(new Queen(Color.WHITE), 3, 0, 3, 1);
    when(moveService.getGameState(any(), any(), any())).thenReturn(GameState.LOSS);
    when(game.getHistory()).thenReturn(Collections.emptyList());
    when(game.getPlayerByColor(eq(Color.WHITE))).thenReturn(player);
    String text = tapSystemOut(() -> {
      controller.displayGameInfo(move);
    });
    assertThat(text).contains("1-0 (0 moves)").contains("Checkmate!");
  }

  @Test
  public void displayGameInfo_blackHumanWin_01Logged() throws Exception {
    Player player = new Human("test");
    when(game.getWhitePlayer()).thenReturn(player);
    Move move = new Move(new Queen(Color.BLACK), 3, 0, 3, 1);
    when(moveService.getGameState(any(), any(), any())).thenReturn(GameState.LOSS);
    when(game.getHistory()).thenReturn(Collections.emptyList());
    when(game.getPlayerByColor(eq(Color.BLACK))).thenReturn(player);

    String text = tapSystemOut(() -> {
      controller.displayGameInfo(move);
    });
    assertThat(text).contains("0-1 (0 moves)").contains("Checkmated?!?");
  }

  @Test
  public void saveGame_saved_writeToFileCalled() throws Exception {
    File file = mock(File.class);
    when(view.saveGameDialog()).thenReturn(Optional.of(file));
    controller.saveGame();
    verify(fileService).writeGameToFileBasicNotation(any(), eq(file));
  }

  @Test
  public void saveGame_cancelled_writeToFileNotCalled() throws Exception {
    when(view.saveGameDialog()).thenReturn(Optional.empty());
    controller.saveGame();
    verify(fileService, never()).writeGameToFileBasicNotation(any(), any());
  }

  @Test
  public void saveGame_throwException_errorLogged() throws Exception {
    File file = mock(File.class);
    when(view.saveGameDialog()).thenReturn(Optional.of(file));
    doThrow(new IOException("Test exception")).when(fileService)
        .writeGameToFileBasicNotation(any(), any());

    String text = tapSystemOut(() -> {
      controller.saveGame();
    });
    assertThat(text).contains("An error happened: Test exception");
  }

  @Test
  public void loadGame_cancelled_readFileNotCalled() throws Exception {
    when(view.loadGameDialog()).thenReturn(Optional.empty());
    controller.loadGame();
    verify(fileService, never()).readFile(any());
  }

  @Test
  public void loadGame_basicNotation_moveDone() throws Exception {
    File file = File.createTempFile("test", ".txt");
    file.deleteOnExit();

    when(view.loadGameDialog()).thenReturn(Optional.of(file));
    when(fileService.readFile(any())).thenReturn(Collections.singletonList("e2-e4"));
    when(game.getWhitePlayer()).thenReturn(new Human("test"));
    when(game.getBlackPlayer()).thenReturn(new Human("test2"));

    Move move = new Move(new Pawn(Color.WHITE), 4, 1, 4, 3);

    when(moveService.computeMoves(any(), any(), anyInt(), anyInt(), anyList(), anyBoolean(),
        anyBoolean())).thenReturn(Collections.singletonList(move));
    when(moveService.getGameState(any(), any(), any())).thenReturn(GameState.IN_PROGRESS);

    controller.loadGame();

  }

  @Test
  public void loadGame_pgn() throws Exception {
    File file = File.createTempFile("test", ".pgn");
    file.deleteOnExit();
    when(view.loadGameDialog()).thenReturn(Optional.of(file));
    Game pgnGame = new Game(null, null);
    Move move = new Move(new Pawn(Color.WHITE), 4, 1, 4, 3);
    pgnGame.addMoveToHistory(move);
    when(pgnService.readPgnFile(any())).thenReturn(pgnGame);
    when(game.getWhitePlayer()).thenReturn(new Human("test"));
    when(game.getBlackPlayer()).thenReturn(new Human("test2"));
    when(moveService.computeMoves(any(), any(), anyInt(), anyInt(), anyList(), anyBoolean(),
        anyBoolean()))
        .thenReturn(Collections.singletonList(new Move(new Pawn(Color.WHITE), 4, 1, 4, 3)));
    when(moveService.getGameState(any(), any(), any())).thenReturn(GameState.IN_PROGRESS);

    controller.loadGame();

  }

  @Test
  public void loadGame_throwException_errorLogged() throws Exception {
    File file = File.createTempFile("test", ".txt");
    file.deleteOnExit();
    when(view.loadGameDialog()).thenReturn(Optional.of(file));
    doThrow(new IOException("Test exception")).when(fileService).readFile(any());

    String text = tapSystemOut(() -> {
      controller.loadGame();
    });

    assertThat(text).contains("An error happened: Test exception");
  }

  @Test
  public void printGameToConsole_none_boardLogged() throws Exception {
    String text = tapSystemOutNormalized(() -> {
      controller.printGameToConsole();
    });
    controller.printGameToConsole();
    assertThat(text).contains("Current board:");
  }

  @Test
  public void suggestMove_knightD8ToE6_moveLogged() throws Exception {
    Move move = new Move(new Knight(Color.BLACK), 3, 7, 4, 5);
    when(moveService.selectMove(any(), anyInt(), any())).thenReturn(move);
    String text = tapSystemOutNormalized(() -> {
      controller.suggestMove();
    });
    assertThat(text).contains(move.toString());
  }

  @Test
  public void undoLastMove_emptyHistory_undoNotCalled() {
    when(game.getHistory()).thenReturn(Collections.emptyList());
    controller.undoLastMove();
    verify(board, never()).undoMove(any());
  }

  @Test
  public void undoLastMove_withHistory_undoLastMove() {
    List<Move> moves = Arrays.asList(new Move(new Knight(Color.BLACK), 3, 7, 4, 5),
        new Move(new Knight(Color.WHITE), 3, 0, 4, 2));
    when(game.getHistory()).thenReturn(moves);
    when(game.getPlayerByColor(eq(Color.WHITE))).thenReturn(new Human("test"));
    controller.undoLastMove();
    verify(board, times(2)).undoMove(any());
  }

  @Test
  public void evaluateDrawProposal_accepted_stateIsDraw() {
    // given
    Player whitePlayer = new TraditionalBot(1, null, moveService);
    when(game.getPlayerWaiting()).thenReturn(whitePlayer);
    when(game.getWhitePlayer()).thenReturn(whitePlayer);
    when(game.getBlackPlayer()).thenReturn(new TraditionalBot(1, null, moveService));
    when(game.getState()).thenReturn(GameState.DRAW_AGREEMENT);
    when(moveService.isDrawAcceptable(any())).thenReturn(true);

    // when
    controller.evaluateDrawProposal();

    // then
    verify(game).setState(eq(GameState.DRAW_AGREEMENT));
  }

  @Test
  public void evaluateDrawProposal_declined_stateIsNotDraw() {
    // given
    Player whitePlayer = new TraditionalBot(1, null, moveService);
    when(game.getPlayerWaiting()).thenReturn(whitePlayer);
    when(moveService.isDrawAcceptable(any())).thenReturn(false);

    // when
    controller.evaluateDrawProposal();

    // then
    verify(game, never()).setState(eq(GameState.DRAW_AGREEMENT));
  }

  @Test
  public void evaluateDrawProposal_humanWaiting_loggedNotYourTurn() {
    when(game.getPlayerWaiting()).thenReturn(new Human("test"));

    controller.evaluateDrawProposal();

    verify(game, never()).setState(eq(GameState.DRAW_AGREEMENT));
  }

  @Test
  public void playNextMove_gameOver_nothingCalled() {
    when(moveService.getGameState(any(), any(), any())).thenReturn(GameState.LOSS);
    when(game.getPlayerToPlay()).thenReturn(new Human("test"));
    controller.playNextMove();
    verify(view, never()).refresh(any());
    verify(board, never()).doMove(any());
  }

  @Test
  public void playNextMove_humanToPlay_waitForHumanMove() {
    when(moveService.getGameState(any(), any(), any())).thenReturn(GameState.IN_PROGRESS);
    when(game.getPlayerToPlay()).thenReturn(new Human("test"));
    Square[][] squares = new Square[8][8];
    for (int i = 0; i < 8; i++) {
      for (int j = 0; j < 8; j++) {
        Square square = mock(Square.class);
        squares[i][j] = square;
      }
    }
    when(view.getSquares()).thenReturn(squares);
    controller.playNextMove();
    verify(view).resetAllClickables();
    verify(board, never()).doMove(any());
  }
}
