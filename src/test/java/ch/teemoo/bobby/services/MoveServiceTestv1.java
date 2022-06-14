package ch.teemoo.bobby.services;

import static ch.teemoo.bobby.helpers.ColorHelper.swap;
import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import ch.teemoo.bobby.models.Board;
import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.games.GameState;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.players.Human;
import ch.teemoo.bobby.models.players.RandomBot;

public class MoveServiceTestv1 {

    private MoveService moveService;

    @BeforeEach
	public void setup() {
        moveService = new MoveService();
    }

    @Test
    public void testSelectMoveCanCheckMate() {
        // Scenario: with a minimal depth, if a checkmate is possible, then it must be the selected move
        List<String> movesNotation = Arrays.asList(
                "e2-e3",
                "f7-f6",
                "f2-f4",
                "g7-g5"
        );
        Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
        Color colorToPlay = Color.WHITE;
        for (String notation: movesNotation) {
            Move move = Move.fromBasicNotation(notation, colorToPlay, game.getBoard());
            Piece piece = game.getBoard().getPiece(move.getFromX(), move.getFromY())
                    .orElseThrow(() -> new RuntimeException("Unexpected move, no piece at this location"));
            move = new Move(piece, move.getFromX(), move.getFromY(), move.getToX(), move.getToY());
            colorToPlay = swap(colorToPlay);
            game.getBoard().doMove(move);
            game.setToPlay(colorToPlay);
            game.addMoveToHistory(move);
        }
        Move bestMove = moveService.selectMove(game, 0, null);
        assertThat(bestMove.getBasicNotation()).isEqualTo("d1-h5+");

        game.getBoard().doMove(bestMove);
        game.addMoveToHistory(bestMove);
        assertThat(moveService.getGameState(game.getBoard(), swap(colorToPlay), game.getHistory())).isEqualTo(GameState.LOSS);
    }

    @Test
    public void testSelectMoveAvoidCheckMate() {
        // Scenario: with a depth of 1+, if the opponent can checkmate at next turn, then the selected move must avoid this, although the best move at first depth would be this one
        List<String> movesNotation = Arrays.asList(
                "e2-e3",
                "f7-f6",
                "f2-f4",
                "g7-g6",
                "d1-f3",
                "b8-c6",
                "f1-e2",
                "b7-b6",
                "f3-h5"
        );
        Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
        Color colorToPlay = Color.WHITE;
        for (String notation: movesNotation) {
            Move move = Move.fromBasicNotation(notation, colorToPlay, game.getBoard());
            Piece piece = game.getBoard().getPiece(move.getFromX(), move.getFromY())
                    .orElseThrow(() -> new RuntimeException("Unexpected move, no piece at this location"));
            move = new Move(piece, move.getFromX(), move.getFromY(), move.getToX(), move.getToY());
            colorToPlay = swap(colorToPlay);
            game.getBoard().doMove(move);
            game.addMoveToHistory(move);
            game.setToPlay(colorToPlay);
        }
        // At this stage, the best move with the minimal depth (0) is to take the queen, but doing this will lead to
        // being checkmated at next turn, so the best move for a larger depth (at least 1) is not to take the queen
        Move naiveBestMove = moveService.selectMove(game, 0, null);
        assertThat(naiveBestMove.getBasicNotation()).isEqualTo("g6xh5");

        Move bestMove = moveService.selectMove(game, 1, null);
        assertThat(bestMove.getBasicNotation()).isNotEqualTo("g6xh5");
        game.getBoard().doMove(bestMove);
        game.addMoveToHistory(bestMove);
        assertThat(moveService.getGameState(game.getBoard(), swap(colorToPlay), game.getHistory())).isNotEqualTo(GameState.LOSS);
    }

    @Test
    public void testGetGameStateInProgress() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝   ♜ \n" +
                "♟   ♟ ♟     ♕ ♟ \n" +
                "  ♟         ♟   \n" +
                "        ♟   ♘   \n" +
                "                \n" +
                "        ♙       \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖   ♗   ♔ ♗ ♘ ♖ \n"
        );
        assertThat(moveService.getGameState(board, Color.BLACK, Collections.emptyList())).isEqualTo(GameState.IN_PROGRESS);
    }

    @Test
    public void testGetGameStateLossCheckmate() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝   ♜ \n" +
                "♟   ♟ ♟   ♕   ♟ \n" +
                "  ♟         ♟   \n" +
                "        ♟   ♘   \n" +
                "                \n" +
                "        ♙       \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖   ♗   ♔ ♗ ♘ ♖ \n"
        );
        assertThat(moveService.getGameState(board, Color.BLACK, Collections.emptyList())).isEqualTo(GameState.LOSS);
    }

    @Test
    public void testGetGameStateDrawStalemate() {
        Board board = new Board("" +
                "        ♚       \n" +
                "            ♕   \n" +
                "                \n" +
                "♗           ♟   \n" +
                "        ♘   ♙ ♟ \n" +
                "        ♙     ♘ \n" +
                "♙ ♙ ♙         ♙ \n" +
                "♖       ♔ ♗   ♖ \n"
        );
        assertThat(moveService.getGameState(board, Color.BLACK, Collections.emptyList())).isEqualTo(GameState.DRAW_STALEMATE);
    }

    @Test
    public void testGetGameStateDraw50MovesNoCaptureNoPawn() {
        Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
        Board board = game.getBoard();
        List<Move> history = new ArrayList<>();
        for (int i = 0; i < 25; i++) {
            Move moveWhite;
            Move moveBlack;
            if (i % 4 == 0) {
                moveWhite = new Move(board.getPiece(1, 0).get(), 1, 0, 2, 2);
                moveBlack = new Move(board.getPiece(1, 7).get(), 1, 7, 2, 5);
            } else if (i % 4 == 1) {
                moveWhite = new Move(board.getPiece(2, 2).get(), 2, 2, 1, 0);
                moveBlack = new Move(board.getPiece(2, 5).get(), 2, 5, 1, 7);
            } else if (i % 4 == 2) {
                moveWhite = new Move(board.getPiece(1, 0).get(), 1, 0, 0, 2);
                moveBlack = new Move(board.getPiece(1, 7).get(), 1, 7, 0, 5);
            } else {
                moveWhite = new Move(board.getPiece(0, 2).get(), 0, 2, 1, 0);
                moveBlack = new Move(board.getPiece(0, 5).get(), 0, 5, 1, 7);
            }
            history.add(moveWhite);
            board.doMove(moveWhite);
            history.add(moveBlack);
            board.doMove(moveBlack);
        }
        assertThat(moveService.getGameState(board, Color.WHITE, history)).isEqualTo(GameState.DRAW_50_MOVES);
    }

    @Test
    public void testGetGameStateDrawThreefold() {
        Board board = new Board("" +
                "      ♚     ♕   \n" +
                "                \n" +
                "                \n" +
                "            ♟   \n" +
                "        ♘   ♙ ♟ \n" +
                "        ♙     ♘ \n" +
                "♙ ♙ ♙ ♗       ♙ \n" +
                "♖       ♔ ♗   ♖ \n"
        );
        List<String> movesBasicNotation = Arrays.asList(
                "e2-e3", "f7-f6", "f2-f4", "e7-e5", "f4xe5", "f6xe5", "d1-f3", "g8-f6", "b1-c3", "f6-e4", "c3xe4",
                "g7-g6", "e4-g5", "d7-d5", "f3xd5", "c7-c6", "d5xc6+", "c8-d7", "c6xb7", "f8-b4", "b7xa8", "e5-e4",
                "g5xe4", "b8-c6", "a8xc6", "b4-c5", "c6xc5", "d7-e6", "c5xa7", "d8xd2+", "c1xd2", "e6-h3", "g1xh3",
                "h7-h5", "a7-h7", "g6-g5", "h7xh8+", "e8-d7", "g2-g4", "h5-h4", "h8-g7+", "d7-d8", "g7-g8+", "d8-d7",
                "g8-g7+", "d7-d8", "g7-g8+", "d8-d7", "g8-g7+", "d7-d8", "g7-g8+");
        List<Move> history = new ArrayList<>(movesBasicNotation.size());
        Color color = Color.WHITE;
        Game game = new Game(null, null);
        for (String notation: movesBasicNotation) {
        	Move move = Move.fromBasicNotation(notation, color, game.getBoard());
        	game.getBoard().doMove(move);
        	history.add(move);
            color = swap(color);
        }
        assertThat(moveService.getGameState(board, Color.BLACK, history)).isEqualTo(GameState.DRAW_THREEFOLD);
    }

    @Test
    public void testIsDrawAcceptableWithInitialPositionsDeclinedForPenalty() {
        // given
        Game game = new Game(new Human("test"), new RandomBot(moveService));

        // when
        boolean isAcceptable = moveService.isDrawAcceptable(game);

        // then
        assertThat(isAcceptable).isFalse();
    }

}
