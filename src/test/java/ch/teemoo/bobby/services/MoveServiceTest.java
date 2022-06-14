package ch.teemoo.bobby.services;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatRuntimeException;
import static org.junit.jupiter.params.provider.Arguments.arguments;
import static org.mockito.Mockito.doReturn;
import static org.mockito.Mockito.spy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Stream;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.ValueSource;
import org.mockito.junit.jupiter.MockitoExtension;

import ch.teemoo.bobby.models.Board;
import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.MoveAnalysis;
import ch.teemoo.bobby.models.Position;
import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.games.GameState;
import ch.teemoo.bobby.models.moves.CastlingMove;
import ch.teemoo.bobby.models.moves.EnPassantMove;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.moves.PromotionMove;
import ch.teemoo.bobby.models.pieces.Bishop;
import ch.teemoo.bobby.models.pieces.King;
import ch.teemoo.bobby.models.pieces.Knight;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Queen;
import ch.teemoo.bobby.models.pieces.Rook;
import ch.teemoo.bobby.models.players.RandomBot;

@ExtendWith(MockitoExtension.class)
class MoveServiceTest {

	private MoveService moveService;

	@BeforeEach
	public void setup() {
		moveService = new MoveService();
	}
	
	private Move getMoveWithTookPiece(Piece piece, int fromX, int fromY, int toX, int toY, Piece tookPiece) {
        Move move = new Move(piece, fromX, fromY, toX, toY);
        move.setTookPiece(tookPiece);
		return move;
	}

	@Test
    public void generateCenteredHeatmap_none_returnCorrectMap() {
        int[][] heatmap = MoveService.generateCenteredHeatmap();
        
        assertThat(heatmap).hasDimensions(8, 8);

        int[][] expected = new int[][] {
                {0, 0, 0, 0, 0, 0, 0, 0},
                {0, 0, 0, 0, 0, 0, 0, 0},
                {0, 0, 1, 1, 1, 1, 0, 0},
                {0, 0, 1, 2, 2, 1, 0, 0},
                {0, 0, 1, 2, 2, 1, 0, 0},
                {0, 0, 1, 1, 1, 1, 0, 0},
                {0, 0, 0, 0, 0, 0, 0, 0},
                {0, 0, 0, 0, 0, 0, 0, 0},
        };
        
        assertThat(heatmap).isEqualTo(expected);
    }
	
	@Test
	public void isOutOfBounds_legalMove_returnFalse() {
		Move move = new Move(null, 0, 0, 0, 7);

		assertThat(moveService.isOutOfBounds(move)).isFalse();
	}

	@ParameterizedTest
	@CsvSource({ "-1,0", "0,-1", "0,8", "8,0" })
	public void isOutOfBounds_outOfBoundsMove_returnTrue(int toX, int toY) {
		Move move = new Move(null, 0, 0, toX, toY);

		assertThat(moveService.isOutOfBounds(move)).isTrue();
	}
	
    @Test
    public void getAllowedMove_outOfBounds_returnEmpty() {
        assertThat(moveService.getAllowedMove(null, 0, 7, 0, 1, null)).isEmpty();
    }

    @Test
    public void getAllowedMove_bishopCapturingQueen_returnTakingMove() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙   ♕   \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ \n"
        );
        
		Optional<Move> move = moveService.getAllowedMove(new Bishop(Color.BLACK), 2, 7, 4, -4, board);
		Optional<Move> move2 = moveService.getAllowedMove(new Bishop(Color.BLACK), 2, 7, 4, -4, board, true);
		assertThat(move).isPresent().get().hasFieldOrPropertyWithValue("tookPiece", board.getPiece(6, 3).get());
		assertThat(move).isEqualTo(move2);
    }

    @Test
    public void getAllowedMove_pawnMovingNoCapture_returnMove() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "                \n" +
                "      ♟ ♟       \n" +
                "        ♙   ♕   \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ \n"
        );
        
        Optional<Move> move = moveService.getAllowedMove(new Pawn(Color.BLACK), 3, 4, 0, -1, board);
        
        assertThat(move).isPresent();
    }

    @Test
    public void getAllowedMove_pawnBlockedByOwnPawn_returnEmpty() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "                \n" +
                "      ♟         \n" +
                "      ♟ ♙   ♕   \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ \n"
        );
        
        Optional<Move> move = moveService.getAllowedMove(new Pawn(Color.BLACK), 3, 4, 0, -1, board);
        assertThat(move).isEmpty();
    }

    @Test
    public void getAllowedMove_pawnCapturing_returnTakingMove() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "                \n" +
                "      ♟ ♟       \n" +
                "        ♙   ♕   \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ \n"
        );
        
        Optional<Move> move = moveService.getAllowedMove(new Pawn(Color.BLACK), 3, 4, 1, -1, board);
        
		assertThat(move).isPresent().get().hasFieldOrPropertyWithValue("tookPiece", board.getPiece(4, 3).get());
    }

    @Test
    public void getAllowedMove_pawnCapturingBlockedByOwnPawn_returnEmpty() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "                \n" +
                "      ♟         \n" +
                "        ♟   ♕   \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ \n"
        );
        
        Optional<Move> move = moveService.getAllowedMove(new Pawn(Color.BLACK), 3, 4, 1, -1, board);
        
        assertThat(move).isEmpty();
    }

    @Test
    public void getAllowedMove_pawnCapturingNothingToCapture_returnEmpty() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "                \n" +
                "      ♟         \n" +
                "            ♕   \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ \n"
        );
        
        Optional<Move> move = moveService.getAllowedMove(new Pawn(Color.BLACK), 3, 4, 1, -1, board);
        
        assertThat(move).isEmpty();
    }

    @Test
    public void getAllowedMove_bishopCapturingOwnPiece_returnEmpty() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" +
                "♟ ♟ ♟       ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙   ♟   \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ \n"
        );
        
        Optional<Move> move = moveService.getAllowedMove(new Bishop(Color.BLACK), 2, 7, 4, -4, board);
        
        assertThat(move).isEmpty();
    }
    
    @Test
    public void getAllowedMove_bishopMovingNoCapture_returnMove() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" +
                "♟ ♟ ♟       ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙   ♟   \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ \n"
        );
        
        Optional<Move> move = moveService.getAllowedMove(new Bishop(Color.BLACK), 2, 7, 3, -3, board);
        
        assertThat(move).isPresent();
    }
    
    @Test
    public void getAllowedMove_pawnCapturingCheckingFalse_returnNotTakingMove() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "                \n" +
                "      ♟ ♟       \n" +
                "        ♙   ♕   \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ \n"
        );
        
        Optional<Move> move = moveService.getAllowedMove(new Pawn(Color.BLACK), 3, 4, 1, -1, board, false);
        
		assertThat(move).isPresent();
		assertThat(move.get().isTaking()).isFalse();
    }
    
    @Test
    public void computeStraightMoves_freeSpace_returnMovesUpToBorder() {
        Board board = new Board("" +
                "                \n" +
                "                \n" +
                "                \n" +
                "      ♖         \n" +
                "                \n" +
                "                \n" +
                "                \n" +
                "                \n"
        );
        Piece rook = board.getPiece(3, 4).get();
        List<Move> moves = moveService.computeStraightMoves(rook, 3, 4, board);
        assertThat(moves).containsExactlyInAnyOrder(
                // up
                new Move(rook, 3, 4, 3, 5),
                new Move(rook, 3, 4, 3, 6),
                new Move(rook, 3, 4, 3, 7),
                //down
                new Move(rook, 3, 4, 3, 3),
                new Move(rook, 3, 4, 3, 2),
                new Move(rook, 3, 4, 3, 1),
                new Move(rook, 3, 4, 3, 0),
                // left
                new Move(rook, 3, 4, 2, 4),
                new Move(rook, 3, 4, 1, 4),
                new Move(rook, 3, 4, 0, 4),
                // right
                new Move(rook, 3, 4, 4, 4),
                new Move(rook, 3, 4, 5, 4),
                new Move(rook, 3, 4, 6, 4),
                new Move(rook, 3, 4, 7, 4)
        );
        
        assertThat(moves).isEqualTo(moveService.computeStraightMoves(rook, 3, 4, board, Board.SIZE));
    }

    @Test
    public void computeStraightMoves_withOpponentPieces_returnMovesLimitedToTaking() {
        Board board = new Board("" +
                "                \n" +
                "      ♟         \n" +
                "                \n" +
                "    ♟ ♖ ♟       \n" +
                "                \n" +
                "                \n" +
                "      ♟         \n" +
                "                \n"
        );
        Piece rook = board.getPiece(3, 4).get();
        List<Move> moves = moveService.computeStraightMoves(rook, 3, 4, board);
        assertThat(moves).containsExactlyInAnyOrder(
                // up
                new Move(rook, 3, 4, 3, 5),
                getMoveWithTookPiece(rook, 3, 4, 3, 6, board.getPiece(3, 6).get()),
                //down
                new Move(rook, 3, 4, 3, 3),
                new Move(rook, 3, 4, 3, 2),
                getMoveWithTookPiece(rook, 3, 4, 3, 1, board.getPiece(3, 1).get()),
                // left
                getMoveWithTookPiece(rook, 3, 4, 2, 4, board.getPiece(2, 4).get()),
                // right
                getMoveWithTookPiece(rook, 3, 4, 4, 4, board.getPiece(4, 4).get())
        );
    }

    @Test
    public void computeStraightMoves_withOwnPieces_returnMovesLimitedByPieces() {
    	Board board = new Board("" +
    			"                \n" +
    			"      ♙         \n" +
    			"                \n" +
    			"    ♙ ♖ ♙       \n" +
    			"                \n" +
    			"                \n" +
    			"      ♙         \n" +
    			"                \n"
    			);
    	Piece rook = board.getPiece(3, 4).get();
    	List<Move> moves = moveService.computeStraightMoves(rook, 3, 4, board);
    	assertThat(moves).containsExactlyInAnyOrder(
    			// up
    			new Move(rook, 3, 4, 3, 5),
    			//down
    			new Move(rook, 3, 4, 3, 3),
    			new Move(rook, 3, 4, 3, 2)
    			// left
    			// right
    			);
    }
    

    @Test
    public void computeDiagonalMoves_freeSpace_returnMovesUpToBorder() {
        Board board = new Board("" +
                "                \n" +
                "                \n" +
                "                \n" +
                "      ♗         \n" +
                "                \n" +
                "                \n" +
                "                \n" +
                "                \n"
        );
        Piece bishop = board.getPiece(3, 4).get();
        List<Move> moves = moveService.computeDiagonalMoves(bishop, 3, 4, board);
        assertThat(moves).containsExactlyInAnyOrder(
                // up-right
                new Move(bishop, 3, 4, 4, 5),
                new Move(bishop, 3, 4, 5, 6),
                new Move(bishop, 3, 4, 6, 7),
                // up-left
                new Move(bishop, 3, 4, 2, 5),
                new Move(bishop, 3, 4, 1, 6),
                new Move(bishop, 3, 4, 0, 7),
                // down-right
                new Move(bishop, 3, 4, 4, 3),
                new Move(bishop, 3, 4, 5, 2),
                new Move(bishop, 3, 4, 6, 1),
                new Move(bishop, 3, 4, 7, 0),
                // down-left
                new Move(bishop, 3, 4, 2, 3),
                new Move(bishop, 3, 4, 1, 2),
                new Move(bishop, 3, 4, 0, 1)
        );
        assertThat(moves).isEqualTo(moveService.computeDiagonalMoves(bishop, 3, 4, board, Board.SIZE));
    }

    @Test
    public void computeDiagonalMoves_withOpponentPieces_returnMovesLimitedToTaking() {
        Board board = new Board("" +
                "                \n" +
                "  ♟             \n" +
                "        ♟       \n" +
                "      ♗         \n" +
                "    ♟           \n" +
                "          ♟     \n" +
                "                \n" +
                "                \n"
        );
        Piece bishop = board.getPiece(3, 4).get();
        List<Move> moves = moveService.computeDiagonalMoves(bishop, 3, 4, board);
        assertThat(moves).containsExactlyInAnyOrder(
                // up-right
                getMoveWithTookPiece(bishop, 3, 4, 4, 5, board.getPiece(4, 5).get()),
                // up-left
                new Move(bishop, 3, 4, 2, 5),
                getMoveWithTookPiece(bishop, 3, 4, 1, 6, board.getPiece(1, 6).get()),
                // down-right
                new Move(bishop, 3, 4, 4, 3),
                getMoveWithTookPiece(bishop, 3, 4, 5, 2, board.getPiece(5, 2).get()),
                // down-left
                getMoveWithTookPiece(bishop, 3, 4, 2, 3, board.getPiece(2, 3).get())
        );
    }

    @Test
    public void computeDiagonalMoves_withOpponentPieces_returnMovesUpToBorder() {
    	Board board = new Board("" +
    			"                \n" +
    			"  ♙             \n" +
    			"        ♙       \n" +
    			"      ♗         \n" +
    			"    ♙           \n" +
    			"          ♙     \n" +
    			"                \n" +
    			"                \n"
    			);
    	Piece bishop = board.getPiece(3, 4).get();
    	List<Move> moves = moveService.computeDiagonalMoves(bishop, 3, 4, board);
    	assertThat(moves).containsExactlyInAnyOrder(
    			// up-right
    			// up-left
    			new Move(bishop, 3, 4, 2, 5),
    			// down-right
    			new Move(bishop, 3, 4, 4, 3)
    			// down-left
    			);
    }

    @Test
    public void computeLShapeMoves_freeSpace_return8Moves() {
        Board board = new Board("" +
                "                \n" +
                "                \n" +
                "                \n" +
                "      ♘         \n" +
                "                \n" +
                "                \n" +
                "                \n" +
                "                \n"
        );
        Piece knight = board.getPiece(3, 4).get();
        List<Move> moves = moveService.computeLShapeMoves(knight, 3, 4, board);
        assertThat(moves).containsExactlyInAnyOrder(
                new Move(knight, 3, 4, 4, 6),
                new Move(knight, 3, 4, 5, 5),
                new Move(knight, 3, 4, 4, 2),
                new Move(knight, 3, 4, 1, 5),
                new Move(knight, 3, 4, 2, 6),
                new Move(knight, 3, 4, 5, 3),
                new Move(knight, 3, 4, 2, 2),
                new Move(knight, 3, 4, 1, 3)
        );
    }

    @Test
    public void computeLShapeMoves_withPieces_return5PossibleMoves() {
        Board board = new Board("" +
                "                \n" +
                "    ♟   ♟       \n" +
                "  ♙       ♟     \n" +
                "      ♘         \n" +
                "  ♙       ♟     \n" +
                "    ♙   ♟       \n" +
                "                \n" +
                "                \n"
        );
        Piece knight = board.getPiece(3, 4).get();
        List<Move> moves = moveService.computeLShapeMoves(knight, 3, 4, board);
        assertThat(moves).containsExactlyInAnyOrder(
                getMoveWithTookPiece(knight, 3, 4, 4, 6, board.getPiece(4, 6).get()),
                getMoveWithTookPiece(knight, 3, 4, 5, 5, board.getPiece(5, 5).get()),
                getMoveWithTookPiece(knight, 3, 4, 4, 2, board.getPiece(4, 2).get()),
                getMoveWithTookPiece(knight, 3, 4, 2, 6, board.getPiece(2, 6).get()),
                getMoveWithTookPiece(knight, 3, 4, 5, 3, board.getPiece(5, 3).get())
        );
    }
    
    @Test
    public void computePawnMoves_freeSpace_returnAllPossibleMoves() {
        Board board = new Board("" +
                "                \n" +
                "                \n" +
                "    ♟   ♟       \n" +
                "      ♙         \n" +
                "                \n" +
                "  ♟             \n" +
                "♙               \n" +
                "                \n"
        );
        Piece pawn = board.getPiece(3, 4).get();
        List<Move> moves = moveService.computePawnMoves(pawn, 3, 4, board, Collections.emptyList(), false);
        assertThat(moves).containsExactlyInAnyOrder(
                new Move(pawn, 3, 4, 3, 5),
                getMoveWithTookPiece(pawn, 3, 4, 2, 5, board.getPiece(2, 5).get()),
                getMoveWithTookPiece(pawn, 3, 4, 4, 5, board.getPiece(4, 5).get())
        );

        Piece pawnAtStart = board.getPiece(0, 1).get();
        moves = moveService.computePawnMoves(pawnAtStart, 0, 1, board, Collections.emptyList(), false);
        assertThat(moves).containsExactlyInAnyOrder(
                new Move(pawnAtStart, 0, 1, 0, 2),
                new Move(pawnAtStart, 0, 1, 0, 3),
                getMoveWithTookPiece(pawnAtStart, 0, 1, 1, 2, board.getPiece(1, 2).get())
        );
        
        List<Move> takingOnly = moveService.computePawnMoves(pawnAtStart, 0, 1, board, Collections.emptyList(), true);
        assertThat(takingOnly).containsOnly(new Move(pawnAtStart, 0,1,1,2));
    }

    @Test
    public void computePawnMoves_withPieces_returnOnlyAllowedMoves() {
        Board board = new Board("" +
                "                \n" +
                "                \n" +
                "    ♙ ♟ ♟       \n" +
                "      ♙         \n" +
                "                \n" +
                "♙               \n" +
                "♙               \n" +
                "                \n"
        );
        Piece pawn = board.getPiece(3, 4).get();
        List<Move> moves = moveService.computePawnMoves(pawn, 3, 4, board, Collections.emptyList(), false);
        assertThat(moves).containsExactlyInAnyOrder(getMoveWithTookPiece(pawn, 3, 4, 4, 5, board.getPiece(4, 5).get()));

        Piece pawnAtStart = board.getPiece(0, 1).get();
        moves = moveService.computePawnMoves(pawnAtStart, 0, 1, board, Collections.emptyList(), false);
        assertThat(moves).isEmpty();

        Piece blackPawn = board.getPiece(4, 5).get();
        moves = moveService.computePawnMoves(blackPawn, 4, 5, board, Collections.emptyList(), false);
        assertThat(moves).containsExactlyInAnyOrder(new Move(blackPawn, 4, 5, 4, 4), getMoveWithTookPiece(blackPawn, 4, 5, 3, 4, board.getPiece(3, 4).get()));
    }

    @Test
    public void computePawnMoves_enPassantPossible_returnEnPassantMove() {
        Board board = new Board("" +
            "                \n" +
            "                \n" +
            "                \n" +
            "      ♙ ♟       \n" +
            "                \n" +
            "                \n" +
            "                \n" +
            "                \n"
        );
        Piece blackPawn = board.getPiece(4, 4).get();
        Move lastMove = new Move(blackPawn, 4, 6, 4, 4);
        List<Move> history = Collections.singletonList(lastMove);
        Piece pawn = board.getPiece(3, 4).get();
        List<Move> moves = moveService.computePawnMoves(pawn, 3, 4, board, history, false);
        Move move = new Move(pawn, 3, 4, 4, 5);
        move.setTookPiece(blackPawn);
        EnPassantMove enPassantMove = new EnPassantMove(move, 4, 4);
        assertThat(moves).containsExactlyInAnyOrder(new Move(pawn, 3, 4, 3, 5), enPassantMove);
    }

    @ParameterizedTest
    @MethodSource
    public void computePawnMoves_enPassantNotPossible_returnNonEnPassantMoves(Move lastMove) {
    	Board board = new Board("" +
    			"                \n" +
    			"                \n" +
    			"                \n" +
    			"      ♙ ♟       \n" +
    			"                \n" +
    			"                \n" +
    			"                \n" +
    			"                \n"
    			);
    	List<Move> history = Collections.singletonList(lastMove);
    	
    	Piece pawn = board.getPiece(3, 4).get();
    	List<Move> moves = moveService.computePawnMoves(pawn, 3, 4, board, history, false);
    	
    	assertThat(moves).containsOnly(new Move(pawn, 3, 4, 3, 5));
    }
    
    private static Stream<Arguments> computePawnMoves_enPassantNotPossible_returnNonEnPassantMoves() {
    	return Stream.of(
    			arguments(new Move(new Pawn(Color.BLACK),4,5,4,4)),
    			arguments(new Move(new Pawn(Color.BLACK),3,6,3,4)),
    			arguments(new Move(new Pawn(Color.BLACK),4,7,4,5)),
    			arguments(new Move(new Rook(Color.BLACK),4,6,4,4))
    	);
    }
    
    @Test
    public void computePawnMoves_promotionPossible_returnAllPromotions() {
        Board board = new Board("" +
            "                \n" +
            "        ♙       \n" +
            "                \n" +
            "                \n" +
            "                \n" +
            "                \n" +
            "                \n" +
            "                \n"
        );
        Piece pawn = board.getPiece(4, 6).get();
        List<Move> moves = moveService.computePawnMoves(pawn, 4, 6, board, Collections.emptyList(), false);
        Move move = new Move(pawn, 4, 6, 4, 7);
        assertThat(moves).containsExactlyInAnyOrder(
        		new PromotionMove(move, new Queen(Color.WHITE)),
        		new PromotionMove(move, new Bishop(Color.WHITE)),
        		new PromotionMove(move, new Knight(Color.WHITE)),
        		new PromotionMove(move, new Rook(Color.WHITE))
        );
    }
    
    @Test
    public void isInPawnCheck_check_returnTrue() {
        Board board = new Board("" +
                "♜ ♞     ♚     ♜ \n" +
                "♟ ♟ ♝ ♕   ♙   ♟ \n" +
                "                \n" +
                "        ♘       \n" +
                "  ♝   ♕ ♙ ♟     \n" +
                "        ♔        \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖   ♗     ♗   ♖ \n"
        );
        assertThat(moveService.isInPawnCheck(board, new Position(4, 7), Color.BLACK)).isTrue();
        assertThat(moveService.isInPawnCheck(board, new Position(4, 2), Color.WHITE)).isTrue();
    }

    @Test
    public void isInPawnCheck_noCheck_returnFalse() {
        Board board = new Board("" +
                "♔               \n" +
                "                \n" +
                "                \n" +
                "        ♘      ♚\n" +
                "♔       ♙ ♛     \n" +
                "♝               \n" +
                "  ♙         ♙ ♙ \n" +
                "♖   ♗ ♕ ♔ ♗ ♚ ♖ \n"
        );
        assertThat(moveService.isInPawnCheck(board, new Position(0, 7), Color.WHITE)).isFalse();
        assertThat(moveService.isInPawnCheck(board, new Position(7, 4), Color.BLACK)).isFalse();
        assertThat(moveService.isInPawnCheck(board, new Position(0, 3), Color.WHITE)).isFalse();
        assertThat(moveService.isInPawnCheck(board, new Position(6, 0), Color.BLACK)).isFalse();
        assertThat(moveService.isInPawnCheck(board, new Position(4, 0), Color.WHITE)).isFalse();
    }

    @Test
    public void isInLCheck_blackKingCheck_returnTrue() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟   ♟ \n" +
                "          ♘ ♟   \n" +
                "        ♘       \n" +
                "  ♝     ♙       \n" +
                "                \n" +
                "♙ ♙ ♙ ♙   ♙ ♙ ♙ \n" +
                "♖   ♗ ♕ ♔ ♗   ♖ \n"
        );
        assertThat(moveService.isInLCheck(board, new Position(4, 7), Color.BLACK)).isTrue();
    }

    @Test
    public void isInLCheck_noCheck_returnFalse() {
        Board board = new Board("" +
                "♜ ♞ ♝   ♚     ♜ \n" +
                "♟ ♟ ♟     ♟   ♟ \n" +
                "          ♛ ♟   \n" +
                "        ♘       \n" +
                "  ♝     ♙       \n" +
                "                \n" +
                "♙ ♙ ♙ ♙   ♙ ♙ ♙ \n" +
                "♖   ♗ ♕ ♔ ♗   ♖ \n"
        );
        assertThat(moveService.isInDiagonalCheck(board, new Position(4, 7), Color.BLACK)).isFalse();
        assertThat(moveService.isInLCheck(board, new Position(4, 0), Color.WHITE)).isFalse();

    }

    @Test
    public void isInDiagonalCheck_checkBothQueenAndBishop_returnTrue() {
        Board board = new Board("" +
                "♜ ♞ ♝   ♚ ♝     \n" +
                "♟ ♟ ♟     ♘   ♟ \n" +
                "      ♟         \n" +
                "  ♗     ♕   ♟   \n" +
                "  ♛ ♙ ♙ ♙   ♞   \n" +
                "♙               \n" +
                "  ♙       ♙ ♙ ♙ \n" +
                "♖ ♘ ♗   ♔     ♖ "
        );
        assertThat(moveService.isInDiagonalCheck(board, new Position(4, 7), Color.BLACK)).isTrue();
        assertThat(moveService.isInDiagonalCheck(board, new Position(4, 0), Color.WHITE)).isTrue();
    }

    @Test
    public void isInDiagonalCheck_noCheck_returnFalse() {
        Board board = new Board("" +
                "♜ ♞ ♝   ♚ ♝     \n" +
                "♟ ♟ ♟ ♟ ♛ ♟   ♟ \n" +
                "                \n" +
                "        ♕   ♟   \n" +
                "      ♙ ♙   ♞   \n" +
                "    ♙           \n" +
                "♙ ♙       ♙ ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ "
        );
        assertThat(moveService.isInDiagonalCheck(board, new Position(4, 7), Color.BLACK)).isFalse();
        assertThat(moveService.isInDiagonalCheck(board, new Position(4, 0), Color.WHITE)).isFalse();
    }

    @Test
    public void isInStraightCheck_verticalCheckByQueen_returnsTrue() {
        // Vertically
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚     ♜ \n" +
                "♟ ♟ ♟ ♟   ♟ ♟ ♟ \n" +
                "          ♞     \n" +
                "        ♕       \n" +
                "        ♙       \n" +
                "                \n" +
                "♙ ♙ ♙ ♙   ♙ ♙ ♙ \n" +
                "♖ ♘ ♗   ♔   ♗ ♖ "
        );
        assertThat(moveService.isInStraightCheck(board, new Position(4, 7), Color.BLACK)).isTrue();
    }

    @Test
    public void isInStraightCheck_orizontalCheckByRock_returnsTrue() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚     ♖ \n" +
                "♟ ♟ ♟ ♟ ♙ ♟   ♟ \n" +
                "            ♝   \n" +
                "            ♟   \n" +
                "      ♙     ♞   \n" +
                "    ♙           \n" +
                "♙ ♙       ♙ ♙ ♙ \n" +
                "♖ ♘ ♗ ♕ ♔ ♗ ♘   "
        );
        assertThat(moveService.isInStraightCheck(board, new Position(4, 7), Color.BLACK)).isTrue();
    }

    @Test
    public void isInStraightCheck_noCheck_returnsFalse() {
        Board board = new Board("" +
                "♜ ♞ ♝   ♚ ♝     \n" +
                "♟ ♟ ♟ ♟ ♛ ♟   ♟ \n" +
                "                \n" +
                "        ♕   ♟   \n" +
                "      ♙ ♙   ♞   \n" +
                "    ♙           \n" +
                "♙ ♙       ♙ ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ "
        );
        assertThat(moveService.isInStraightCheck(board, new Position(4, 7), Color.BLACK)).isFalse();
    }
    
    @Test
    public void findKingPosition_initialBoard_returnStartingPositions() {
        // Initial positions board
        Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
        
        Optional<Position> whiteKingPosition = moveService.findKingPosition(game.getBoard(), Color.WHITE);
        Optional<Position> blackKingPosition = moveService.findKingPosition(game.getBoard(), Color.BLACK);
        
        assertThat(whiteKingPosition).isPresent().get().hasFieldOrPropertyWithValue("file", 4).hasFieldOrPropertyWithValue("rank", 0);
        assertThat(blackKingPosition).isPresent().get().hasFieldOrPropertyWithValue("file", 4).hasFieldOrPropertyWithValue("rank", 7);
    }

    @Test
    public void findKingPosition_emptyBoard_returnEmptyPositions() {
        // Empty board
        Board emptyBoard = new Board(new Piece[8][8]);

        Optional<Position> whiteKingPosition = moveService.findKingPosition(emptyBoard, Color.WHITE);
        Optional<Position> blackKingPosition = moveService.findKingPosition(emptyBoard, Color.BLACK);

        
        assertThat(whiteKingPosition).isEmpty();
        assertThat(blackKingPosition).isEmpty();
    }

    @ParameterizedTest
    @ValueSource(strings = {
    		"♜ ♞ ♝ ♛ ♚     ♜ \n" +
            "♟ ♟ ♟     ♟   ♟ \n" +
            "          ♘ ♟   \n" +
            "        ♘       \n" +
            "  ♝     ♙       \n" +
            "                \n" +
            "♙ ♙ ♙ ♙   ♙ ♙ ♙ \n" +
            "♖   ♗ ♕ ♔ ♗   ♖ \n",

    		"♜ ♞ ♝ ♛ ♚     ♜ \n" +
            "♟ ♟ ♟     ♟   ♟ \n" +
            "    ♗       ♟   \n" +
            "        ♘       \n" +
            "  ♝     ♙       \n" +
            "                \n" +
            "♙ ♙ ♙ ♙ ♘ ♙ ♙ ♙ \n" +
            "♖     ♕ ♔ ♗   ♖ \n",
            
    		"♜ ♞ ♝ ♛ ♚     ♖ \n" +
            "♟ ♟ ♟     ♟   ♜ \n" +
            "            ♟ ♟ \n" +
            "        ♘       \n" +
            "  ♝     ♙       \n" +
            "                \n" +
            "♙ ♙ ♙ ♙   ♙ ♙ ♙ \n" +
            "♖   ♗ ♕ ♔ ♗     \n",

            "♜ ♞ ♝ ♛ ♚       \n" +
    		"♟ ♟ ♟     ♙   ♜ \n" +
    		"            ♟ ♟ \n" +
    		"        ♘       \n" +
    		"  ♝     ♙       \n" +
    		"                \n" +
    		"♙ ♙ ♙ ♙     ♙ ♙ \n" +
    		"♖   ♗ ♕ ♔ ♗     \n"
    })
	public void isInCheck_blackKingCheck_returnTrue(String boardString) {
		Board board = new Board(boardString);
		assertThat(moveService.isInCheck(board, Color.BLACK)).isTrue();
	}

	@Test
	public void isInCheck_noCheck_returnFalse() {
		Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
		assertThat(moveService.isInCheck(game.getBoard(), Color.BLACK)).isFalse();
	}

	@Test
	public void isInCheck_noKing_throwRuntime() {
		// Empty board
		Board emptyBoard = new Board(new Piece[8][8]);
		assertThatRuntimeException().isThrownBy(() -> moveService.isInCheck(emptyBoard, Color.WHITE))
				.withMessage("King not found");
	}
	
	@Test
    public void isValidSituation_valid_returnTrue() {
        Board board = new Board("" +
                "♜ ♞       ♚   ♜ \n" +
                "♟ ♟   ♝   ♙   ♟ \n" +
                "    ♙           \n" +
                "        ♘       \n" +
                "        ♙ ♛     \n" +
                "♖               \n" +
                "  ♙   ♟     ♙ ♙ \n" +
                "    ♗ ♕ ♔ ♗   ♖ \n"
        );
        assertThat(moveService.isValidSituation(board, Color.BLACK)).isTrue();
    }
	
	@Test
    public void isValidSituation_missingKings_returnFalse() {
        Board board = new Board("" +
                "♜ ♞       ♚   ♜ \n" +
                "♟ ♟   ♝   ♙   ♟ \n" +
                "    ♙           \n" +
                "        ♘       \n" +
                "        ♙ ♛     \n" +
                "♝               \n" +
                "  ♙   ♟     ♙ ♙ \n" +
                "♖   ♗ ♕   ♗   ♖ \n"
        );
        
        assertThat(moveService.isValidSituation(board, Color.WHITE)).isFalse();
        assertThat(moveService.isValidSituation(board, Color.BLACK)).isFalse();
    }

    @Test
    public void isValidSituation_kingsDistanceTooSmall_returnFalse() {
        Board board = new Board("" +
                "♜ ♞     ♔ ♚   ♜ \n" +
                "♟ ♟   ♝   ♙   ♟ \n" +
                "    ♙           \n" +
                "        ♘       \n" +
                "        ♙ ♛     \n" +
                "♝               \n" +
                "  ♙   ♟     ♙ ♙ \n" +
                "♖   ♗ ♕   ♗   ♖ \n"
        );
        assertThat(moveService.isValidSituation(board, Color.WHITE)).isFalse();
        assertThat(moveService.isValidSituation(board, Color.BLACK)).isFalse();
    }

    @Test
    public void isValidSituation_inCheckAfterMyMove_returnFalse() {
        Board board = new Board("" +
                "♜ ♞       ♚   ♜ \n" +
                "♟ ♟   ♝   ♙   ♟ \n" +
                "    ♙           \n" +
                "        ♘       \n" +
                "        ♙ ♛     \n" +
                "♖               \n" +
                "  ♙   ♟     ♙ ♙ \n" +
                "    ♗ ♕ ♔ ♗   ♖ \n"
        );
        assertThat(moveService.isValidSituation(board, Color.WHITE)).isFalse();
    }
    
    @Test
    public void getCastlingMove_ok_returnCastlingMove() {
        Board board = new Board("" +
                "♜ ♞   ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙       \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖       ♔ ♗ ♘ ♖ \n"
        );

		List<Move> history = Arrays.asList(new Move(new Pawn(Color.WHITE), 4, 1, 4, 3),
				new Move(new Pawn(Color.WHITE), 0, 1, 0, 3));
        
        Piece whiteKing = board.getPiece(4, 0).get();
        
        assertThat(moveService.getCastlingMove(board, whiteKing, 4, 0, 2, 0, 3, history)).isPresent().get().isInstanceOf(
            CastlingMove.class);
        Piece blackKing = board.getPiece(4, 7).get();
        assertThat(moveService.getCastlingMove(board, blackKing, 4, 7, 6, 7, 5, history)).isPresent().get().isInstanceOf(CastlingMove.class);
    }

    @ParameterizedTest
    @ValueSource(strings = {
    		"♜ ♞   ♛ ♚     ♜ \n" +
            "♟ ♟ ♟     ♟ ♟ ♟ \n" +
            "      ♟         \n" +
            "        ♟       \n" +
            "        ♙       \n" +
            "          ♙     \n" +
            "♙ ♙ ♙ ♙     ♙ ♙ \n" +
            "        ♔ ♗ ♘ ♖ \n",
            
            "♜ ♞   ♛ ♚     ♜ \n" +
            "♟ ♟ ♟     ♟ ♟ ♟ \n" +
            "      ♟         \n" +
            "        ♟       \n" +
            "        ♙       \n" +
            "          ♙     \n" +
            "♙ ♙ ♙ ♙     ♙ ♙ \n" +
            "♗       ♔   ♘ ♖ \n",
            
            "  ♞   ♛ ♚     ♜ \n" +
            "♟ ♟ ♟     ♟ ♟ ♟ \n" +
            "      ♟         \n" +
            "        ♟       \n" +
            "        ♙       \n" +
            "          ♙     \n" +
            "♙ ♙ ♙ ♙     ♙ ♙ \n" +
            "♜       ♔ ♗ ♘ ♖ \n"
    })
    public void getCastlingMove_whiteRookNotPresent_returnEmpty(String boardString) {
        Board board = new Board(boardString);
        Piece king = board.getPiece(4, 0).get();
        assertThat(moveService.getCastlingMove(board, king, 4, 0, 2, 0, 3, Collections.emptyList())).isEmpty();
    }

    @Test
    public void getCastlingMove_pieceBetweenRookAndKing_returnEmpty() {
        Board board = new Board("" +
                "♜ ♞   ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙       \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖     ♗ ♔   ♘ ♖ \n"
        );
        Piece king = board.getPiece(4, 0).get();
        assertThat(moveService.getCastlingMove(board, king, 4, 0, 2, 0, 3, Collections.emptyList())).isEmpty();
    }

    @ParameterizedTest
    @ValueSource(strings= {
    		"♜ ♞     ♚     ♜ \n" +
            "♟ ♟ ♟     ♟ ♟ ♟ \n" +
            "      ♟         \n" +
            "        ♟       \n" +
            "      ♛ ♙       \n" +
            "          ♙     \n" +
            "♙ ♙ ♙       ♙ ♙ \n" +
            "♖       ♔ ♗ ♘ ♖ \n",
            
            "♜ ♞     ♚     ♜ \n" +
            "♟ ♟ ♟     ♟ ♟ ♟ \n" +
            "      ♟         \n" +
            "        ♟       \n" +
            "  ♝ ♛   ♙       \n" +
            "      ♙   ♙     \n" +
            "♙ ♙         ♙ ♙ \n" +
            "♖       ♔ ♗ ♘ ♖ \n",
            
            "♜ ♞     ♚     ♜ \n" +
            "♟ ♟ ♟     ♟ ♟ ♟ \n" +
            "      ♟         \n" +
            "        ♟       \n" +
            "  ♝ ♛   ♙       \n" +
            "      ♙   ♙     \n" +
            "♙ ♙         ♙ ♙ \n" +
            "♖       ♔ ♗ ♘ ♖ \n"
    })
    public void getCastlingMove_kingCrossFireOrChecked(String boardString) {
        Board board = new Board(boardString);
        Piece king = board.getPiece(4, 0).get();
        assertThat(moveService.getCastlingMove(board, king, 4, 0, 2, 0, 3, Collections.emptyList())).isEmpty();
    }
    
    @ParameterizedTest
    @MethodSource
    public void getCastlingMove_kingOrRookAlreadyMoved_returnEmpty(Move move) {
    	Board board = new Board("" +
                "♜       ♚     ♜ \n" +
                "♟ ♟ ♟ ♛   ♟ ♟ ♟ \n" +
                "    ♞ ♟         \n" +
                "        ♟       \n" +
                "        ♙       \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖       ♔ ♗ ♘ ♖ \n"
        );
        Piece whiteKing = board.getPiece(4, 0).get();
        List<Move> history = Collections.singletonList(move);
        assertThat(moveService.getCastlingMove(board, whiteKing, 4, 0, 2, 0, 3, history)).isEmpty();
    }
    
    private static Stream<Arguments> getCastlingMove_kingOrRookAlreadyMoved_returnEmpty() {
    	return Stream.of(
    			arguments(new Move(new King(Color.WHITE), 4, 0, 3, 0)),
    			arguments(new Move(new Pawn(Color.WHITE), 4, 0, 3, 0)),
    			arguments(new Move(new Rook(Color.WHITE), 0, 0, 1, 0))
    	);
    }

    @ParameterizedTest
    @MethodSource
    public void isValidKingPositionForCastling_kingHasMoved_returnFalse(String stringBoard, int x, int y) {
        Board board = new Board(stringBoard);
        Piece king = board.getPiece(x, y).get();
        assertThat(moveService.isValidKingPositionForCastling(king, x, y, board)).isFalse();
    }
    
    private static Stream<Arguments> isValidKingPositionForCastling_kingHasMoved_returnFalse() {
    	return Stream.of(
    			arguments("♜ ♞ ♝ ♛ ♚     ♜ \n" +
		                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
		                "      ♟         \n" +
		                "        ♟       \n" +
		                "        ♙   ♕   \n" +
		                "          ♙     \n" +
		                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
		                "♖     ♔   ♗ ♘ ♖ \n", 3, 0),
    			arguments("♜ ♞ ♝ ♛ ♚     ♜ \n" +
    	                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
    	                "      ♟         \n" +
    	                "        ♟       \n" +
    	                "        ♙   ♕   \n" +
    	                "          ♙     \n" +
    	                "♙ ♙ ♙ ♙ ♔   ♙ ♙ \n" +
    	                "♖         ♗ ♘ ♖ \n", 4, 1),
    			arguments("♜ ♞ ♝ ♛       ♜ \n" +
    	                "♟ ♟ ♟   ♚ ♟ ♟ ♟ \n" +
    	                "      ♟         \n" +
    	                "        ♟       \n" +
    	                "        ♙   ♕   \n" +
    	                "          ♙     \n" +
    	                "♙ ♙ ♙ ♙ ♔   ♙ ♙ \n" +
    	                "♖         ♗ ♘ ♖ \n", 4,6)
    	);
    }

    @ParameterizedTest
    @ValueSource(strings= {
    		"♜ ♞ ♝ ♛ ♚     ♜ \n" +
            "♟ ♟ ♟     ♟ ♟ ♟ \n" +
            "      ♟         \n" +
            "        ♟       \n" +
            "        ♙       \n" +
            "          ♙     \n" +
            "♙ ♙ ♙ ♙     ♙ ♙ \n" +
            "♖     ♔   ♗ ♘ ♖ \n",
            
            "♜ ♞ ♝ ♛ ♚     ♜ \n" +
            "♟ ♟ ♟     ♟ ♟ ♟ \n" +
            "      ♟         \n" +
            "        ♟       \n" +
            "        ♙       \n" +
            "          ♙     \n" +
            "♙ ♙ ♙ ♙     ♙ ♙ \n" +
            "♖     ♔ ♕ ♗ ♘ ♖ \n",
            
            "♜ ♞ ♝ ♛       ♜ \n" +
            "♟ ♟ ♟     ♟ ♟ ♟ \n" +
            "      ♟         \n" +
            "        ♟       \n" +
            "        ♙       \n" +
            "          ♙     \n" +
            "♙ ♙ ♙ ♙ ♕   ♙ ♙ \n" +
            "♖     ♔ ♚ ♗ ♘ ♖ \n"
    })
    public void testIsValidKingPositionForCastling_invalidKingPosition_returnFalse(String boardString) {
        Board board = new Board(boardString);
        Piece king = board.getPiece(3, 0).get();
        assertThat(moveService.isValidKingPositionForCastling(king, 4, 0, board)).isFalse();
    }

    @Test
    public void isValidKingPositionForCastling_inCheck_returnFalse() {
        Board board = new Board("" +
                "♜ ♞   ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙     ♝ \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖       ♔ ♗ ♘ ♖ \n"
        );
        Piece king = board.getPiece(4, 0).get();
        assertThat(moveService.isValidKingPositionForCastling(king, 4, 0, board)).isFalse();
    }

    @Test
    public void isValidKingPositionForCastling_validPosition_returnTrue() {
        Board board = new Board("" +
                "♜ ♞   ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙       \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖       ♔ ♗ ♘ ♖ \n"
        );
        Piece whiteKing = board.getPiece(4, 0).get();
        assertThat(moveService.isValidKingPositionForCastling(whiteKing, 4, 0, board)).isTrue();
        Piece blackKing = board.getPiece(4, 7).get();
        assertThat(moveService.isValidKingPositionForCastling(blackKing, 4, 7, board)).isTrue();
    }
    
    @Test
    public void computeCastlingMoves_blackBothSides_return2Moves() {
        Board board = new Board("" +
                "♜       ♚     ♜ \n" +
                "♟ ♟ ♟ ♛   ♟ ♟ ♟ \n" +
                "    ♞ ♟         \n" +
                "        ♟       \n" +
                "        ♙       \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖     ♔   ♗ ♘ ♖ \n"
        );
        Piece blackKing = board.getPiece(4, 7).get();
        
        assertThat(moveService.computeCastlingMoves(blackKing, 4, 7, board, Collections.emptyList())).hasSize(2).containsExactlyInAnyOrder(
        		new CastlingMove(blackKing,4,7,2,7, new Rook(Color.BLACK), 0,7,3,7),
        		new CastlingMove(blackKing,4,7,6,7, new Rook(Color.BLACK), 7,7,5,7)
        );
    }

    @Test
    public void computeCastlingMoves_kingInvalid_returnEmpty() {
    	Board board = new Board("" +
    			"♜       ♚     ♜ \n" +
    			"♟ ♟ ♟ ♛   ♟ ♟ ♟ \n" +
    			"    ♞ ♟         \n" +
    			"        ♟       \n" +
    			"        ♙       \n" +
    			"          ♙     \n" +
    			"♙ ♙ ♙ ♙     ♙ ♙ \n" +
    			"♖     ♔   ♗ ♘ ♖ \n"
    			);
    	Piece whiteKing = board.getPiece(3, 0).get();
        assertThat(moveService.computeCastlingMoves(whiteKing, 4, 0, board, Collections.emptyList())).isEmpty();
    }

    @Test
    public void computeCastlingMoves_deniedByHistory_returnEmpty() {
        Board board = new Board("" +
                "♜       ♚     ♜ \n" +
                "♟ ♟ ♟ ♛   ♟ ♟ ♟ \n" +
                "    ♞ ♟         \n" +
                "        ♟       \n" +
                "        ♙       \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖       ♔ ♗ ♘ ♖ \n"
        );
        Piece whiteKing = board.getPiece(4, 0).get();
        List<Move> history = Collections.singletonList(new Move(whiteKing, 4, 0, 3, 0));
        assertThat(moveService.computeCastlingMoves(whiteKing, 4, 0, board, history)).isEmpty();
    }
    
    @Test
    public void computeMoves_castlingPossible_returnCorrectSizeForEachPiece() {
    	Board board = new Board("" +
                "♜ ♞   ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙       \n" +
                "                \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖       ♔ ♗ ♘ ♖ \n"
        );
    	
    	Piece pawn = board.getPiece(3,1).get();
    	List<Move> pawnMoves = moveService.computeMoves(board, pawn, 3, 1, Collections.emptyList(), false, false);
    	assertThat(pawnMoves).hasSize(2);
    	
    	Piece rook = board.getPiece(7, 0).get();
    	List<Move> rookMoves = moveService.computeMoves(board, rook, 7, 0, Collections.emptyList(), false, false);
    	assertThat(rookMoves).isEmpty();

    	Piece queen = board.getPiece(3, 7).get();
    	List<Move> queenMoves = moveService.computeMoves(board, queen, 3, 7, Collections.emptyList(), true, false);
    	assertThat(queenMoves).hasSize(6).anyMatch(it -> it.isChecking());
    	
    	Piece knight = board.getPiece(6, 0).get();
    	List<Move> knightMoves = moveService.computeMoves(board, knight, 6, 0, Collections.emptyList(), false, false);
    	assertThat(knightMoves).hasSize(3);

    	Piece bishop = board.getPiece(5, 0).get();
    	List<Move> bishopMoves = moveService.computeMoves(board, bishop, 5, 0, Collections.emptyList(), false, false);
    	assertThat(bishopMoves).hasSize(5);
    	
    	Piece king = board.getPiece(4, 0).get();
    	List<Move> kingMoves = moveService.computeMoves(board, king, 4, 0, Collections.emptyList(), false, true);
    	assertThat(kingMoves).hasSize(3);

		assertThat(moveService.computeMoves(board, king, 4, 0, Collections.emptyList(), false, false)).hasSize(4)
				.anyMatch(CastlingMove.class::isInstance);
    }
    
    @Test
    public void computeBoardMoves_initialPositions_returnAllPossibleStartingMoves() {
        // Initial positions board
        Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
        Board board = game.getBoard();
        List<Move> whiteMovesStart = moveService.computeBoardMoves(board, Color.WHITE, game.getHistory(),false, false, false);
        assertThat(whiteMovesStart).containsExactlyInAnyOrder(
                // Pawns
                new Move(board.getPiece(0, 1).get(), 0, 1, 0, 2),
                new Move(board.getPiece(0, 1).get(), 0, 1, 0, 3),
                new Move(board.getPiece(1, 1).get(), 1, 1, 1, 2),
                new Move(board.getPiece(1, 1).get(), 1, 1, 1, 3),
                new Move(board.getPiece(2, 1).get(), 2, 1, 2, 2),
                new Move(board.getPiece(2, 1).get(), 2, 1, 2, 3),
                new Move(board.getPiece(3, 1).get(), 3, 1, 3, 2),
                new Move(board.getPiece(3, 1).get(), 3, 1, 3, 3),
                new Move(board.getPiece(4, 1).get(), 4, 1, 4, 2),
                new Move(board.getPiece(4, 1).get(), 4, 1, 4, 3),
                new Move(board.getPiece(5, 1).get(), 5, 1, 5, 2),
                new Move(board.getPiece(5, 1).get(), 5, 1, 5, 3),
                new Move(board.getPiece(6, 1).get(), 6, 1, 6, 2),
                new Move(board.getPiece(6, 1).get(), 6, 1, 6, 3),
                new Move(board.getPiece(7, 1).get(), 7, 1, 7, 2),
                new Move(board.getPiece(7, 1).get(), 7, 1, 7, 3),
                // Knights
                new Move(board.getPiece(1, 0).get(), 1, 0, 0, 2),
                new Move(board.getPiece(1, 0).get(), 1, 0, 2, 2),
                new Move(board.getPiece(6, 0).get(), 6, 0, 5, 2),
                new Move(board.getPiece(6, 0).get(), 6, 0, 7, 2)
        );
    }

    @Test
    public void computeBoardMoves_returnFirstPieceHavingMoves_returnKnightMoves() {
        // Initial positions board
        Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
        Board board = game.getBoard();
        List<Move> whiteMovesStart = moveService.computeBoardMoves(board, Color.WHITE, game.getHistory(),false, true, false);
        assertThat(whiteMovesStart).containsExactlyInAnyOrder(
                new Move(board.getPiece(1, 0).get(), 1, 0, 0, 2),
                new Move(board.getPiece(1, 0).get(), 1, 0, 2, 2)
        );
    }
    
    @Test
    public void canMove_initialPosition_returnTrueForBothColor() {
        // Initial positions board
        Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
        Board board = game.getBoard();
        assertThat(moveService.canMove(board, Color.WHITE, game.getHistory())).isTrue();
        assertThat(moveService.canMove(board, Color.BLACK, game.getHistory())).isTrue();
    }

    @Test
    public void canMove_checkMate_returnFalse() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" +
                "♟ ♟ ♟ ♟ ♟     ♟ \n" +
                "          ♟     \n" +
                "            ♟ ♕ \n" +
                "          ♙     \n" +
                "        ♙       \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ \n"
        );
        assertThat(moveService.canMove(board, Color.BLACK, Collections.emptyList())).isFalse();
    }

    @Test
    public void computeAllMoves_initialPosition_return20Moves() {
        Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
        Board initialBoard = game.getBoard();
        // Each player has 20 possible moves in initial position
        assertThat(moveService.computeAllMoves(initialBoard, Color.WHITE, game.getHistory(), false)).hasSize(20)
        	.isEqualTo(moveService.computeAllMoves(initialBoard, Color.WHITE, game.getHistory(), false, false));
        
        assertThat(moveService.computeAllMoves(initialBoard, Color.BLACK, game.getHistory(),false)).hasSize(20);
    }
    
    @Test
    public void getHeatmapAroundLocation_leftBottomCorner_returnExpectedHeatMap() {
        int[][] heatmap = moveService.getHeatmapAroundLocation(7, 0);
        int[][] expected = new int[][] {
                {0, 0, 0, 0, 0, 0, 0, 0},
                {0, 0, 0, 0, 0, 0, 0, 0},
                {0, 0, 0, 0, 0, 0, 0, 0},
                {0, 0, 0, 0, 0, 0, 0, 0},
                {0, 0, 0, 0, 0, 0, 0, 0},
                {1, 1, 1, 0, 0, 0, 0, 0},
                {2, 2, 1, 0, 0, 0, 0, 0},
                {3, 2, 1, 0, 0, 0, 0, 0},
        };
        assertThat(heatmap).hasDimensions(8, 8).isEqualTo(expected);
    }
    
    @Test
    public void getHeatScore_initialBoard_return0() {
    	Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
        Board initialBoard = game.getBoard();

		assertThat(moveService.getHeatScore(initialBoard, Color.WHITE, new Position(4, 0), new Position(4, 7),
				Collections.emptyList())).isZero();
		assertThat(moveService.getHeatScore(initialBoard, Color.BLACK, new Position(4, 7), new Position(4, 0),
				Collections.emptyList())).isZero();
    }
    
    @Test
    public void getHeatScore_checkmateAfter30Moves_return18() {
    	Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" +
                "♟ ♟ ♟ ♟ ♟     ♟ \n" +
                "          ♟     \n" +
                "            ♟ ♕ \n" +
                "          ♙     \n" +
                "        ♙       \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖ ♘ ♗   ♔ ♗ ♘ ♖ \n"
        );
    	
    	List<Move> history = spy(new ArrayList<Move>());
    	doReturn(30).when(history).size();
    	
    	assertThat(moveService.getHeatScore(board, Color.WHITE, new Position(4, 0), new Position(4, 7),
    			history)).isEqualTo(18);
    }

    @Test
    public void getPiecesValueSum_initialPosition_return140() {
        // Initial positions board
        Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
        Board board = game.getBoard();
        assertThat(moveService.getPiecesValueSum(board, Color.WHITE)).isEqualTo(
                8 * (new Pawn(Color.WHITE)).getValue()
                + 2 * (new Knight(Color.WHITE)).getValue()
                + 2 * (new Bishop(Color.WHITE)).getValue()
                + 2 * (new Rook(Color.WHITE)).getValue()
                + (new Queen(Color.WHITE)).getValue()
                + (new King(Color.WHITE)).getValue()
                ).isEqualTo(moveService.getPiecesValueSum(board, Color.BLACK));
			
		assertThat(moveService.getPiecesScore(board, Color.WHITE)).isEqualTo(0)
				.isEqualTo(moveService.getPiecesScore(board, Color.BLACK));
    }
    
    @Test
    public void getPiecesValueSum_blackDisadvantage_returnCorrectPoints() {
        Board board = new Board("" +
                "                \n" +
                "                \n" +
                "        ♚       \n" +
                "            ♟ ♕ \n" +
                "    ♗     ♙     \n" +
                "          ♘     \n" +
                "♛           ♙ ♙ \n" +
                "    ♖   ♔       \n"
        );
        assertThat(moveService.getPiecesValueSum(board, Color.BLACK)).isEqualTo(111);
        assertThat(moveService.getPiecesValueSum(board, Color.WHITE)).isEqualTo(124);
    	assertThat(moveService.getPiecesScore(board, Color.WHITE)).isEqualTo(13);

    }
    
    @Test
    public void getDevelopmentBonus_noMovesDone_return0() {
        assertThat(moveService.getDevelopmentBonus(Collections.emptyList())).isEqualTo(0);
    }

    @ParameterizedTest
    @MethodSource
    public void getDevelopmentBonus_importantPieceMoveInOpening_returnOpeningPenalty(Move move) {
        List<Move> moves = Arrays.asList(
            new Move(new Pawn(Color.WHITE), 3, 1, 3, 3),
            move
        );
        assertThat(moveService.getDevelopmentBonus(moves)).isEqualTo(-5 + (move.getPiece() instanceof King ? - 10 : 0));
    }
    
    private static Stream<Arguments> getDevelopmentBonus_importantPieceMoveInOpening_returnOpeningPenalty() {
    	return Stream.of(
    			arguments(new Move(new Queen(Color.WHITE), 3, 1, 3, 3)),
    			arguments(new Move(new King(Color.WHITE), 3, 1, 3, 3)),
    			arguments(new Move(new Rook(Color.WHITE), 3, 1, 3, 3))
    	);
    }

    @Test
    public void getDevelopmentBonus_pieceMovedTwiceInOpening_returnOpeningPenalty() {
        Piece knight = new Knight(Color.WHITE);
        List<Move> moves = Arrays.asList(
            new Move(knight, 1, 0, 2, 2),
            new Move(knight, 2, 2, 3, 4)
        );
        assertThat(moveService.getDevelopmentBonus(moves)).isEqualTo(-5);
    }

    @Test
    public void getDevelopmentBonus_castling_returnCastlingBonus() {
        Piece king = new King(Color.WHITE);
        List<Move> moves = Arrays.asList(
            new CastlingMove(king, 4, 0, 2, 0, new Rook(Color.WHITE), 0, 0, 3, 0)
        );
        assertThat(moveService.getDevelopmentBonus(moves)).isEqualTo(15);
    }

    @Test
    public void getDevelopmentBonus_kingMoveBeforeCastling_returnKingMovedPenalty() {
        List<Move> moves = Arrays.asList(
            new Move(new Pawn(Color.WHITE), 3, 1, 3, 2),
            new Move(new Pawn(Color.WHITE), 3, 2, 3, 3),
            new Move(new Pawn(Color.WHITE), 3, 3, 3, 4),
            new Move(new Pawn(Color.WHITE), 3, 4, 3, 5),
            new Move(new Pawn(Color.WHITE), 3, 5, 3, 6),
            new Move(new King(Color.WHITE), 4, 0, 4, 1)
            );
        assertThat(moveService.getDevelopmentBonus(moves)).isEqualTo(-10);
    }

    @Test
    public void getDevelopmentScore_whiteCasltedBlackMovedQueen_return20() {
    	List<Move> moves = Arrays.asList(
				new CastlingMove(new King(Color.WHITE), 4, 0, 2, 0, new Rook(Color.WHITE), 0, 0, 3, 0),
				new Move(new Pawn(Color.BLACK), 3, 6, 3, 4),
				new Move(new Queen(Color.BLACK), 3, 7, 3, 5));
    	assertThat(moveService.getDevelopmentScore(Color.WHITE, moves)).isEqualTo(20);
    }
    
	@Test
	public void evaluateBoard_loss_returnWorstPossible() {
		assertThat(moveService.evaluateBoard(null, Color.BLACK, Color.WHITE, GameState.LOSS, null, null,
				Collections.emptyList())).isEqualTo(MoveService.WORST);
	}

	@Test
	public void evaluateBoard_win_returnBestPossible() {
		assertThat(moveService.evaluateBoard(null, Color.BLACK, Color.BLACK, GameState.LOSS, null, null,
				Collections.emptyList())).isEqualTo(MoveService.BEST);
	}

	@Test
	public void evaluateBoard_draw_returnDrawPenalty() {
		assertThat(moveService.evaluateBoard(null, Color.BLACK, Color.BLACK, GameState.DRAW_STALEMATE, null, null,
				Collections.emptyList())).isEqualTo(-20);
	}

    @Test
    public void evaluateBoard_initialPosition_returnZero() {
        Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
        assertThat(moveService.evaluateBoard(game.getBoard(), Color.WHITE, Color.BLACK, GameState.IN_PROGRESS, new Position(4, 7), new Position(4, 0), game.getHistory())).isEqualTo(0);
    }

    @Test
    public void evaluateBoard_oneRookMissing_returnMinus50() {
    	Game game = new Game(new RandomBot(moveService), new RandomBot(moveService));
    	game.getBoard().getBoard()[0][0] = null;
    	assertThat(moveService.evaluateBoard(game.getBoard(), Color.WHITE, Color.BLACK, GameState.IN_PROGRESS, new Position(4, 7), new Position(4, 0), game.getHistory())).isEqualTo(-50);
    }
    
    @Test
    public void getMaxScoreWithRandomChoice_maxScoreIs8_returnMoveWithThatScore() {
        Map<MoveAnalysis, Integer> map = new HashMap<>();
        map.put(new MoveAnalysis(new Move(new Bishop(Color.WHITE), 4, 5, 5, 6)), -2);
        map.put(new MoveAnalysis(new Move(new Bishop(Color.WHITE), 4, 5, 3, 4)), 5);
        map.put(new MoveAnalysis(new Move(new Bishop(Color.WHITE), 4, 5, 6, 7)), 8);
        map.put(new MoveAnalysis(new Move(new Knight(Color.WHITE), 2, 3, 4, 4)), 8);
        map.put(new MoveAnalysis(new Move(new Knight(Color.WHITE), 2, 3, 1, 5)), 7);
        map.put(new MoveAnalysis(new Move(new Knight(Color.WHITE), 2, 3, 0, 4)), -2);
        
        Optional<MoveAnalysis> bestmove = moveService.getMaxScoreWithRandomChoice(map);
        
        assertThat(bestmove).isPresent();
        assertThat(map.get(bestmove.get())).isEqualTo(8);

    }

    @Test
    public void getMaxScoreWithRandomChoice_singleMove_returnOnlyMove() {
        Map<MoveAnalysis, Integer> map = new HashMap<>(1);
        MoveAnalysis moveAnalysis = new MoveAnalysis(new Move(new Bishop(Color.WHITE), 4, 5, 5, 6));
        
        map.put(moveAnalysis, 0);
        assertThat(moveService.getMaxScoreWithRandomChoice(map)).isPresent().get().isEqualTo(moveAnalysis);
    }

	@Test
	public void getMaxScoreWithRandomChoice_emptyMap_returnEmpty() {
		assertThat(moveService.getMaxScoreWithRandomChoice(new HashMap<>())).isEmpty();
	}

	@Test
	public void getBestMove_bestMoveisQueenG8_returnQueenMove() {
		Map<MoveAnalysis, Integer> map = new HashMap<>();
		map.put(new MoveAnalysis(new Move(new Bishop(Color.BLACK), 4, 5, 5, 6)), 60);
		map.put(new MoveAnalysis(new Move(new Bishop(Color.BLACK), 4, 5, 3, 4)), 23);
		map.put(new MoveAnalysis(new Move(new Bishop(Color.BLACK), 4, 5, 6, 7)), 45);
		map.put(new MoveAnalysis(new Move(new Knight(Color.BLACK), 2, 3, 4, 4)), -56);
		map.put(new MoveAnalysis(new Move(new Knight(Color.BLACK), 2, 3, 1, 5)), 20);
		map.put(new MoveAnalysis(new Move(new Knight(Color.BLACK), 2, 3, 0, 4)), 59);
		MoveAnalysis bestMove = new MoveAnalysis(new Move(new Queen(Color.BLACK), 6, 6, 6, 7));
		map.put(bestMove, 65);

		assertThat(moveService.getBestMove(map)).isEqualTo(bestMove);
	}

	@Test
	public void getBestMove_empty_throwsRuntime() {
		assertThatRuntimeException().isThrownBy(() -> moveService.getBestMove(new HashMap<>()));
	}


}
