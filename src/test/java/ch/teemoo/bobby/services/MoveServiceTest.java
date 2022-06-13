package ch.teemoo.bobby.services;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatRuntimeException;
import static org.junit.jupiter.params.provider.Arguments.arguments;

import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.ValueSource;

import ch.teemoo.bobby.models.Board;
import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.Position;
import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.moves.CastlingMove;
import ch.teemoo.bobby.models.moves.EnPassantMove;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.moves.PromotionMove;
import ch.teemoo.bobby.models.pieces.Bishop;
import ch.teemoo.bobby.models.pieces.Knight;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Queen;
import ch.teemoo.bobby.models.pieces.Rook;
import ch.teemoo.bobby.models.players.RandomBot;

class MoveServiceTest {

	private MoveService moveService;

	@BeforeEach
	public void setup() {
		moveService = new MoveService();
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

    private Move getMoveWithTookPiece(Piece piece, int fromX, int fromY, int toX, int toY, Piece tookPiece) {
        Move move = new Move(piece, fromX, fromY, toX, toY);
        move.setTookPiece(tookPiece);
		return move;
	}
    
    @Test
    public void testGetCastlingMoveCorrect() {
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
        assertThat(moveService.getCastlingMove(board, whiteKing, 4, 0, 2, 0, 3, Collections.emptyList())).isPresent().get().isInstanceOf(
            CastlingMove.class);
        Piece blackKing = board.getPiece(4, 7).get();
        assertThat(moveService.getCastlingMove(board, blackKing, 4, 7, 6, 7, 5, Collections.emptyList())).isPresent().get().isInstanceOf(CastlingMove.class);
    }

    @Test
    public void testGetCastlingMoveRookNotPresent() {
        Board board = new Board("" +
                "♜ ♞   ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙       \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "        ♔ ♗ ♘ ♖ \n"
        );
        Piece king = board.getPiece(4, 0).get();
        assertThat(moveService.getCastlingMove(board, king, 4, 0, 2, 0, 3, Collections.emptyList())).isEmpty();

        board = new Board("" +
                "♜ ♞   ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙       \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♗       ♔   ♘ ♖ \n"
        );
        assertThat(moveService.getCastlingMove(board, king, 4, 0, 2, 0, 3, Collections.emptyList())).isEmpty();

        board = new Board("" +
                "  ♞   ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙       \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♜       ♔ ♗ ♘ ♖ \n"
        );
        assertThat(moveService.getCastlingMove(board, king, 4, 0, 2, 0, 3, Collections.emptyList())).isEmpty();
    }

    @Test
    public void testGetCastlingMovePieceBetweenRookAndKing() {
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

    @Test
    public void testGetCastlingMoveKingCrossFire() {
        Board board = new Board("" +
                "♜ ♞     ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "    ♛   ♙       \n" +
                "          ♙     \n" +
                "♙ ♙   ♙     ♙ ♙ \n" +
                "♖       ♔ ♗ ♘ ♖ \n"
        );
        Piece king = board.getPiece(4, 0).get();
        assertThat(moveService.getCastlingMove(board, king, 4, 0, 2, 0, 3, Collections.emptyList())).isEmpty();
    }

    @Test
    public void testIsValidKingPositionForCastlingKingHasMoved() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙   ♕   \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖     ♔   ♗ ♘ ♖ \n"
        );
        Piece king = board.getPiece(3, 0).get();
        assertThat(moveService.isValidKingPositionForCastling(king, 3, 0, board)).isFalse();

        board = new Board("" +
                "♜ ♞ ♝ ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙   ♕   \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙ ♔   ♙ ♙ \n" +
                "♖         ♗ ♘ ♖ \n"
        );
        king = board.getPiece(4, 1).get();
        assertThat(moveService.isValidKingPositionForCastling(king, 4, 1, board)).isFalse();

        board = new Board("" +
                "♜ ♞ ♝ ♛       ♜ \n" +
                "♟ ♟ ♟   ♚ ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙   ♕   \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙ ♔   ♙ ♙ \n" +
                "♖         ♗ ♘ ♖ \n"
        );
        king = board.getPiece(4, 6).get();
        assertThat(moveService.isValidKingPositionForCastling(king, 4, 6, board)).isFalse();
    }


    @Test
    public void testIsValidKingPositionForCastlingWrongPiece() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙       \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖     ♔ ♕ ♗ ♘ ♖ \n"
        );
        Piece king = board.getPiece(3, 0).get();
        assertThat(moveService.isValidKingPositionForCastling(king, 4, 0, board)).isFalse();
    }

    @Test
    public void testIsValidKingPositionForCastlingEmptyLocation() {
        Board board = new Board("" +
                "♜ ♞ ♝ ♛ ♚     ♜ \n" +
                "♟ ♟ ♟     ♟ ♟ ♟ \n" +
                "      ♟         \n" +
                "        ♟       \n" +
                "        ♙       \n" +
                "          ♙     \n" +
                "♙ ♙ ♙ ♙     ♙ ♙ \n" +
                "♖     ♔   ♗ ♘ ♖ \n"
        );
        Piece king = board.getPiece(3, 0).get();
        assertThat(moveService.isValidKingPositionForCastling(king, 4, 0, board)).isFalse();
    }

    @Test
    public void testIsValidKingPositionForCastlingInCheck() {
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
    public void testIsValidKingPositionForCastlingCorrect() {
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

}
