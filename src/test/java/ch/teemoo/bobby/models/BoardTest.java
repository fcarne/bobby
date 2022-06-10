package ch.teemoo.bobby.models;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import ch.teemoo.bobby.models.moves.CastlingMove;
import ch.teemoo.bobby.models.moves.EnPassantMove;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.moves.PromotionMove;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Queen;
import ch.teemoo.bobby.models.pieces.Rook;

class BoardTest {

	Board initialBoard;
	Move move;
	Piece pawn;

	@BeforeEach
	public void setup() {
		initialBoard = new Board("♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" + //
				"♟ ♟ ♟ ♟ ♟ ♟ ♟ ♟ \n" + //
				"                \n" + //
				"                \n" + //
				"                \n" + //
				"                \n" + //
				"♙ ♙ ♙ ♙ ♙ ♙ ♙ ♙ \n" + //
				"♖ ♘ ♗ ♕ ♔ ♗ ♘ ♖ \n");
		pawn = initialBoard.getPiece(0, 1).get();
		move = new Move(pawn, 0, 1, 0, 2);
	}

	@Test
	void arrayConstructor_ok_returnCorrect() {
		Piece[][] pieces = new Piece[Board.SIZE][Board.SIZE];
		Rook rook = new Rook(Color.WHITE);
		pieces[0][0] = rook;
		Board board = new Board(pieces);

		assertThat(board.getBoard()).isDeepEqualTo(pieces);
		assertThat(board.getPiece(0, 0)).isPresent().get().isEqualTo(rook);
		assertThat(board.getPiece(0, 1)).isEmpty();
	}

	@Test
	void stringConstructor_ok_returnCorrect() {
		Board board = new Board("                \n" + //
				"                \n" + //
				"                \n" + //
				"                \n" + //
				"                \n" + //
				"                \n" + //
				"                \n" + //
				"♖               \n");

		Piece[][] pieces = new Piece[Board.SIZE][Board.SIZE];
		Rook rook = new Rook(Color.WHITE);
		pieces[0][0] = rook;

		assertThat(board.getBoard()).isDeepEqualTo(pieces);
		assertThat(board.getPiece(0, 0)).isPresent().get().isEqualTo(rook);
		assertThat(board.getPiece(0, 1)).isEmpty();
	}

	@Test
	void copy_initialPosition_returnSame() {
		Board board = initialBoard.copy();
		assertThat(board.getBoard()).isDeepEqualTo(initialBoard.getBoard());
		assertThat(board.toString()).isEqualTo(initialBoard.toString());
	}

	@Test
	void toString_initialPosition_returnCorrect() {
		String representation = "♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜ \n" + //
				"♟ ♟ ♟ ♟ ♟ ♟ ♟ ♟ \n" + //
				"                \n" + //
				"                \n" + //
				"                \n" + //
				"                \n" + //
				"♙ ♙ ♙ ♙ ♙ ♙ ♙ ♙ \n" + //
				"♖ ♘ ♗ ♕ ♔ ♗ ♘ ♖ \n";

		assertThat(initialBoard.toString()).isEqualTo(representation);
	}

	@Test
	public void doMove_normalMove_movesPiece() {

		assertThat(pawn).isEqualTo(new Pawn(Color.WHITE));
		assertThat(initialBoard.getPiece(0, 2)).isEmpty();
		initialBoard.doMove(move);

		assertThat(initialBoard.getPiece(0, 1)).isEmpty();
		assertThat(initialBoard.getPiece(0, 2)).isPresent().get().isEqualTo(pawn);
	}

	@Test
	public void doMove_promotionMove_pawnMovedAndPromoted() {
		Queen queen = new Queen(Color.WHITE);
		PromotionMove pmove = new PromotionMove(move, queen);

		initialBoard.doMove(pmove);

		assertThat(initialBoard.getPiece(0, 1)).isEmpty();
		assertThat(initialBoard.getPiece(0, 2)).isPresent().get().isEqualTo(queen);
	}
	
	@Test
	public void doMove_castlingMove_rookAndKingMoved() {
		Board board = new Board("" +
                "♜ ♞ ♝   ♚ ♝   ♜ \n" +
                "♟ ♟   ♟ ♞ ♟ ♟ ♟ \n" +
                "    ♟           \n" +
                "                \n" +
                "      ♛         \n" +
                "  ♕ ♘           \n" +
                "♙ ♙   ♗ ♙ ♙ ♙ ♙ \n" +
                "♖       ♔ ♗ ♘ ♖ \n");

		Piece king = board.getPiece(4, 0).get();
		Piece rook = board.getPiece(0, 0).get();
		Move castlingMove = new CastlingMove(king, 4, 0, 2, 0, rook, 0, 0, 3, 0);
		board.doMove(castlingMove);
		assertThat(board.getPiece(2, 0)).isPresent().get().isEqualTo(king);
		assertThat(board.getPiece(3, 0)).isPresent().get().isEqualTo(rook);
		assertThat(board.getPiece(4, 0)).isEmpty();
		assertThat(board.getPiece(0, 0)).isEmpty();
	}

	@Test
	public void doMove_enPassantMove_pawnTaken() {
		Board board = new Board("" +
				"♜ ♞ ♝   ♚ ♝   ♜ \n" +
				"♟     ♟ ♞ ♟ ♟ ♟ \n" +
				"    ♟           \n" +
				"♙ ♟             \n" +
				"      ♛         \n" +
				"  ♕ ♘           \n" +
				"  ♙   ♗ ♙ ♙ ♙ ♙ \n" +
				"♖       ♔ ♗ ♘ ♖ \n");
		Piece whitePawn = board.getPiece(0, 4).get();
		Piece blackPawn = board.getPiece(1, 4).get();
		
		Move move = new Move(whitePawn, 0, 4, 1, 5);
        move.setTookPiece(blackPawn);
        EnPassantMove enPassantMove = new EnPassantMove(move, 1, 4);
        
        assertThat(board.getPiece(1, 5)).isEmpty();
        
        board.doMove(enPassantMove);
        assertThat(board.getPiece(0, 4)).isEmpty();
        assertThat(board.getPiece(1, 3)).isEmpty();
        assertThat(board.getPiece(1, 5)).isPresent().get().isEqualTo(whitePawn);
	}

	@Test
	public void undoMove_normalMove_movesPiece() {
		initialBoard.doMove(move);

		assertThat(initialBoard.getPiece(0, 2)).isPresent();
		initialBoard.undoMove(move);

		assertThat(initialBoard.getPiece(0, 2)).isEmpty();
		assertThat(initialBoard.getPiece(0, 1)).isPresent();
		assertThat(initialBoard.getPiece(0, 1).get()).isEqualTo(pawn);
	}
	
	@Test
	public void undoMove_takingMove_pieceRepositioned() {
		Board board = new Board("" +
				"♜ ♞ ♝   ♚ ♝   ♜ \n" +
				"♟     ♟ ♞ ♟ ♟ ♟ \n" +
				"  ♟  ♟           \n" +
				"♙               \n" +
				"      ♛         \n" +
				"  ♕ ♘           \n" +
				"  ♙   ♗ ♙ ♙ ♙ ♙ \n" +
				"♖       ♔ ♗ ♘ ♖ \n");
		Piece whitePawn = board.getPiece(0, 4).get();
		Piece blackPawn = board.getPiece(1, 5).get();
		
		Move move = new Move(whitePawn, 0, 4, 1, 5);
        move.setTookPiece(blackPawn);
        
        assertThat(move.isTaking()).isTrue();
        
        board.doMove(move);
        
        board.undoMove(move);

		assertThat(board.getPiece(0, 4)).isPresent().get().isEqualTo(whitePawn);
		assertThat(board.getPiece(1, 5)).isPresent().get().isEqualTo(blackPawn);
	}

	@Test
	public void undoMove_promotionMove_pawnMovedAndPromotedBack() {
		Queen queen = new Queen(Color.WHITE);
		PromotionMove pmove = new PromotionMove(move, queen);
		initialBoard.doMove(pmove);

		assertThat(initialBoard.getPiece(0, 2).get()).isEqualTo(queen);

		initialBoard.undoMove(pmove);
		assertThat(initialBoard.getPiece(0, 2)).isEmpty();
		assertThat(initialBoard.getPiece(0, 1)).isPresent();
		assertThat(initialBoard.getPiece(0, 1).get()).isEqualTo(pawn);

	}

	@Test
	public void undoMove_castlingMove_rookAndKingMovedBack() {
		Board board = new Board("" +
                "♜ ♞ ♝   ♚ ♝   ♜ \n" +
                "♟ ♟   ♟ ♞ ♟ ♟ ♟ \n" +
                "    ♟           \n" +
                "                \n" +
                "      ♛         \n" +
                "  ♕ ♘           \n" +
                "♙ ♙   ♗ ♙ ♙ ♙ ♙ \n" +
                "♖       ♔ ♗ ♘ ♖ \n");

		Piece king = board.getPiece(4, 0).get();
		Piece rook = board.getPiece(0, 0).get();
		Move castlingMove = new CastlingMove(king, 4, 0, 2, 0, rook, 0, 0, 3, 0);
		board.doMove(castlingMove);
		board.undoMove(castlingMove);
		assertThat(board.getPiece(2, 0)).isEmpty();
		assertThat(board.getPiece(3, 0)).isEmpty();
		assertThat(board.getPiece(4, 0)).isPresent().get().isEqualTo(king);
		assertThat(board.getPiece(0, 0)).isPresent().get().isEqualTo(rook);
	}
	
	@Test
	public void undoMove_enPassantMove_pawnRepositioned() {
		Board board = new Board("" +
				"♜ ♞ ♝   ♚ ♝   ♜ \n" +
				"♟     ♟ ♞ ♟ ♟ ♟ \n" +
				"    ♟           \n" +
				"♙ ♟             \n" +
				"      ♛         \n" +
				"  ♕ ♘           \n" +
				"  ♙   ♗ ♙ ♙ ♙ ♙ \n" +
				"♖       ♔ ♗ ♘ ♖ \n");
		Piece whitePawn = board.getPiece(0, 4).get();
		Piece blackPawn = board.getPiece(1, 4).get();
		
		Move move = new Move(whitePawn, 0, 4, 1, 5);
        move.setTookPiece(blackPawn);
        EnPassantMove enPassantMove = new EnPassantMove(move, 1, 4); 
        board.doMove(enPassantMove);
        
        board.undoMove(enPassantMove);
        
        assertThat(board.getPiece(0, 4)).isPresent().get().isEqualTo(whitePawn);
        assertThat(board.getPiece(1, 5)).isEmpty();
        assertThat(board.getPiece(1, 4)).isPresent().get().isEqualTo(blackPawn);
	}
}
