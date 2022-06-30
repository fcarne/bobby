package ch.teemoo.bobby.models;

import ch.teemoo.bobby.models.moves.CastlingMove;
import ch.teemoo.bobby.models.moves.EnPassantMove;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.moves.PromotionMove;
import ch.teemoo.bobby.models.pieces.Piece;
import java.util.Optional;

public class Board {
  public static final int SIZE = 8;

  private /*@ spec_public @*/ final Piece[][] pieces;

  //@ public invariant pieces != null;
  //@ public invariant pieces.length == SIZE && pieces[0].length == SIZE;
  
  //@ requires board != null;
  //@ ensures pieces == board;
  public Board(Piece[][] board) {
    this.pieces = board.clone();
  }

  public Board(String representation) {
    this.pieces = fromString(representation);
  }

  //@ ensures \result == pieces;
  public Piece[][] getBoard() {
    return pieces.clone();
  }

  //@ requires 0 <= x <= 7;
  //@ requires 0 <= y <= 7;
  //@ ensures !\result.isPresent() <==> pieces[y][x] == null;
  //@ ensures \result.get() == pieces[y][x];
  public Optional<Piece> getPiece(int x, int y) {
    return Optional.ofNullable(pieces[y][x]);
  }

  @Override
  public String toString() {
    StringBuilder builder = new StringBuilder();
    for (int i = SIZE - 1; i >= 0; i--) {
      for (int j = 0; j < SIZE; j++) {
        Optional<Piece> piece = getPiece(j, i);

        if (piece.isPresent()) {
          builder.append(piece.get().getUnicode());
        } else {
          builder.append(' ');
        }
        
        builder.append(' ');
      }
      builder.append('\n');
    }
    return builder.toString();
  }

  //@ ensures (\forall int i; 0 <= i && i < SIZE; (\forall int j; 0 <= j && j < SIZE; pieces[i][j] == \result.pieces[i][j]));
  public Board copy() {
    Board clone = new Board(new Piece[SIZE][SIZE]);
    for (int i = 0; i < SIZE; i++) {
      for (int j = 0; j < SIZE; j++) {
        Optional<Piece> piece = getPiece(i, j);
        if (piece.isPresent()) {
          clone.setPiece(i, j, piece.get().copy());
        }
      }
    }
    return clone;
  }

  //@ requires move != null;
  //@ ensures pieces[move.getFromX()][move.getFromY()] == null;
  //@ ensures pieces[move.getToX()][move.getToY()] == \old(pieces[move.getFromX()][move.getFromY()]);
  //@ ensures move instanceof PromotionMove ==> pieces[move.getFromX()][move.getFromY()] == ((PromotionMove) move).getPromotedPiece();
  //@ ensures !(move instanceof PromotionMove) ==> pieces[move.getFromX()][move.getFromY()] == move.getPiece();
  //@ ensures move instanceof EnPassantMove ==> pieces[((EnPassantMove)move).getTookPiecePosX()][((EnPassantMove)move).getTookPiecePosY()] == null;
  //@ ensures move instanceof CastlingMove ==> pieces[((CastlingMove)move).getRookFromX()][((CastlingMove)move).getRookFromY()] == null;
  //@ ensures move instanceof CastlingMove ==> pieces[((CastlingMove)move).getRookToX()][((CastlingMove)move).getRookToY()] == \old(pieces[((CastlingMove)move).getRookFromX()][((CastlingMove)move).getRookFromY()]);
  public void doMove(Move move) {
    removePiece(move.getFromX(), move.getFromY());
    Piece piece = move.getPiece();

    if (move instanceof PromotionMove) {
      PromotionMove promotionMove = (PromotionMove) move;
      piece = promotionMove.getPromotedPiece();
    }

    setPiece(move.getToX(), move.getToY(), piece);

    if (move instanceof CastlingMove) {
      CastlingMove castlingMove = (CastlingMove) move;
      removePiece(castlingMove.getRookFromX(), castlingMove.getRookFromY());
      setPiece(castlingMove.getRookToX(), castlingMove.getRookToY(), castlingMove.getRook());
    } else if (move instanceof EnPassantMove) {
      EnPassantMove enPassantMove = (EnPassantMove) move;
      removePiece(enPassantMove.getTookPiecePosX(), enPassantMove.getTookPiecePosY());
    }
  }

  //@ requires move != null;
  //@ ensures pieces[move.getFromX()][move.getFromY()] == move.getPiece();
  //@ ensures pieces[move.getFromX()][move.getFromY()] == \old(pieces[move.getToX()][move.getToY()]);
  //@ ensures !move.isTaking() ==> pieces[move.getToX()][move.getToY()] == null;
  //@ ensures move.isTaking() && move instanceof EnPassantMove ==> pieces[((EnPassantMove)move).getTookPiecePosX()][((EnPassantMove)move).getTookPiecePosY()] == move.getTookPiece();
  //@ ensures move.isTaking() && !(move instanceof EnPassantMove) ==> pieces[move.getToX()][move.getToY()] == move.getTookPiece();
  //@ ensures move instanceof CastlingMove ==> pieces[((CastlingMove)move).getRookFromX()][((CastlingMove)move).getRookFromY()] == null;
  //@ ensures move instanceof CastlingMove ==> pieces[((CastlingMove)move).getRookToX()][((CastlingMove)move).getRookToY()] == \old(pieces[((CastlingMove)move).getRookFromX()][((CastlingMove)move).getRookFromY()]);
  public void undoMove(Move move) {
    removePiece(move.getToX(), move.getToY());
    Piece piece = move.getPiece();
    setPiece(move.getFromX(), move.getFromY(), piece);

    if (move.isTaking()) {
      if (move instanceof EnPassantMove) {
        EnPassantMove enPassantMove = (EnPassantMove) move;
        setPiece(enPassantMove.getTookPiecePosX(), enPassantMove.getTookPiecePosY(),
            enPassantMove.getTookPiece());
      } else {
        setPiece(move.getToX(), move.getToY(), move.getTookPiece());
      }
    }

    if (move instanceof CastlingMove) {
      CastlingMove castlingMove = (CastlingMove) move;
      removePiece(castlingMove.getRookToX(), castlingMove.getRookToY());
      setPiece(castlingMove.getRookFromX(), castlingMove.getRookFromY(), castlingMove.getRook());
    }
  }

  //@ requires 0 <= x <= 7;
  //@ requires 0 <= y <= 7;
  //@ requires piece != null;
  //@ ensures pieces[y][x] == piece;
  private void setPiece(int x, int y, Piece piece) {
    pieces[y][x] = piece;
  }

  //@ requires 0 <= x <= 7;
  //@ requires 0 <= y <= 7;
  //@ ensures pieces[y][x] == null;
  private void removePiece(int x, int y) {
    //Optional<Piece> toRemove = getPiece(x, y);
    pieces[y][x] = null;
    //return toRemove;
  }

  private Piece[][] fromString(String value) {
    Piece[][] pieces = new Piece[SIZE][SIZE];
    String[] lines = value.split("\n");
    //@ assert lines.length == SIZE;

    for (int i = 0; i < SIZE; i++) {
      String line = lines[i];
      // Every piece is followed by a space, just ignore the spaces
      for (int j = 0; j < SIZE; j++) {
        char c = line.charAt(2 * j);
        if (c != ' ') {
          pieces[SIZE - 1 - i][j] = Piece.fromUnicodeChar(c);
        }
      }
    }
    return pieces;
  }
}
