package ch.teemoo.bobby.models.moves;

import ch.teemoo.bobby.models.Board;
import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.pieces.Piece;
import java.util.Objects;

public class Move {
  private /*@ spec_public @*/ final Piece piece;
  private /*@ spec_public @*/ final int fromX;
  private /*@ spec_public @*/ final int fromY;
  private /*@ spec_public @*/ final int toX;
  private /*@ spec_public @*/ final int toY;
  private /*@ spec_public @*/ Piece tookPiece;
  private /*@ spec_public @*/ boolean check;
  
  //@ public invariant piece != null;
  //@ public invariant 0 <= fromX && fromX <= 7;
  //@ public invariant 0 <= fromY && fromY <= 7;
  //@ public invariant 0 <= toX && toX <= 7;
  //@ public invariant 0 <= toY && toY <= 7;
  //@ public invariant fromX != toX || fromY != toY;
  //@ public invariant tookPiece != null ==> tookPiece.getColor() != piece.getColor();

  //@ ensures this.piece == piece && this.fromX == fromX && this.fromY == fromY && this.toX == toX && this.toY == toY;
  public Move(Piece piece, int fromX, int fromY, int toX, int toY) {
    this.piece = piece;
    this.fromX = fromX;
    this.fromY = fromY;
    this.toX = toX;
    this.toY = toY;
    //this.tookPiece = null;
  }

  //@ ensures \result == piece;
  //@ pure
  public Piece getPiece() {
    return piece;
  }

  //@ ensures \result == fromX;
  //@ pure
  public int getFromX() {
    return fromX;
  }

  //@ ensures \result == fromY;
  //@ pure
  public int getFromY() {
    return fromY;
  }

  //@ ensures \result == toX;
  //@ pure
  public int getToX() {
    return toX;
  }

  //@ ensures \result == toY;
  //@ pure
  public int getToY() {
    return toY;
  }

  //@ ensures \result == (tookPiece != null);
  //@ pure
  public boolean isTaking() {
    return tookPiece != null;
  }

  //@ ensures \result == tookPiece;
  //@ pure
  public Piece getTookPiece() {
    return tookPiece;
  }

  //@ ensures this.tookPiece == tookPiece;
  public void setTookPiece(Piece tookPiece) {
    this.tookPiece = tookPiece;
  }

  //@ ensures \result == check;
  //@ pure
  public boolean isChecking() {
    return check;
  }

  //@ ensures this.check == checking;
  public void setChecking(boolean checking) {
    check = checking;
  }

  public String getPrettyNotation() {
    StringBuilder builder = new StringBuilder().append(piece.getColor())
        .append(' ')
        .append(getBasicNotation())
        .append(" (")
        .append(piece.getClass().getSimpleName())
        .append(')');
    return builder.toString();
  }

  public String getBasicNotation() {
    StringBuilder builder = new StringBuilder();
    builder.append(convertXToChar(fromX))
        .append(fromY + 1)
        .append(isTaking() ? "x" : "-")
        .append(convertXToChar(toX))
        .append(toY + 1);

    if (check) {
      builder.append('+');
    }
    return builder.toString();
  }
  
  public static Move fromBasicNotation(String notation, Color color, Board board) {
    if (notation == null || color == null) {
      throw new IllegalArgumentException(
          "Unexpected format for basic notation move: " + notation + " (" + color + ")");
    }

    Move move;
    if (notation.contains("0-0-0")) {
      int y = color == Color.WHITE ? 0 : 7;
      Piece king = board.getPiece(4, y)
          .orElseThrow(() -> new RuntimeException("There is no king at (4, " + y + ")"));
      Piece rook = board.getPiece(0, y)
          .orElseThrow(() -> new RuntimeException("There is no rook at (0, " + y + ")"));
      move = new CastlingMove(king, 4, y, 2, y, rook, 0, y, 3, y);

      if (notation.indexOf('+') > -1) {
        move.setChecking(true);
      }
      return move;
    } else if (notation.contains("0-0")) {
      int y = color == Color.WHITE ? 0 : 7;
      Piece king = board.getPiece(4, y)
          .orElseThrow(() -> new RuntimeException("There is no king at (4, " + y + ")"));
      Piece rook = board.getPiece(7, y)
          .orElseThrow(() -> new RuntimeException("There is no rook at (7, " + y + ")"));
      move = new CastlingMove(king, 4, y, 6, y, rook, 7, y, 5, y);

      if (notation.indexOf('+') > -1) {
        move.setChecking(true);
      }
      return move;
    }

    if (notation.length() < 5) {
      throw new IllegalArgumentException("Unexpected format for basic notation move: " + notation);
    }
    char fromXChar = notation.charAt(0);
    char fromYChar = notation.charAt(1);
    char takingChar = notation.charAt(2);
    char toXChar = notation.charAt(3);
    char toYChar = notation.charAt(4);

    int fromX = convertCharToX(fromXChar);
    int fromY = Character.getNumericValue(fromYChar) - 1;
    int toX = convertCharToX(toXChar);
    int toY = Character.getNumericValue(toYChar) - 1;

    Piece moved = board.getPiece(fromX, fromY)
        .orElseThrow(() -> new RuntimeException(
            "There should be a piece at (" + fromX + "," + fromY + ") but there is none!"));

    move = new Move(moved, fromX, fromY, toX, toY);

    if (notation.indexOf('+') > -1) {
      move.setChecking(true);
    }

    if (takingChar == 'x') {
      // mark the move as taking
      move.setTookPiece(board.getPiece(toX, toY)
          .orElseThrow(() -> new RuntimeException(
              "There should be a piece at (" + toX + "," + toY + ") but there is none!")));
    }

    return move;
  }

  public static String convertXToChar(int x) {
    final int aAscii = (int) 'a';
    return String.valueOf((char) (aAscii + x));
  }

  public static int convertCharToX(char character) {
    final int aAscii = (int) 'a';
    final int charAscii = (int) character;
    return charAscii - aAscii;
  }

  //@ requires move != null;
  //@ ensures \result <==> fromX == move.fromX && fromY == move.fromY && toX == move.toX && toY == move.toY;
  public boolean equalsForPositions(Move move) {
    return fromX == move.fromX && fromY == move.fromY && toX == move.toX && toY == move.toY;
  }

  @Override
  public int hashCode() {
    return Objects.hash(fromX, fromY, check, piece, toX, toY, tookPiece);
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }
    Move move = (Move) o;
    return equalsForPositions(move) && tookPiece == move.tookPiece && check == move.check
        && Objects.equals(piece, move.piece);
  }

  @Override
  public String toString() {
    return getPrettyNotation();
  }
}
