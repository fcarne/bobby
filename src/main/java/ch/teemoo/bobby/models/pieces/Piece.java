package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;
import java.util.Objects;

public abstract class Piece {
  protected /*@ spec_public @*/ final Color color;
  protected /*@ spec_public @*/ final int value;
  protected /*@ spec_public @*/ final String whiteChar;
  protected /*@ spec_public @*/ final String blackChar;
  
  //@ public invariant color != null;
  //@ public invariant whiteChar != blackChar;
  //@ public invariant value > 0;
  
  //@ requires value > 0 && whiteChar != blackChar && color != null;
  //@ ensures this.color == color && this.value == value && this.whiteChar == whiteChar && this.blackChar == blackChar;
  public Piece(Color color, int value, String whiteChar, String blackChar) {
    super();
    this.color = color;
    this.value = value;
    this.whiteChar = whiteChar;
    this.blackChar = blackChar;
  }

  //@ ensures \result == whiteChar <==> color == Color.WHITE;
  //@ ensures \result == blackChar <==> color == Color.BLACK;
  public String getUnicode() {
    String unicode;
    if (color == Color.WHITE) {
      unicode = whiteChar;
    } else {
      //@ assert color == Color.BLACK;
      unicode = blackChar;
    }
    return unicode;
  }

  //@ ensures \result == color;
  //@ pure
  public Color getColor() {
    return color;
  }

  //@ ensures \result == value;
  public int getValue() {
    return value;
  }

  @Override
  public String toString() {
    return this.color + " " + this.getClass().getSimpleName();
  }

  public abstract Piece copy();

  //@ ensures unicode == '♜' <==> \result.equals(new Rook(Color.BLACK)); 
  //@ ensures unicode == '♞' <==> \result.equals(new Knight(Color.BLACK));
  //...
  public static Piece fromUnicodeChar(final char unicode) {
    Piece piece;
    switch (unicode) {
      case '♜':
        piece = new Rook(Color.BLACK);
        break;
      case '♞':
        piece = new Knight(Color.BLACK);
        break;
      case '♝':
        piece = new Bishop(Color.BLACK);
        break;
      case '♛':
        piece = new Queen(Color.BLACK);
        break;
      case '♚':
        piece = new King(Color.BLACK);
        break;
      case '♟':
        piece = new Pawn(Color.BLACK);
        break;
      case '♖':
        piece = new Rook(Color.WHITE);
        break;
      case '♘':
        piece = new Knight(Color.WHITE);
        break;
      case '♗':
        piece = new Bishop(Color.WHITE);
        break;
      case '♕':
        piece = new Queen(Color.WHITE);
        break;
      case '♔':
        piece = new King(Color.WHITE);
        break;
      case '♙':
        piece = new Pawn(Color.WHITE);
        break;
      default:
        throw new IllegalArgumentException("Unexpected piece unicode: " + unicode);
    }
    return piece;
  }

  @Override
  public int hashCode() {
    return Objects.hash(color, value);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    Piece other = (Piece) obj;
    return color == other.color;
  }

}
