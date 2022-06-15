package ch.teemoo.bobby.models.pieces;

import ch.teemoo.bobby.models.Color;
import java.util.Objects;

public abstract class Piece {
  protected final Color color;
  protected final int value;
  protected final String whiteChar;
  protected final String blackChar;

  public Piece(Color color, int value, String whiteChar, String blackChar) {
    super();
    this.color = color;
    this.value = value;
    this.whiteChar = whiteChar;
    this.blackChar = blackChar;
  }

  public String getUnicode() {
    String unicode;
    if (color == Color.WHITE) {
      unicode = whiteChar;
    } else {
      unicode = blackChar;
    }
    return unicode;
  }

  public Color getColor() {
    return color;
  }

  public int getValue() {
    return value;
  }

  @Override
  public String toString() {
    return this.color + " " + this.getClass().getSimpleName();
  }

  public abstract Piece copy();

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
