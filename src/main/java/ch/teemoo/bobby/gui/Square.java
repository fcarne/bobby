package ch.teemoo.bobby.gui;

import ch.teemoo.bobby.models.Position;
import ch.teemoo.bobby.models.pieces.Piece;
import java.awt.Font;
import javax.swing.JLabel;

public class Square extends JLabel {
  private static final long serialVersionUID = 3293244645639553936L;
  private Piece piece;
  private final Position position;

  Square(Piece piece, Position position, Background background, Font font) {
    super(getPieceText(piece));
    this.piece = piece;
    this.position = position;
    setFont(font);
    setOpaque(true);
    setHorizontalAlignment(CENTER);
    setBackground(background.getColor());
  }

  public Piece getPiece() {
    return piece;
  }

  public void setPiece(Piece piece) {
    this.piece = piece;
    this.setText(getPieceText(piece));
  }

  public Position getPosition() {
    return position;
  }

  private static String getPieceText(Piece piece) {
    return piece != null ? piece.getUnicode() : "";
  }
}
