import models.Move;
import models.Position;
import models.pieces.Piece;

public class MoveFactory {
	private MoveFactory() {
	}

	public static Move createMove(Piece piece, Position from, Position to) {
		return new Move(piece, from.getX(), from.getY(), to.getX(), to.getY());
	}
}
