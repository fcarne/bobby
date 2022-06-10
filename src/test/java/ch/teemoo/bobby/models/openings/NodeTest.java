package ch.teemoo.bobby.models.openings;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Optional;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Rook;

class NodeTest {

	Move move;
	Move childMove;

	@BeforeEach
	void setupMoves() {
		move = new Move(new Pawn(Color.WHITE), 0, 1, 0, 2);
		childMove = new Move(new Rook(Color.WHITE), 0, 0, 0, 1);
	}

	@Test
	void constructor_ok_returnsCorrect() {
		Node node = new Node(move);
		node.setOpeningName("Sicilian Defense");

		assertThat(node.getMove()).isEqualTo(move);
		assertThat(node.getChildren()).isEmpty();
		assertThat(node.getOpeningName()).isEqualTo("Sicilian Defense");

		Node childNode = new Node(childMove);
		node.addNode(childNode);

		assertThat(node.getChildren()).hasSize(1).first().isEqualTo(childNode);
	}

	@Test
	void getNodeForMove_exist_returnNode() {
		Node node = new Node(move);
		node.addNode(new Node(childMove));

		Optional<Node> childNode = node.getNodeForMove(childMove);
		assertThat(childNode).isPresent();
		assertThat(childNode.get().getMove()).isEqualTo(childMove);
	}

	@Test
	void getNodeForMove_notExist_returnNull() {
		Node node = new Node(move);
		node.addNode(new Node(childMove));

		Optional<Node> childNode = node.getNodeForMove(new Move(new Pawn(Color.WHITE), 1, 1, 1, 2));
		assertThat(childNode).isEmpty();
	}

}
