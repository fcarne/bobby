package ch.teemoo.bobby.models;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.jupiter.api.Test;

import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.pieces.Pawn;

class MoveAnalysisTest {

	@Test
	void constructor_ok_returnOk() {
		Move move = new Move(new Pawn(Color.WHITE),0,1,0,2);
		Move next = new Move(new Pawn(Color.WHITE),1,1,1,2);
		MoveAnalysis moveAnalysis = new MoveAnalysis(move);
		moveAnalysis.setScore(0);
		moveAnalysis.setNextProbableMove(new MoveAnalysis(next));
		
		assertThat(moveAnalysis.getMove()).isEqualTo(move);
		assertThat(moveAnalysis.getScore()).isZero();
		assertThat(moveAnalysis.getNextProbableMove().getMove()).isEqualTo(next);
	}

}
