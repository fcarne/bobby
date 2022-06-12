package ch.teemoo.bobby.models.games;

public enum GameState {
	IN_PROGRESS, LOSS, DRAW_STALEMATE, DRAW_THREEFOLD, DRAW_50_MOVES, DRAW_AGREEMENT;

	public boolean isDraw() {
		return this == DRAW_50_MOVES || this == DRAW_THREEFOLD || this == DRAW_STALEMATE || this == DRAW_AGREEMENT;
	}

	public boolean isLost() {
		return this == LOSS;
	}

	public boolean isInProgress() {
		return this == IN_PROGRESS;
	}

	public String getDrawDescription() {
		assert isDraw();
		switch (this) {
		case DRAW_STALEMATE:
			return "Stalemate";
		case DRAW_50_MOVES:
			return "50 moves";
		case DRAW_AGREEMENT:
			return "aggreement";
		default:
			assert this == DRAW_THREEFOLD;
			return "threefold";
		}
	}
}
