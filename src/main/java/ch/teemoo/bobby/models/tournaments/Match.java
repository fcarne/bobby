package ch.teemoo.bobby.models.tournaments;

import ch.teemoo.bobby.models.players.Player;

public class Match {
  private /*@ spec_public @*/ final Player player1;
  private /*@ spec_public @*/ final Player player2;
  private /*@ spec_public @*/ float scorePlayer1;
  private /*@ spec_public @*/ float scorePlayer2;
  private /*@ spec_public @*/ int playedGames;
  private /*@ spec_public @*/ int totalMoves;

  //@ public invariant player1 != null;
  //@ public invariant player2 != null;
  
  //@ requires player1 != null && player2 != null;
  //@ ensures this.player1 == player1 && this.player2 == player2;
  //@ ensures scorePlayer1 == 0 && scorePlayer2 == 0;
  //@ ensures playedGames == 0 && totalMoves == 0;  
  public Match(Player player1, Player player2) {
    this.player1 = player1;
    this.player2 = player2;
    this.scorePlayer1 = 0;
    this.scorePlayer2 = 0;
    this.playedGames = 0;
    this.totalMoves = 0;
  }

  //@ ensures \result == player1;
  public Player getPlayer1() {
    return player1;
  }

  //@ ensures \result == player2;
  public Player getPlayer2() {
    return player2;
  }

  //@ normal_behavior
  //@ requires player == player1 || player == player2;
  //@ ensures \result == scorePlayer1 <==> player == player1;
  //@ ensures \result == scorePlayer2 <==> player == player2;
  //@ also
  //@ exceptional_behavior
  //@ requires player != player1 && player != player2;
  //@ signals_only IllegalArgumentException;
  public float getScoreByPlayer(Player player) {
    if (player.equals(player1)) {
      return scorePlayer1;
    } else if (player.equals(player2)) {
      return scorePlayer2;
    } else {
      throw new IllegalArgumentException("Given player does not take part to this match");
    }
  }

  //@ ensures \result <==> player == player1 || player == player2;
  public boolean isPlayerTakingPartToTheMatch(Player player) {
    return player.equals(player1) || player.equals(player2);
  }

  //@ requires nbMoves > 0;
  //@ ensures scorePlayer1 == \old(scorePlayer1) + 0.5;
  //@ ensures scorePlayer2 == \old(scorePlayer2) + 0.5;
  public void addDraw(int nbMoves) {
    this.scorePlayer1 += 0.5;
    this.scorePlayer2 += 0.5;
    addGame(nbMoves);
  }

  //@ normal_behavior
  //@ requires nbMoves > 0;
  //@ requires player == player1 || player == player2;
  //@ ensures player == player1 ==> (scorePlayer1 == \old(scorePlayer1) + 1 && scorePlayer2 == \old(scorePlayer2));
  //@ ensures player == player2 ==> (scorePlayer2 == \old(scorePlayer2) + 1 && scorePlayer1 == \old(scorePlayer1));
  //@ also
  //@ exceptional_behavior
  //@ requires player != player1 && player != player2;
  //@ signals_only IllegalArgumentException;
  public void addWin(Player player, int nbMoves) {
    if (player.equals(player1)) {
      this.scorePlayer1 += 1;
    } else if (player.equals(player2)) {
      this.scorePlayer2 += 1;
    } else {
      throw new IllegalArgumentException("Player not found");
    }
    addGame(nbMoves);
  }

  public String toString() {
    return "Players: \t" + player1.getDescription() + " vs " + player2.getDescription() + "\n"
        + "Score:   \t" + scorePlayer1 + "-" + scorePlayer2 + "\n"
        + "Games:   \t" + playedGames + "\n"
        + "Moves:   \t" + totalMoves + "\n"
        + "Avg m/g: \t" + (float) totalMoves / (float) playedGames;
  }

  
  //@ requires nbMoves > 0;
  //@ ensures playedGames == \old(playedGames) + 1;
  //@ ensures totalMoves == \old(totalMoves) + nbMoves;
  private void addGame(int nbMoves) {
    this.playedGames++;
    this.totalMoves += nbMoves;
  }
}
