package ch.teemoo.bobby.models;

public class Position {
  private final int file;
  private final int rank;

  //@ requires 0 <= file <= 7;
  //@ requires 0 <= rank <= 7;
  //@ ensures this.file == file && this.rank == rank;
  public Position(int file, int rank) {
    this.file = file;
    this.rank = rank;
  }

  //@ ensures \result == file;
  public int getFile() {
    return file;
  }

  //@ ensures \result == rank;
  public int getRank() {
    return rank;
  }
}
