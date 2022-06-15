package ch.teemoo.bobby.models;

public class Position {
  private final int file;
  private final int rank;

  public Position(int file, int rank) {
    assert 0 <= file && file < 8;
    assert 0 <= rank && rank < 8;

    this.file = file;
    this.rank = rank;
  }

  public int getFile() {
    return file;
  }

  public int getRank() {
    return rank;
  }
}
