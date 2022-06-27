package ch.teemoo.bobby.services;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatRuntimeException;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.moves.CastlingMove;
import ch.teemoo.bobby.models.moves.EnPassantMove;
import ch.teemoo.bobby.models.moves.PromotionMove;
import ch.teemoo.bobby.models.pieces.Bishop;
import ch.teemoo.bobby.models.pieces.Knight;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Queen;
import ch.teemoo.bobby.models.pieces.Rook;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import org.mockito.Spy;
import org.mockito.junit.jupiter.MockitoExtension;

@ExtendWith(MockitoExtension.class)
public class PortableGameNotationServiceTest {
  private static final String PGN_OPENING_RUY_LOPEZ_CONTENT = "[Event \"?\"]\n"
      + "[Site \"?\"]\n"
      + "[Date \"????.??.??\"]\n"
      + "[Round \"?\"]\n"
      + "[White \"?\"]\n"
      + "[Black \"?\"]\n"
      + "[Result \"*\"]\n"
      + "s2 \"Should_be_skipped\"]\n"
      + "\n"
      + "1. e4 e5 2. Nf3 Nc6 3. Bb5 *";

  private static final String PGN_GAME_CONTENT = "[Event \"F/S Return Match\"]\n"
      + "[Site \"Belgrade, Serbia JUG\"]\n"
      + "[Date \"1992.11.04\"]\n"
      + "[Round \"29\"]\n"
      + "[White \"Fischer, Robert J.\"]\n"
      + "[Black \"Spassky, Boris V.\"]\n"
      + "[Result \"1/2-1/2\"]\n"
      + "\n"
      + "1. e4 e5 2. Nf3 Nc6 3. Bb5 a6 {This opening is called the Ruy Lopez.}\n"
      + "4. Ba4 Nf6 5. O-O Be7 6. Re1 b5 7. Bb3 d6 8. c3 O-O 9. h3 Nb8 10. d4 Nbd7\n"
      + "11. c4 c6 12. cxb5 axb5 13. Nc3 Bb7 14. Bg5 b4 15. Nb1 h6 16. Bh4 c5 17. dxe5\n"
      + "Nxe4 18. Bxe7 Qxe7 19. exd6 Qf6 20. Nbd2 Nxd6 21. Nc4 Nxc4 22. Bxc4 Nb6\n"
      + "23. Ne5 Rae8 24. Bxf7+ Rxf7 25. Nxf7 Rxe1+ 26. Qxe1 Kxf7 27. Qe3 Qg5 28. Qxg5\n"
      + "hxg5 29. b3 Ke6 30. a3 Kd6 31. axb4 cxb4 32. Ra5 Nd5 33. f3 Bc8 34. Kf2 Bf5\n"
      + "35. Ra7 g6 36. Ra6+ Kc5 37. Ke1 Nf4 38. g3 Nxh3 39. Kd2 Kb5 40. Rd6 Kc5 41. Ra6\n"
      + "Nf2 42. g4 Bd3 43. Re6 1/2-1/2";

  private static final String PGN_GAME_WORLD_CHAMPIONSHIP_CONTENT = 
      "[Event \"World Championship 28th\"]\n"
      + "[Site \"Reykjavik\"]\n"
      + "[Date \"1972.??.??\"]\n"
      + "[Round \"13\"]\n"
      + "[White \"Spassky, Boris V\"]\n"
      + "[Black \"Fischer, Robert James\"]\n"
      + "[Result \"0-1\"]\n"
      + "[WhiteElo \"2660\"]\n"
      + "[BlackElo \"2785\"]\n"
      + "[ECO \"B04\"]\n"
      + "\n"
      + "1.e4 Nf6 2.e5 Nd5 3.d4 d6 4.Nf3 g6 5.Bc4 Nb6 6.Bb3 Bg7 7.Nbd2 O-O 8.h3 a5\n"
      + "9.a4 dxe5 10.dxe5 Na6 11.O-O Nc5 12.Qe2 Qe8 13.Ne4 Nbxa4 14.Bxa4 Nxa4 15.Re1 Nb6\n"
      + "16.Bd2 a4 17.Bg5 h6 18.Bh4 Bf5 19.g4 Be6 20.Nd4 Bc4 21.Qd2 Qd7 22.Rad1 Rfe8\n"
      + "23.f4 Bd5 24.Nc5 Qc8 25.Qc3 e6 26.Kh2 Nd7 27.Nd3 c5 28.Nb5 Qc6 29.Nd6 Qxd6\n"
      + "30.exd6 Bxc3 31.bxc3 f6 32.g5 hxg5 33.fxg5 f5 34.Bg3 Kf7 35.Ne5+ Nxe5 36.Bxe5 b5\n"
      + "37.Rf1 Rh8 38.Bf6 a3 39.Rf4 a2 40.c4 Bxc4 41.d7 Bd5 42.Kg3 Ra3+ 43.c3 Rha8\n"
      + "44.Rh4 e5 45.Rh7+ Ke6 46.Re7+ Kd6 47.Rxe5 Rxc3+ 48.Kf2 Rc2+ 49.Ke1 Kxd7 50.Rexd5+ Kc6\n"
      + "51.Rd6+ Kb7 52.Rd7+ Ka6 53.R7d2 Rxd2 54.Kxd2 b4 55.h4 Kb5 56.h5 c4 57.Ra1 gxh5\n"
      + "58.g6 h4 59.g7 h3 60.Be7 Rg8 61.Bf8 h2 62.Kc2 Kc6 63.Rd1 b3+ 64.Kc3 h1=Q\n"
      + "65.Rxh1 Kd5 66.Kb2 f4 67.Rd1+ Ke4 68.Rc1 Kd3 69.Rd1+ Ke2 70.Rc1 f3 71.Bc5 Rxg7\n"
      + "72.Rxc4 Rd7 73.Re4+ Kf1 74.Bd4 f2  0-1\n";

  private static final String PGN_ENPASSANT_CHECK_CONTENT = 
      "[Event \"Pietzcker Christmas Tournament\"]\n"
      + "[Site \"Melbourne AUS\"]\n"
      + "[Date \"1928.??.??\"]\n"
      + "[EventDate \"?\"]\n"
      + "[Round \"?\"]\n"
      + "[Result \"1-0\"]\n"
      + "[White \"Gunnar Gundersen\"]\n"
      + "[Black \"A H Faul\"]\n"
      + "[ECO \"C02\"]\n"
      + "[WhiteElo \"?\"]\n"
      + "[BlackElo \"?\"]\n"
      + "[PlyCount \"29\"]\n"
      + "\n"
      + "1. e4 e6 2. d4 d5 3. e5 c5 4. c3 cxd4 5. cxd4 Bb4+ 6. Nc3 Nc6\n"
      + "7. Nf3 Nge7 8. Bd3 O-O 9. Bxh7+ Kxh7 10. Ng5+ Kg6 11. h4 Nxd4\n"
      + "12. Qg4 f5 13. h5+ Kh6 14. Nxe6+ g5 15. hxg6#  1-0";

  private static final String PGN_PROMOTION_6KNIGHTS_CONTENT = "[Event \"Live Chess\"]\n"
      + "[Site \"Chess.com\"]\n"
      + "[Date \"2022.05.27\"]\n"
      + "[Round \"?\"]\n"
      + "[White \"Buchtel6\"]\n"
      + "[Black \"Orciety\"]\n"
      + "[Result \"0-1\"]\n"
      + "[ECO \"D00\"]\n"
      + "[WhiteElo \"1371\"]\n"
      + "[BlackElo \"1407\"]\n"
      + "[TimeControl \"180\"]\n"
      + "[EndTime \"15:41:04 PDT\"]\n"
      + "[Termination \"Orciety won by checkmate\"]\n"
      + "\n"
      + "1. d2d4 d5 2. Bf4 c5 3. Nf3 Nc6 4. c3 Qb6 5. Qc2 cxd4 6. cxd4 Nxd4 7. Nxd4 Qxd4 8.\n"
      + "e3 Qb6 9. Nc3 Nf6 10. Bb5+ Bd7 11. Bxd7+ Kxd7 12. O-O Rc8 13. Qd2 e6 14. Bg5 Be7\n"
      + "15. Rfd1 h6 16. Bh4 g5 17. Bg3 Nh5 18. Be5 f6 19. Bd4 Qb4 20. a3 Qb3 21. f3 b6\n"
      + "22. e4 e5 23. Bf2 d4 24. Nd5 Rc2 25. Qe1 Qxb2 26. Nxe7 Kxe7 27. Rdb1 Qc3 28.\n"
      + "Qxc3 Rxc3 29. Rb4 Nf4 30. g3 Nd3 31. a4 Nxb4 32. Rb1 Nd3 33. a5 Rc1+ 34. Rxc1\n"
      + "Nxc1 35. axb6 axb6 36. Kf1 b5 37. Ke1 Nd3+ 38. Kd2 Nxf2 39. Kc2 Rc8+ 40. Kb3\n"
      + "Rc3+ 41. Kb4 Rxf3 42. Kxb5 Rxg3 43. Kc5 Rg2 44. Kd5 Rxh2 45. Kc6 Nxe4 46. Kd5\n"
      + "Ng3 47. Kc5 d3 48. Kc4 d2 49. Kc3 d1=N+ 50. Kb3 Rd2 51. Ka4 Rc2 52. Ka5 Kd6 53.\n"
      + "Ka6 Rb2 54. Ka5 Kc5 55. Ka4 Rb4+ 56. Ka3 h5 57. Ka2 h4 58. Ka3 h3 59. Ka2 h2 60.\n"
      + "Ka1 h1=N 61. Ka2 e4 62. Ka3 e3 63. Ka2 Ndf2 64. Ka1 Nf1 65. Ka2 Nh3 66. Ka3 Ng1\n"
      + "67. Ka2 e2 68. Ka1 e1=N 69. Ka2 f5 70. Ka3 Nd2 71. Ka2 f4 72. Ka1 f3 73. Ka2 f2\n"
      + "74. Ka3 f1=N 75. Ka2 g4 76. Ka1 Ngf3 77. Ka2 g3 78. Ka3 g2 79. Ka2 g1=N 80. Ka1\n"
      + "Ne4 81. Ka2 Ng2 82. Ka3 Rb3+ 83. Ka2 Rb2+ 84. Ka1 Nhf2 85. Kxb2 Nfe3 86. Kb1 Ne2\n"
      + "87. Kb2 Nge1 88. Kb3 Ned2+ 89. Kb2 Nfd3+ 90. Ka3 Nfd4 91. Ka4 N1c2 92. Ka5 N2b3+\n"
      + "93. Ka6 Kc6 94. Ka7 Kc7 95. Ka6 Ncb4+ 96. Ka7 Ned5 97. Ka8 Ng3 98. Ka7 Nh1 99.\n"
      + "Ka8 N3f4 100. Ka7 Ng6 101. Ka8 Nh8 102. Ka7 Nb5+ 103. Ka8 Nb6# 0-1";

  private PortableGameNotationService portableGameNotationService;

  @Spy
  private MoveService moveService;

  @BeforeEach
  void setup() {
    this.moveService = new MoveService();
    this.portableGameNotationService = new PortableGameNotationService(moveService);
  }

  @Test
  void readPgnFile_openingRuyLopez_returnBoardCurrentSituation() {
    // given
    List<String> lines = Arrays.asList(PGN_OPENING_RUY_LOPEZ_CONTENT.split("\\n"));

    // when
    Game game = portableGameNotationService.readPgnFile(lines);

    // then
    // headers check
    assertThat(game.getWhitePlayer()).isNotNull();
    assertThat(game.getWhitePlayer().getName()).isEqualTo("?");
    assertThat(game.getBlackPlayer()).isNotNull();
    assertThat(game.getBlackPlayer().getName()).isEqualTo("?");

    // moves check
    assertThat(game.getHistory()).hasSize(5);
    assertThat(game.getHistory().get(0).toString()).isEqualTo("WHITE e2-e4 (Pawn)");
    assertThat(game.getHistory().get(4).toString()).isEqualTo("WHITE f1-b5 (Bishop)");
  }

  @Test
  void readPgnFile_gameDraw_returnBoardCurrentSituation() throws IOException {
    // given
    List<String> lines = Arrays.asList(PGN_GAME_CONTENT.split("\\n"));

    // when
    Game game = portableGameNotationService.readPgnFile(lines);

    // then
    // headers check
    assertThat(game.getWhitePlayer()).isNotNull();
    assertThat(game.getWhitePlayer().getName()).isEqualTo("Fischer, Robert J.");
    assertThat(game.getBlackPlayer()).isNotNull();
    assertThat(game.getBlackPlayer().getName()).isEqualTo("Spassky, Boris V.");

    // moves check
    assertThat(game.getHistory()).hasSize(85);

    assertThat(game.getHistory().get(0).getPiece()).isInstanceOf(Pawn.class);
    assertThat(game.getHistory().get(0).getPiece().getColor()).isEqualTo(Color.WHITE);
    assertThat(game.getHistory().get(0).getToY()).isEqualTo(3);

    assertThat(game.getHistory().get(1).getPiece()).isInstanceOf(Pawn.class);
    assertThat(game.getHistory().get(1).getPiece().getColor()).isEqualTo(Color.BLACK);
    assertThat(game.getHistory().get(1).getToY()).isEqualTo(4);

    assertThat(game.getHistory().get(8)).isInstanceOf(CastlingMove.class);
    assertThat(game.getHistory().get(8).getToX()).isEqualTo(6);

    assertThat(game.getHistory().get(34).getPiece()).isInstanceOf(Bishop.class);
    assertThat(game.getHistory().get(34).getPiece().getColor()).isEqualTo(Color.WHITE);
    assertThat(game.getHistory().get(34).isTaking()).isTrue();

    assertThat(game.getHistory().get(49).getPiece()).isInstanceOf(Rook.class);
    assertThat(game.getHistory().get(49).getPiece().getColor()).isEqualTo(Color.BLACK);
    assertThat(game.getHistory().get(49).isTaking()).isTrue();
    assertThat(game.getHistory().get(49).isChecking()).isTrue();
  }

  @Test
  void readPgnFile_longGame_returnBoardCurrentSituation() throws IOException {
    // given
    List<String> lines = Arrays.asList(PGN_GAME_WORLD_CHAMPIONSHIP_CONTENT.split("\\n"));

    // when
    Game game = portableGameNotationService.readPgnFile(lines);

    // then
    // headers check
    assertThat(game.getWhitePlayer()).isNotNull();
    assertThat(game.getWhitePlayer().getName()).isEqualTo("Spassky, Boris V");
    assertThat(game.getBlackPlayer()).isNotNull();
    assertThat(game.getBlackPlayer().getName()).isEqualTo("Fischer, Robert James");

    // moves check
    assertThat(game.getHistory()).hasSize(148);

    assertThat(game.getHistory().get(127).getPiece()).isInstanceOf(Pawn.class);
    assertThat(game.getHistory().get(127).getPiece().getColor()).isEqualTo(Color.BLACK);
    assertThat(game.getHistory().get(127).isTaking()).isFalse();
    assertThat(game.getHistory().get(127).isChecking()).isFalse();
    assertThat(game.getHistory().get(127)).isInstanceOf(PromotionMove.class);
    assertThat(((PromotionMove) game.getHistory().get(127)).getPromotedPiece())
        .isInstanceOf(Queen.class);
  }

  @Test
  void readPgnFile_enPassantMoveGame_returnBoardCurrentSituation() throws IOException {
    // given
    List<String> lines = Arrays.asList(PGN_ENPASSANT_CHECK_CONTENT.split("\\n"));

    // when
    Game game = portableGameNotationService.readPgnFile(lines);

    // then
    // headers check
    assertThat(game.getWhitePlayer()).isNotNull();
    assertThat(game.getWhitePlayer().getName()).isEqualTo("Gunnar Gundersen");
    assertThat(game.getBlackPlayer()).isNotNull();
    assertThat(game.getBlackPlayer().getName()).isEqualTo("A H Faul");

    // moves check
    assertThat(game.getHistory()).hasSize(29);

    assertThat(game.getHistory().get(28).getPiece()).isInstanceOf(Pawn.class);
    assertThat(game.getHistory().get(28).getPiece().getColor()).isEqualTo(Color.WHITE);
    assertThat(game.getHistory().get(28).isTaking()).isTrue();
    assertThat(game.getHistory().get(28).isChecking()).isTrue();
    assertThat(game.getHistory().get(28)).isInstanceOf(EnPassantMove.class);
  }

  @Test
  void readPgnFile_6KnightsGame_returnBoardCurrentSituation() throws IOException {
    // given
    List<String> lines = Arrays.asList(PGN_PROMOTION_6KNIGHTS_CONTENT.split("\\n"));

    // when
    Game game = portableGameNotationService.readPgnFile(lines);

    // then
    // headers check
    assertThat(game.getWhitePlayer()).isNotNull();
    assertThat(game.getBlackPlayer()).isNotNull();

    // moves check
    assertThat(game.getHistory()).hasSize(206);

    assertThat(game.getHistory().get(97).getPiece()).isInstanceOf(Pawn.class);
    assertThat(game.getHistory().get(97).getPiece().getColor()).isEqualTo(Color.BLACK);
    assertThat(game.getHistory().get(97).isTaking()).isFalse();
    assertThat(game.getHistory().get(97).isChecking()).isTrue();
    assertThat(game.getHistory().get(97)).isInstanceOf(PromotionMove.class);
    assertThat(((PromotionMove) game.getHistory().get(97)).getPromotedPiece())
        .isInstanceOf(Knight.class);

    assertThat(game.getBoard().getPiece(7, 7)).isPresent().get().isInstanceOf(Knight.class);

  }

  @ParameterizedTest
  @ValueSource(strings = {
      "[Event \"?\"]\n"
          + "[Site \"?\"]\n"
          + "[Date \"????.??.??\"]\n"
          + "[Round \"?\"]\n"
          + "[White \"?\"]\n"
          + "[Black \"?\"]\n"
          + "[Result \"*\"]\n"
          + "\n"
          + "1. O-O-O O-O-O 2. e8=R e1=K 3. d8=B *",
      "[Event \"?\"]\n"
          + "[Site \"?\"]\n"
          + "[Date \"????.??.??\"]\n"
          + "[Round \"?\"]\n"
          + "[White \"?\"]\n"
          + "[Black \"?\"]\n"
          + "[Result \"*\"]\n"
          + "\n"
          + "1. e4 c5 2. d4 cxd4 3. Qxd4 Nc6 4. Qd1 Nf6 5. Nd2 d5 6. exd5 Nxd5 7. Nf3 Bf5 *",
      "[Event \"?\"]\n"
          + "[Site \"?\"]\n"
          + "[Date \"????.??.??\"]\n"
          + "[Round \"?\"]\n"
          + "[White \"?\"]\n"
          + "[Black \"?\"]\n"
          + "[Result \"*\"]\n"
          + "\n"
          + "1. e4 c9 2. d4 cxd4 3. Qxd4 Nc6 4. Qd1 Nf6 5. Nd2 d5 6. exd5 Nxd5 7. Nf3 Bf5 *" })
  void testUnexpectedMove(String pgn) throws IOException {
    // given
    List<String> lines = Arrays.asList(pgn.split("\\n"));

    // then
    assertThatRuntimeException().isThrownBy(() -> portableGameNotationService.readPgnFile(lines));
  }

}
