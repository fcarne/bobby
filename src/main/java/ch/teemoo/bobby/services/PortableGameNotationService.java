package ch.teemoo.bobby.services;

import static ch.teemoo.bobby.helpers.ColorHelper.swap;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.moves.CastlingMove;
import ch.teemoo.bobby.models.moves.EnPassantMove;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.moves.PromotionMove;
import ch.teemoo.bobby.models.pieces.Bishop;
import ch.teemoo.bobby.models.pieces.King;
import ch.teemoo.bobby.models.pieces.Knight;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.pieces.Piece;
import ch.teemoo.bobby.models.pieces.Queen;
import ch.teemoo.bobby.models.pieces.Rook;
import ch.teemoo.bobby.models.players.Human;
import ch.teemoo.bobby.models.players.Player;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import org.apache.commons.lang3.StringUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class PortableGameNotationService {
  private static final Logger LOGGER = LoggerFactory.getLogger(PortableGameNotationService.class);

  private final MoveService moveService;

  public PortableGameNotationService(MoveService moveService) {
    this.moveService = moveService;
  }

  public Game readPgnFile(List<String> lines) {
    // Separate headers from moves given an empty line
    String content = String.join("\n", lines);
    String[] contentSplit = content.split("\\n\\n");
    String headersContent = contentSplit[0];
    String movesContent = contentSplit[1];

    Map<String, String> headers = getHeadersMap(headersContent);

    Player whitePlayer = new Human(headers.getOrDefault("White", "?"));
    Player blackPlayer = new Human(headers.getOrDefault("Black", "?"));
    Game game = new Game(whitePlayer, blackPlayer);
    game.setOpening(headers.get("Opening"));

    movesContent = cleanMovesContent(movesContent);

    // Split into words
    String[] movesWords = movesContent.split("\\s+");

    List<Move> moves = new ArrayList<>();
    Color color = Color.WHITE;

    for (String word : movesWords) {
      if (!(word.equals("1-0") || word.equals("0-1") || word.equals("1/2-1/2")
          || word.equals("*"))) {
        Move move = getMove(color, word);
        moves.add(move);
        color = swap(color);
      }
    }

    for (Move readMove : moves) {
      final List<Move> allowedMoves = moveService.computeAllMoves(game.getBoard(), game.getToPlay(),
          game.getHistory(), true);

      Move move = toEnPassant(readMove, game);

      final Predicate<Move> fromXCond = m -> move.getFromX() < 0 || m.getFromX() == move.getFromX();
      final Predicate<Move> fromYCond = m -> move.getFromY() < 0 || m.getFromY() == move.getFromY();
      final Predicate<Move> toXCond = m -> /* move.getToX() < 0 || */ m.getToX() == move.getToX();
      final Predicate<Move> toYCond = m -> /* move.getToY() < 0 || */ m.getToY() == move.getToY();
      final Predicate<Move> pieceCond = m -> move.getPiece().getClass()
          .equals(m.getPiece().getClass());
      final Predicate<Move> isTakingCond = m -> move.isTaking() == m.isTaking();
      final Predicate<Move> isCheckingCond = m -> move.isChecking() == m.isChecking();
      final Predicate<Move> moveTypeCond = m -> move.getClass().equals(m.getClass());
      final Predicate<Move> promotionCond = m -> !(move instanceof PromotionMove)
          || ((PromotionMove) move).getPromotedPiece().getClass()
              .equals(((PromotionMove) m).getPromotedPiece().getClass());

      List<Move> matchingMoves = allowedMoves.stream()
          .filter(fromXCond)
          .filter(fromYCond)
          .filter(toXCond)
          .filter(toYCond)
          .filter(pieceCond)
          .filter(isTakingCond)
          .filter(isCheckingCond)
          .filter(moveTypeCond)
          .filter(promotionCond)
          .collect(Collectors.toList());

      if (matchingMoves.isEmpty()) {
        LOGGER.error("Move {} is not allowed here. Allowed moves are {}", move, allowedMoves);
        throw new IllegalArgumentException("Unexpected move: " + move);
      } else if (matchingMoves.size() > 1) {
        LOGGER.error("Move {} is ambiguous here. Allowed moves are {}", move, allowedMoves);
        throw new IllegalArgumentException("Ambiguous move: " + move);
      }
      Move matchingMove = matchingMoves.get(0);

      game.getBoard().doMove(matchingMove);
      game.setToPlay(swap(matchingMove.getPiece().getColor()));
      game.addMoveToHistory(matchingMove);
    }

    LOGGER.info("PGN game successfully loaded ({} moves, opening {})", game.getHistory().size(),
        game.getOpening());

    return game;
  }

  private Move toEnPassant(Move move, Game game) {
    if (!move.isTaking() || !(move.getPiece() instanceof Pawn)) {
      return move;
    }

    if (!game.getBoard().getPiece(move.getToX(), move.getToY()).isPresent()) {
      List<Move> history = game.getHistory();
      Move lastMove = history.get(history.size() - 1);
      return new EnPassantMove(move, lastMove.getToX(), lastMove.getToY());
    } else {
      return move;
    }
  }

  private Map<String, String> getHeadersMap(String headersContent) {
    Map<String, String> headers = new HashMap<>();
    final Pattern headerPattern = Pattern.compile("^\\[(\\w+)\\s\"(.+)\"\\]$");
    for (String line : headersContent.split("\n")) {
      Matcher headerMatcher = headerPattern.matcher(line);
      if (headerMatcher.matches()) {
        headers.put(headerMatcher.group(1), headerMatcher.group(2));
      }
    }
    return headers;
  }

  private String cleanMovesContent(String originalContent) {
    String movesContent = originalContent;

    // Skip comments
    movesContent = movesContent.replaceAll("\\{.*\\}", "");
    movesContent = movesContent.replaceAll(";.*\\n", "");
    movesContent = movesContent.replaceAll("[\\\\?\\\\!]", "");

    // Skip variants
    movesContent = movesContent.replaceAll("\\(.*\\)", "");

    // Skip moves number
    movesContent = movesContent.replaceAll("\\d+\\.{1,3}", "");

    // Skip unnecessary spaces
    movesContent = StringUtils.strip(movesContent);
    return movesContent;
  }

  private Move getMove(Color color, String word) {
    final Pattern castlingPattern = Pattern.compile("^O(-O){1,2}.*$");

    Move move;
    Matcher castlingMatcher = castlingPattern.matcher(word);
    if (castlingMatcher.matches()) {
      move = getCastlingMove(color, word);
    } else {
      move = getStandardMove(color, word);
    }

    Pattern checkPattern = Pattern.compile("^.+[+#]$");
    Matcher checkMatcher = checkPattern.matcher(word);
    if (checkMatcher.matches()) {
      move.setChecking(true);
    }
    return move;
  }

  private Move getStandardMove(Color color, String word) {
    final Pattern piecePattern = Pattern.compile("^[KQBNR].*$");
    final Pattern columnFromPattern = Pattern.compile("^([abcdefgh])[xabcdefgh].*$");
    final Pattern lineFromPattern = Pattern.compile("^([12345678])[xabcdefgh].*$");
    final Pattern columnLineFromPattern = Pattern
        .compile("^([abcdefgh])([12345678])[xabcdefgh].*$");
    final Pattern columnLineToPattern = Pattern.compile("^([abcdefgh])([12345678]).*$");
    final Pattern promotionPattern = Pattern.compile("^=([QBNR])[+]?$");

    
    String remaining = word;
    Piece piece;
    Piece tookPiece = null;
    int fromX = -1;
    int fromY = -1;
    int toX = -1;
    int toY = -1;

    Matcher pieceFirstLetterMatcher = piecePattern.matcher(remaining);
    if (pieceFirstLetterMatcher.matches()) {
      piece = getPiece(color, remaining);
      remaining = remaining.substring(1);
    } else {
      piece = new Pawn(color);
    }

    Matcher columnFromMatcher = columnFromPattern.matcher(remaining);
    Matcher lineFromMatcher = lineFromPattern.matcher(remaining);
    Matcher columnLineFromMatcher = columnLineFromPattern.matcher(remaining);
    if (columnFromMatcher.matches()) {
      fromX = Move.convertCharToX(columnFromMatcher.group(1).charAt(0));
      remaining = remaining.substring(1);
    } else if (lineFromMatcher.matches()) {
      fromY = Integer.parseInt(lineFromMatcher.group(1)) - 1;
      remaining = remaining.substring(1);
    } else if (columnLineFromMatcher.matches()) {
      fromX = Move.convertCharToX(columnLineFromMatcher.group(1).charAt(0));
      fromY = Integer.parseInt(columnLineFromMatcher.group(2)) - 1;
      remaining = remaining.substring(2);
    }

    if (remaining.startsWith("x")) {
      tookPiece = new Pawn(color == Color.WHITE ? Color.BLACK : Color.WHITE);
      remaining = remaining.substring(1);
    }

    Matcher columnLineToMatcher = columnLineToPattern.matcher(remaining);
    if (columnLineToMatcher.matches()) {
      toX = Move.convertCharToX(columnLineToMatcher.group(1).charAt(0));
      toY = Integer.parseInt(columnLineToMatcher.group(2)) - 1;
      remaining = remaining.substring(2);
    } else {
      throw new IllegalArgumentException("Cannot determine move " + word + " (" + color + ")");
    }

    Move move = new Move(piece, fromX, fromY, toX, toY);

    if (tookPiece != null) {
      move.setTookPiece(tookPiece);
    }

    Matcher promotionMatcher = promotionPattern.matcher(remaining);
    if (promotionMatcher.matches()) {
      move = getPromotionMove(color, move, promotionMatcher);
    }
    return move;
  }

  private Piece getPiece(Color color, String remaining) {
    Piece piece;
    if (remaining.startsWith("K")) {
      piece = new King(color);
    } else if (remaining.startsWith("Q")) {
      piece = new Queen(color);
    } else if (remaining.startsWith("B")) {
      piece = new Bishop(color);
    } else if (remaining.startsWith("N")) {
      piece = new Knight(color);
    } else {
      assert remaining.startsWith("R");
      piece = new Rook(color);
    }
    return piece;
  }

  private Move getPromotionMove(Color color, Move move, Matcher promotionMatcher) {
    Piece promotedPiece;
    switch (promotionMatcher.group(1)) {
      case "R":
        promotedPiece = new Rook(color);
        break;
      case "B":
        promotedPiece = new Bishop(color);
        break;
      case "N":
        promotedPiece = new Knight(color);
        break;
      default:
        promotedPiece = new Queen(color);
        break;
    }
    return new PromotionMove(move, promotedPiece);
  }

  private Move getCastlingMove(Color color, String word) {
    Move move;
    Piece king = new King(color);
    Piece rook = new Rook(color);
    if (word.startsWith("O-O-O")) {
      if (color == Color.WHITE) {
        move = new CastlingMove(king, 4, 0, 2, 0, rook, 0, 0, 3, 0);
      } else {
        move = new CastlingMove(king, 4, 7, 2, 7, rook, 0, 7, 3, 7);
      }
    } else {
      if (color == Color.WHITE) {
        move = new CastlingMove(king, 4, 0, 6, 0, rook, 7, 0, 5, 0);
      } else {
        move = new CastlingMove(king, 4, 7, 6, 7, rook, 7, 7, 5, 7);
      }
    }
    return move;
  }
}
