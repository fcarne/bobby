package ch.teemoo.bobby.services;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatRuntimeException;

import ch.teemoo.bobby.models.Color;
import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.pieces.Pawn;
import ch.teemoo.bobby.models.players.Human;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.UUID;
import java.util.stream.Collectors;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class FileServiceTest {

  private FileService fileService = new FileService();

  private File file;

  @BeforeEach
  void setup() throws IOException {
    file = File.createTempFile("temp", "tmp");
    file.deleteOnExit();
  }

  @Test
  void readFile() throws IOException {
    // given
    Files.write(Paths.get(file.toURI()), Arrays.asList("Hello", "World"));

    // when
    List<String> lines = fileService.readFile(Paths.get(file.toURI()));

    // then
    assertThat(lines).hasSize(2);
  }

  @Test
  void writeGameToFileBasicNotation_oneMove_fileIsWritten() throws IOException {
    // given
    Game game = new Game(new Human("A"), new Human("B"));
    game.addMoveToHistory(new Move(new Pawn(Color.WHITE), 0, 1, 0, 2));

    // when
    fileService.writeGameToFileBasicNotation(game, file);

    // then
    assertThat(file.length()).isGreaterThan(0);
    assertThat(Files.readAllLines(Paths.get(file.toURI()))).isEqualTo(
        game.getHistory().stream().map(Move::getBasicNotation).collect(Collectors.toList()));
  }

  @Test
  void readFileFromResourceFolder_existingFile_returnsFile() throws IOException {
    // given
    String folder = "openings";
    String filename = "siciliandefense.pgn";

    // when
    List<String> lines = fileService.readFileFromResourceFolder(folder, filename);

    // then
    assertThat(lines).isNotEmpty().hasSize(10);
  }

  @Test
  void readFileFromResourceFolder_nonExistingFile_throwsRuntime() {
    // given
    String folder = "openings";
    String filename = UUID.randomUUID().toString() + ".pgn";

    // then
    assertThatRuntimeException()
        .isThrownBy(() -> fileService.readFileFromResourceFolder(folder, filename))
        .withMessage("Unable to read file " + filename + " in resource folder " + folder)
        .withRootCauseInstanceOf(IllegalArgumentException.class);
  }
}
