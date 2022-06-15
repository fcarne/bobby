package ch.teemoo.bobby;

import ch.teemoo.bobby.gui.BoardView;
import ch.teemoo.bobby.gui.IBoardView;
import ch.teemoo.bobby.helpers.BotFactory;
import ch.teemoo.bobby.helpers.GameFactory;
import ch.teemoo.bobby.helpers.GuiHelper;
import ch.teemoo.bobby.models.games.GameSetup;
import ch.teemoo.bobby.models.players.Human;
import ch.teemoo.bobby.services.FileService;
import ch.teemoo.bobby.services.MoveService;
import ch.teemoo.bobby.services.OpeningService;
import ch.teemoo.bobby.services.PortableGameNotationService;
import com.formdev.flatlaf.FlatIntelliJLaf;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class Bobby implements Runnable {
  private static final Logger LOGGER = LoggerFactory.getLogger(Bobby.class);

  private final MoveService moveService = new MoveService();
  private final FileService fileService = new FileService();
  private final PortableGameNotationService portableGameNotationService = 
      new PortableGameNotationService(moveService);
  private final OpeningService openingService = new OpeningService(portableGameNotationService,
      fileService);
  private final GameFactory gameFactory = new GameFactory();
  private final BotFactory botFactory = new BotFactory(moveService, openingService);
  private final GuiHelper guiHelper = new GuiHelper();
  private final boolean useDefaultSettings;

  public Bobby(boolean useDefaultSettings) {
    this.useDefaultSettings = useDefaultSettings;
  }

  public static void main(String[] args) {
    boolean defaultSettings = args.length > 0 && args[0].equalsIgnoreCase("default");

    setLookAndFeel(defaultSettings);
    SwingUtilities.invokeLater(new Bobby(defaultSettings));
  }

  public void run() {
    GameSetup gameSetup = null;
    if (useDefaultSettings) {
      gameSetup = new GameSetup(new Human("Player"), botFactory.getStrongestBot());
    }
    IBoardView boardView = new BoardView("Bobby chess game", guiHelper);
    GameController gameController = new GameController(boardView, gameFactory, botFactory,
        moveService, fileService, portableGameNotationService);
    gameController.newGame(gameSetup, true, r -> {});
  }

  private static void setLookAndFeel(boolean useDefaultSettings) {
    try {
      if (useDefaultSettings) {
        UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
      } else {
        UIManager.setLookAndFeel(new FlatIntelliJLaf());
      }
    } catch (Exception e) {
      LOGGER.warn("Unable to set Look and Feel (use system L&F is {})", useDefaultSettings, e);
    }
  }
}
