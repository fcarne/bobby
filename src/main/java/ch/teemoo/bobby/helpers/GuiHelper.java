package ch.teemoo.bobby.helpers;

import java.awt.Font;
import java.awt.FontFormatException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class GuiHelper {
  private static final Logger LOGGER = LoggerFactory.getLogger(GuiHelper.class);

  private Font pieceFont;
  private Properties properties;

  public GuiHelper() {
    pieceFont = loadPieceFont();
    properties = loadProperties();
  }

  public Font getPieceFont() {
    return pieceFont;
  }

  public String getVersion() {
    return properties.getProperty("bobby.version");
  }

  public String getBuildTimestamp() {
    return properties.getProperty("bobby.buildTimestamp");
  }

  private Font loadPieceFont() {
    try {
      InputStream inputStream = getResource("fonts/FreeSerif.ttf");
      if (inputStream == null) {
        throw new IOException("Cannot load font from resource");
      }
      Font font = Font.createFont(Font.TRUETYPE_FONT, inputStream);
      return font.deriveFont(Font.PLAIN, 72);
    } catch (IOException | FontFormatException e) {
      LOGGER.warn("Unable to use embedded font, using fallback", e);
      return new Font("Serif", Font.PLAIN, 48);
    }
  }

  private Properties loadProperties() {
    Properties properties = new Properties();
    try (InputStream inputStream = getResource("bobby.properties")) {
      if (inputStream == null) {
        throw new IOException("Cannot load properties from resources");
      }
      properties.load(inputStream);
    } catch (IOException e) {
      LOGGER.warn("Unable to read properties", e);
    }
    return properties;
  }

  protected InputStream getResource(String filename) {
    return Thread.currentThread().getContextClassLoader().getResourceAsStream(filename);
  }

}
