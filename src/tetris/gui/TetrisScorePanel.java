/*
 * TCSS305 - Autumn 2012
 * Tetris Project
 * Levon Kechichian
 */

package tetris.gui;

import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import java.util.Observable;
import java.util.Observer;

import javax.swing.JPanel;

import tetris.Board;

/**
 * Class for displaying the game score on a JPanel.
 * 
 * @author Levon Kechichian
 * @version Autumn 2012
 */
@SuppressWarnings("serial")
public class TetrisScorePanel extends JPanel implements Observer
{
  /**
   * The font type.
   */
  private static final String FONT_TYPE = "Helvetica";
  
  /**
   * The number of lines needed to be removed until the next level.
   */
  private static final int LINES_PER_LEVEL = 5;
  
  /**
   * The value of each line cleared.
   */
  private static final int POINT_VALUE = 100;
  
  /**
   * The paint stroke size.
   */
  private static final int STROKE_SIZE = 4;
  
  /**
   * A constant for displaying font sizes.
   */
  private static final double FONT_SIZE_CONSTANT = 0.25;
  
  /**
   * A constant for displaying my pause font size.
   */
  private static final double PAUSE_FONT_CONSTANT = 0.6;
  
  /**
   * A constant for displaying the scores y-coordinate.
   */
  private static final double SCORE_X_COORDINATE = 0.25;
  
  /**
   * A constant for displaying the scores x-coordinate.
   */
  private static final double SCORE_Y_COORDINATE = 0.45;
  
  /**
   * A constant for displaying the level y-coordinate.
   */
  private static final double LEVEL_Y_CONSTANT = 0.65;
  
  /**
   * A constant for displaying the pause string x-coordinate.
   */
  private static final double PAUSE_X_CONSTANT = 0.05;
  
  /**
   * A constant for displaying the pause string y-coordinate.
   */
  private static final double PAUSE_Y_CONSTANT = 0.9;
  
  /**
   * The font for the score and level.
   */
  private Font my_font;

  /**
   * The pause font.
   */
  private Font my_pause_font;
  
  /**
   * The current users current game level.
   */
  private int my_level = 1;
  
  /**
   * Reference to the tetris board.
   */
  private Board my_board;
  
  /**
   * The game score.
   */
  private int my_score;
  
  /**
   * Constructs a new JPanel to display the game score.
   * 
   * @param the_width the panel width
   * @param the_height the panel height
   */
  public TetrisScorePanel(final int the_width,
    final int the_height)
  {
    super();
    setSize(new Dimension(the_width, the_height));
    setPreferredSize(new Dimension(the_width, the_height));
    setBackground(Color.DARK_GRAY);
  //  repaint();
  }
  
  /**
   * Sets the board instance field to the given board.
   * 
   * @param the_board the board reference
   */
  public void setBoard(final Board the_board)
  {
    my_board = the_board;
    my_board.addObserver(this);
  }
  
  /**
   * Creates the font objects for displaying the text.
   */
  public void createFonts()
  {
    my_font = new Font(FONT_TYPE, Font.BOLD, (int) (getWidth() * FONT_SIZE_CONSTANT));
    my_pause_font = new Font(FONT_TYPE, Font.BOLD, (int) ((getWidth() * 
        FONT_SIZE_CONSTANT) * PAUSE_FONT_CONSTANT));
  }
  
  /**
   * Paints the game score on the JPanel.
   * 
   * @param the_graphics the graphics object that will be painting
   */
  public void paintComponent(final Graphics the_graphics)
  {
    super.paintComponent(the_graphics);
    final Graphics2D g2d = (Graphics2D) the_graphics;
    g2d.setRenderingHint(RenderingHints.KEY_ANTIALIASING, 
                         RenderingHints.VALUE_ANTIALIAS_ON);
    g2d.setFont(my_font);
    g2d.setStroke(new BasicStroke(STROKE_SIZE));
    g2d.setColor(Color.WHITE);
    g2d.drawString("Score", (int) (getWidth() * FONT_SIZE_CONSTANT), 
      (int) (getHeight() * FONT_SIZE_CONSTANT));
    g2d.drawString(Integer.toString(my_score), (int) (getHeight() * SCORE_X_COORDINATE), 
      (int) (getHeight() * SCORE_Y_COORDINATE));
    g2d.drawString("Level " + my_level, (int) (getWidth() * FONT_SIZE_CONSTANT), 
      (int) (getHeight() * LEVEL_Y_CONSTANT));
    g2d.setFont(my_pause_font);
    g2d.drawString("Press 'P' to Pause", (int) (getWidth() * PAUSE_X_CONSTANT), 
      (int) (getHeight() * PAUSE_Y_CONSTANT));
  }
  
  /**
   * Computes the game score and level.
   */
  private void computeScore()
  {
    final int score = my_board.lastLinesRemoved();
    for (int i = 1; i <= score; i++)
    {
      my_score += my_board.lastLinesRemoved() * POINT_VALUE;
    }
    my_level = my_score / (POINT_VALUE * LINES_PER_LEVEL) + 1;
  }
  
  /**
   * Overrides the observer interface method to display
   * the users score for the tetris game.
   * 
   * @param the_observed the observable object that changed
   * @param the_arg the argument object that caused the event
   */
  @Override
  public void update(final Observable the_observed, final Object the_arg)
  {
    computeScore();
    repaint();
  }

}
