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
import java.awt.geom.Rectangle2D;
import java.util.Observable;
import java.util.Observer;

import javax.swing.JPanel;

import tetris.Board;
import tetris.pieces.Piece;
import tetris.util.Point;

/**
 * Class for displaying the next tetris piece on a JPanel.
 * 
 * @author Levon Kechichian
 * @version Autumn 2012
 */
@SuppressWarnings("serial")
public class NextPiecePanel extends JPanel implements Observer
{ 
  /**
   * The next piece string.
   */
  private static final String PIECE_STRING = "Next Piece";
  
  /**
   * The paint stroke size.
   */
  private static final int STROKE_SIZE = 4;
  
  /**
   * The font size.
   */
  private static final double FONT_SIZE = 0.25;
  
  /**
   * A constant for displaying the label y-coordinate.
   */
  private static final double LABEL_STARTING_Y = 0.15;
  
  /**
   * A constant to display the block size in a viewable manner.
   */
  private static final double BLOCK_SIZE_CONSTANT = 0.15;
  
  /**
   * A constant for displaying the blocks x-coordinate.
   */
  private static final double BLOCK_STARTING_X = 0.20;
  
  /**
   * The font object used for displaying the text.
   */
  private Font my_font;
  
  /**
   * Reference to the tetris board.
   */
  private Board my_board;
  
  /**
   * Constructs a JPanel to display the next tetris piece.
   *
   * @param the_width the panel width
   * @param the_height the panel height
   */
  public NextPiecePanel(final int the_width,
    final int the_height)
  {
    super();
    setSize(new Dimension(the_width, the_height));
    setPreferredSize(new Dimension(the_width, the_height));
    setBackground(Color.DARK_GRAY);
//    repaint();
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
   * Creates the text font object.
   */
  public void createFont()
  {
    my_font = new Font("Helvetica", Font.BOLD, (int) (getWidth() * FONT_SIZE));
  }
  
  /**
   * Paints the next piece graphics onto the JPanel.
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
    g2d.setColor(Color.WHITE);
    g2d.setStroke(new BasicStroke(STROKE_SIZE));
    g2d.drawString(PIECE_STRING, (getWidth() / (STROKE_SIZE * STROKE_SIZE)) - 
      (PIECE_STRING.length() / STROKE_SIZE),  (int) (getHeight() * LABEL_STARTING_Y));
    
    for (int y = Piece.NUMBER_OF_BLOCKS - 1; 0 <= y; y--) 
    {
      for (int x = 0; x < Piece.NUMBER_OF_BLOCKS; x++) 
      {
        for (int i = 0; i < Piece.NUMBER_OF_BLOCKS; i++) 
        {
          final Point block = my_board.nextPiece().blocks()[i];
          if (block.x() == x && block.y() == y) 
          {
            g2d.setColor(my_board.nextPiece().color());
            g2d.fill(new Rectangle2D.Double((x * getWidth() * BLOCK_SIZE_CONSTANT) + 
               (int) (getWidth() * BLOCK_STARTING_X), (getHeight() / 2) + 
               (float) (getWidth() * BLOCK_SIZE_CONSTANT) - (y * getWidth() * 
               BLOCK_SIZE_CONSTANT), getWidth() * BLOCK_SIZE_CONSTANT, getWidth() * 
               BLOCK_SIZE_CONSTANT));
            g2d.setColor(Color.DARK_GRAY);
            g2d.draw(new Rectangle2D.Double((x * getWidth() * BLOCK_SIZE_CONSTANT) + 
              (int) (getWidth() * BLOCK_STARTING_X), (getHeight() / 2) + 
              (float) (getWidth() * BLOCK_SIZE_CONSTANT) - (y * getWidth() * 
              BLOCK_SIZE_CONSTANT), getWidth() * BLOCK_SIZE_CONSTANT, getWidth() * 
              BLOCK_SIZE_CONSTANT));
          } 
        }
      }
    }
  }
  
  /**
   * Overrides the observer interface method to display
   * the next tetris piece that will go on the tetris board.
   * 
   * @param the_observed the observable object that changed
   * @param the_arg the argument object that caused the event
   */
  @Override
  public void update(final Observable the_observed, final Object the_arg)
  {
    if (!my_board.isFull())
    {
      repaint();
    }
  }
}
