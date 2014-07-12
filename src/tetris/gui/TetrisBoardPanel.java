/*
 * TCSS305 - Autumn 2012
 * Tetris Project
 * Levon Kechichian
 */

package tetris.gui;

import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Dimension;
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
 * Constructs the game board for tetris and displays
 * the current state every time step.
 * 
 * @author Levon Kechichian
 * @version Autumn 2012
 */
@SuppressWarnings("serial")
public class TetrisBoardPanel extends JPanel implements Observer
{
  /**
   * The color of the board outline.
   */
  private static final Color OUTLINE_COLOR = Color.LIGHT_GRAY;
  
  /**
   * A constant for setting the alpha of the piece (used for "ghosting").
   */
  private static final int GHOST_ALPHA = 75;
  
  /**
   * The paint stroke size.
   */
  private static final int STROKE_SIZE = 3;
  
  /**
   * A reference to the tetris board
   * for repainting purposes.
   */
  private Board my_board;
  
  /**
   * Constructs a panel for displaying the main tetris board.
   *
   * @param the_width the panel width
   * @param the_height the panel height
   */
  public TetrisBoardPanel(final int the_width,
    final int the_height)
  {
    super();
    setSize(new Dimension(the_width, the_height));
    setPreferredSize(new Dimension(the_width, the_height));
    setBackground(Color.DARK_GRAY);
    repaint();
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
   * Paints the tetris board graphics onto the JPanel.
   * 
   * @param the_graphics the graphics object that will be painting
   */
  public void paintComponent(final Graphics the_graphics)
  {
    super.paintComponent(the_graphics);
    final Graphics2D g2d = (Graphics2D) the_graphics;
    g2d.setRenderingHint(RenderingHints.KEY_ANTIALIASING, 
                         RenderingHints.VALUE_ANTIALIAS_ON);
    
    g2d.setStroke(new BasicStroke(STROKE_SIZE));
    final Piece projection = my_board.projection();
    for (int y = 0; y < my_board.height(); y++)
    {
      final Color[] row = my_board.rowAt(y);
      for (int x = 0; x < my_board.width(); x++)
      {
        final Color board_block = row[x];
        if (my_board.color(new Point(x, y)) == null)
        {
          g2d.setPaint(OUTLINE_COLOR);
          g2d.draw(new Rectangle2D.Double(x * (getWidth() / my_board.width()), 
            ((my_board.height() - 1) - y) * (getHeight() / my_board.height()),
            getWidth() / my_board.width(), getHeight() / my_board.height()));
        }
        else if (board_block == null)
        {
          g2d.setPaint(my_board.currentPiece().color());
          g2d.fill(new Rectangle2D.Double(x * (getWidth() / my_board.width()), 
            ((my_board.height() - 1) - y) * (getHeight() / my_board.height()),
            getWidth() / my_board.width(), getHeight() / my_board.height()));
          g2d.setPaint(OUTLINE_COLOR);
          g2d.draw(new Rectangle2D.Double(x * (getWidth() / my_board.width()), 
            ((my_board.height() - 1) - y) * (getHeight() / my_board.height()),
            getWidth() / my_board.width(), getHeight() / my_board.height()));
        }
        else
        {
          g2d.setPaint(board_block);
          g2d.fill(new Rectangle2D.Double(x * (getWidth() / my_board.width()), 
            ((my_board.height() - 1) - y) * (getHeight() / my_board.height()),
            getWidth() / my_board.width(), getHeight() / my_board.height()));
          g2d.setPaint(OUTLINE_COLOR);
          g2d.draw(new Rectangle2D.Double(x * (getWidth() / my_board.width()), 
            ((my_board.height() - 1) - y) * (getHeight() / my_board.height()),
            getWidth() / my_board.width(), getHeight() / my_board.height()));
        }
        for (int i = 0; i < Piece.NUMBER_OF_BLOCKS; i++)
        {
          if (y == projection.absolutePosition(i).y() && 
              x == projection.absolutePosition(i).x())
          {
            g2d.setPaint(new Color(projection.color().getRed(), 
              projection.color().getGreen(), projection.color().getBlue(), 
              GHOST_ALPHA));
            g2d.fill(new Rectangle2D.Double(x * (getWidth() / my_board.width()), 
              ((my_board.height() - 1) - y) * (getHeight() / my_board.height()),
              getWidth() / my_board.width(), getHeight() / my_board.height()));
          }
        }
      }
    }
  }

  /**
   * Overrides the observer interface method to repaint the tetris board.
   * 
   * @param the_observed the observable object that changed
   * @param the_arg the argument object that caused the event
   */
  @Override
  public void update(final Observable the_observed, final Object the_arg)
  {
    repaint();
  }
}
