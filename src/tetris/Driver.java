/*
 * TCSS305 - Autumn 2012
 * Tetris Project
 * Levon Kechichian
 */

package tetris;

import javax.swing.UIManager;
import javax.swing.UnsupportedLookAndFeelException;

import tetris.gui.TetrisFrame;

/**
 * The driver class that starts the game.
 * 
 * @author Levon Kechichian
 * @version Autumn 2012
 */
public final class Driver
{ 
  /**
   * Private constructor so that no classes can derive from it.
   */
  private Driver()
  {
    // Do nothing!
  }

  /**
   * @param the_args the arguments
   */
  public static void main(final String[] the_args) 
  {
    try
    {
      // set cross-platform Java look and feel
      UIManager.setLookAndFeel(UIManager.getCrossPlatformLookAndFeelClassName());
    }
    catch (final UnsupportedLookAndFeelException e)
    {
      assert false;
    }
    catch (final ClassNotFoundException e)
    {
      assert false;
    }
    catch (final InstantiationException e)
    {
      assert false;
    }
    catch (final IllegalAccessException e)
    {
      assert false;
    }
    
    final TetrisFrame frame = new TetrisFrame();
    frame.run();
  }

}

