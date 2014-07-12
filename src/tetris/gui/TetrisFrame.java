/*
 * TCSS305 - Autumn 2012
 * Tetris Project
 * Levon Kechichian
 */

package tetris.gui;

import com.sun.media.codec.audio.mp3.JavaDecoder;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.io.File;

import javax.media.Codec;
import javax.media.PlugInManager;
import javax.swing.ButtonGroup;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JRadioButtonMenuItem;
import javax.swing.Timer;

import tetris.Board;
import tetris.MusicPlayer;

/**
 * The gui for my tetris game.
 * 
 * @author Levon Kechichian
 * @version Autumn 2012
 */
@SuppressWarnings("serial")
public class TetrisFrame extends JFrame
{ 
  /**
   * The displayed height of the board.
   */
  private static final int BOARD_HEIGHT = 20;
  
  /**
   * The displayed width of the board.
   */
  private static final int BOARD_WIDTH = 10;
  
  /**
   * A constant for the board width position.
   */
  private static final double BOARD_WIDTH_CONSTANT = 0.666;
  
  /**
   * A constant for the side panel height position.
   */
  private static final double SIDE_PANEL_HEIGHT = 0.5;
  
  /**
   * The default frame width.
   */
  private static final int DEFAULT_FRAME_WIDTH = 300;
  
  /**
   * The default frame height.
   */
  private static final int DEFAULT_FRAME_HEIGHT = 400;
  
  /**
   * The larger frame width.
   */
  private static final int LARGER_FRAME_WIDTH =  500;
  
  /**
   * The larger frame height.
   */
  private static final int LARGER_FRAME_HEIGHT = 700;

  /**
   * The number of lines needed to be removed until the next level.
   */
  private static final int LINES_PER_LEVEL = 5;
  
  /**
   * Fractional representation of the time delay after each level.
   */
  private static final double NEXT_LEVEL_TIME_DELAY = 0.75;
  
  /**
   * The default time delay.
   */
  private static final int TIME_DELAY = 1000;
  
  /**
   * The string representation of the game tetris.
   */
  private static final String TETRIS_STRING = "Tetris";
  
  /**
   * The panel that displays the next piece.
   */
  private JPanel my_next_piece_panel;
  
  /**
   * The panel that displays the score and level.
   */
  private JPanel my_score_panel;
  
  /**
   * The panel that displays the tetris board.
   */
  private JPanel my_board_panel;
  
  /**
   * Reference to the tetris board object.
   */
  private Board my_board;
  
  /**
   * Reference to the timer that controls the game steps.
   */
  private Timer my_timer;
  
  /**
   * The number of lines removed so far.
   */
  private int my_line_count;
  
  /**
   * The amount of time it takes to update the game (in milliseconds).
   */
  private int my_time_increment = TIME_DELAY;
  
  /**
   * The music player for the game.
   */
  private MusicPlayer my_player;
  
  /**
   * The state of the game (true if still playing).
   */
  private boolean my_game_state;
  
  /**
   * Initializes a full screen tetris game.
   */
  public TetrisFrame()
  {
    super(TETRIS_STRING);
    setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
    setSize(DEFAULT_FRAME_WIDTH, DEFAULT_FRAME_HEIGHT);
    setPreferredSize(new Dimension(DEFAULT_FRAME_WIDTH, DEFAULT_FRAME_HEIGHT));
    my_board = new Board(BOARD_HEIGHT, BOARD_WIDTH, 
      System.currentTimeMillis());
    setResizable(false);
    addKeyListener(new TetrisKeyListener());
  }
  
  /**
   * Sets up the frame panels and listeners.
   */
  public void run()
  {
    setUpTimer();
    setBackground(Color.DARK_GRAY);
    setJMenuBar(createMenuBar());
    final JPanel panel = new JPanel(new GridLayout(1, 2));
    createBoardPanel();
    panel.add(my_board_panel);
    panel.add(createSidePanels());
    add(panel);
    createMusicPlayer();
    pack();
    setVisible(true);
    showIntro();
    
  }
  
  /**
   * Creates the music player that plays the game audio.
   */
  public void createMusicPlayer()
  {
    final Codec c = new JavaDecoder();
    PlugInManager.addPlugIn("com.sun.media.codec.audio.mp3.JavaDecoder",
          c.getSupportedInputFormats(),
          c.getSupportedOutputFormats(null),
          PlugInManager.CODEC);
    my_player = new MusicPlayer();
    my_player.newList(new File[]{new File("Gangnam Style.mp3")});
    my_player.pause();
  }
  
  /**
   * Shows the starting message along with the
   * default game controls.
   */
  public void showIntro()
  {
    displayControls();
    setGameState(true);
    my_timer.start();
    my_player.play();
    
  }
  
  /**
   * Creates the tetris board panel.
   */
  public void createBoardPanel()
  {
    my_board_panel = new TetrisBoardPanel((int) 
      (getWidth() * BOARD_WIDTH_CONSTANT), getHeight());
    ((TetrisBoardPanel) my_board_panel).setBoard(my_board);
  }
  
  /**
   * Creates the side panels which includes
   * a panel for the next piece and a panel
   * for the users score.
   * 
   * @return returns a panel that displays
   * the score and next piece
   */
  public JPanel createSidePanels()
  {
    final JPanel panel = new JPanel(new GridLayout(2, 1));
   
    my_next_piece_panel = new NextPiecePanel((int) 
      (getWidth() * (1 - BOARD_WIDTH_CONSTANT)), (int) (getHeight() * 
      SIDE_PANEL_HEIGHT));
    ((NextPiecePanel) my_next_piece_panel).setBoard(my_board);
    ((NextPiecePanel) my_next_piece_panel).createFont();
    panel.add(my_next_piece_panel);
    
    my_score_panel = new TetrisScorePanel((int) (getWidth() *
      (1 - BOARD_WIDTH_CONSTANT)), (int) (getHeight() * SIDE_PANEL_HEIGHT));
    ((TetrisScorePanel) my_score_panel).setBoard(my_board);
    ((TetrisScorePanel) my_score_panel).createFonts();
    panel.add(my_score_panel);
    
    return panel;
  }
  
  /**
   * Sets up the tetris game timer.
   */
  public void setUpTimer()
  {
    my_timer = new Timer(my_time_increment, new TimerListener());
  }
  
  /**
   * Creates the tetris menu bar.
   * 
   * @return returns a JMenuBar to be
   * displayed in the JFrame
   */
  public JMenuBar createMenuBar()
  {
    final JMenuBar tetris_menu_bar = new JMenuBar();   
    tetris_menu_bar.add(createFileMenu());
    tetris_menu_bar.add(createHelpMenu());
    tetris_menu_bar.add(createOptionsMenu());
    return tetris_menu_bar;
  }
  
  /**
   * Displays the game controls.
   */
  private void displayControls()
  {
    my_timer.stop();
    JOptionPane.showMessageDialog(null,
      'W' + " = Rotate Clockwise\n" +
      'Q' + " = Rotate Counter-Clockwise\n" +
      "SPACE" + " = Drop Piece\n" + 
      'A' + " = Move Left\n" + 
      'D' + " = Move Right\n" + 
      'S' + " = Move Down");
  }
  
  /**
   * Processes the key event to the corresponding action.
   * 
   * @param the_key the key event as an int
   */
  private void processKey(final int the_key)
  {
    switch(the_key)
    {
      case KeyEvent.VK_A:
        my_board.moveLeft();
        break;
      case KeyEvent.VK_S:
        my_board.moveDown();
        break;
      case KeyEvent.VK_D:
        my_board.moveRight();
        break;
      case KeyEvent.VK_W:
        my_board.rotateClockwise();
        break;
      case KeyEvent.VK_Q:
        my_board.rotateCounterclockwise();
        break;
      case KeyEvent.VK_SPACE:
        my_board.drop();
        break;
      case KeyEvent.VK_P:
        my_timer.stop();
        JOptionPane.showMessageDialog(null, "\tPAUSED\n\nPress OK to unpause the game");
        my_timer.start();
        break;
      default:
        System.err.println("Invalid key " + the_key);
        break;
    }
  }
  
  
  /**
   * Creates the options menu for the tetris menu bar.
   * 
   * @return returns a JMenu with option game controls
   */
  private JMenu createOptionsMenu()
  {
    final JMenu options_menu = new JMenu("Options");
    options_menu.setMnemonic(KeyEvent.VK_O);
    
    final ButtonGroup frame_size = new ButtonGroup();
    
    final JMenuItem controls = new JMenuItem("Controls", KeyEvent.VK_C);
    controls.addActionListener(new ActionListener()
    {
      public void actionPerformed(final ActionEvent the_event)
      {
        displayControls();
        if (isGamePlayable())
        {
          my_timer.start();
        }
      }
    });
    options_menu.add(controls);
    
    final JMenu view = new JMenu("View"); 
    view.setMnemonic(KeyEvent.VK_V);
    
    final JRadioButtonMenuItem original_size = 
        new JRadioButtonMenuItem("300 X 400");
    original_size.addActionListener(new ActionListener()
    {
      public void actionPerformed(final ActionEvent the_event)
      {
        my_timer.stop();
        setSize(new Dimension(DEFAULT_FRAME_WIDTH, DEFAULT_FRAME_HEIGHT));
        setPreferredSize(new Dimension(DEFAULT_FRAME_WIDTH, DEFAULT_FRAME_HEIGHT));
        resetComponents();
        if (isGamePlayable())
        {
          my_timer.start();
        }
      }
    });
    original_size.setSelected(true);
    frame_size.add(original_size);
    view.add(original_size);
    
    
    final JRadioButtonMenuItem bigger_size =
        new JRadioButtonMenuItem("500 X 700");
    bigger_size.addActionListener(new ActionListener()
    {
      public void actionPerformed(final ActionEvent the_event)
      {
        my_timer.stop();
        setSize(new Dimension(LARGER_FRAME_WIDTH, LARGER_FRAME_HEIGHT));
        setPreferredSize(new Dimension(LARGER_FRAME_WIDTH, LARGER_FRAME_HEIGHT));
        resetComponents();
        if (isGamePlayable())
        {
          my_timer.start();
        }
      }
    });
    frame_size.add(bigger_size);
    view.add(bigger_size);
    
    options_menu.add(view);
    return options_menu;
  }
  
  /**
   * Clears and resets the board frame and all its components
   * to the new specifications.
   */
  public void resetComponents()
  {
    setUpTimer();
    my_time_increment = TIME_DELAY;
    my_board_panel.setSize(new Dimension((int) (getWidth() *
      BOARD_WIDTH_CONSTANT), getHeight()));
    my_next_piece_panel.setSize(new Dimension((int) (getWidth() * 
      (1 - BOARD_WIDTH_CONSTANT)), (int) (getHeight() * SIDE_PANEL_HEIGHT)));
    my_score_panel.setSize(new Dimension((int) (getWidth() *
      (1 - BOARD_WIDTH_CONSTANT)), (int) (getHeight() * SIDE_PANEL_HEIGHT)));
    ((TetrisBoardPanel) my_board_panel).setBoard(my_board);
    ((TetrisScorePanel) my_score_panel).setBoard(my_board);
    ((TetrisScorePanel) my_score_panel).createFonts();
    ((NextPiecePanel) my_next_piece_panel).setBoard(my_board);
    ((NextPiecePanel) my_next_piece_panel).createFont();
    pack();
  }
  
  /**
   * Gets the game state.
   * 
   * @return returns true if the game is still playable.
   */
  public boolean isGamePlayable()
  {
    return my_game_state;
  }
  
  /**
   * Sets the game state as playable or not.
   * 
   * @param the_state true if the game will be playable
   */
  public void setGameState(final boolean the_state)
  {
    my_game_state = the_state;
  }
  
  /**
   * Creates a file menu for the JMenuBar.
   * 
   * @return returns a JMenu with basic tetris
   * menu options
   */
  private JMenu createFileMenu()
  {
    final JMenu file_menu = new JMenu("File");
    file_menu.setMnemonic(KeyEvent.VK_F);
    
    final JMenuItem new_game = new JMenuItem("New Game", KeyEvent.VK_N);
    new_game.addActionListener(new ActionListener()
    {
      public void actionPerformed(final ActionEvent the_event)
      {
        my_player.stopPlay();
        my_timer.stop();
        my_board = new Board(BOARD_HEIGHT, BOARD_WIDTH,
          System.currentTimeMillis());
        resetComponents();
        createMusicPlayer();
        showIntro();
      }
    });
    file_menu.add(new_game);
    
    final JMenuItem end_game = new JMenuItem("End Game", KeyEvent.VK_E);
    end_game.addActionListener(new ActionListener()
    {
      public void actionPerformed(final ActionEvent the_event)
      {
        my_player.stopPlay();
        setGameState(false);
        my_timer.stop();
      }
    });
    file_menu.add(end_game);
    
    
    final JMenuItem quit = new JMenuItem("Quit", KeyEvent.VK_Q);
    quit.addActionListener(new ActionListener()
    {
      public void actionPerformed(final ActionEvent the_event)
      {
        my_player.stopPlay();
        my_timer.stop();
        dispose();
      }
    });
    file_menu.add(quit);
    
    return file_menu;
  }
  
  /**
   * Creates the help menu for the JMenuBar.
   * 
   * @return returns a JMenu with the tetris
   * help options.
   */
  private JMenu createHelpMenu()
  {
    final JMenu help_menu = new JMenu("Help");
    help_menu.setMnemonic(KeyEvent.VK_H);
    
    final JMenuItem about = new JMenuItem("About...", KeyEvent.VK_A);
    about.addActionListener(new ActionListener()
    {
      public void actionPerformed(final ActionEvent the_event)
      {
        my_timer.stop();
        JOptionPane.showMessageDialog(null, "TCSS 305 Tetris v1.0");
        if (isGamePlayable())
        {
          my_timer.start();
        }
      }
    });
    help_menu.add(about);
    return help_menu;
  }
  
  /**
   * A listener class for the timer that controls
   * most of the game functionality.
   * 
   * @author Levon Kechichian
   * @version Autumn 2012
   */
  public class TimerListener implements ActionListener
  {
    /**
     * Overrides the actionperformed method to 
     * define how the game timer should act.
     * 
     * @param the_event the event object that was fired
     */
    public void actionPerformed(final ActionEvent the_event)
    {
      my_line_count += my_board.lastLinesRemoved();
      if (my_line_count >= LINES_PER_LEVEL)
      {
        my_time_increment = (int) (my_time_increment * NEXT_LEVEL_TIME_DELAY);
        my_timer.setDelay(my_time_increment);
        my_line_count %= LINES_PER_LEVEL;
      }
      if (my_board.isFull())
      {
        my_player.stopPlay();
        setGameState(false);
        my_timer.stop();
        JOptionPane.showMessageDialog(null, "GAME OVER!");
      }
      else
      {
        my_board.moveDown();
      }
    }
  }
  
  /**
   * Private inner class to listen  and respond
   * to key events from the user.
   * 
   * @author Levon Kechichian
   * @version Autumn 2012
   */
  public class TetrisKeyListener extends KeyAdapter
  { 
    /**
     * Overrides the keyPressed method to define it
     * for my tetris game.
     * 
     * @param the_event the key event that fired the event
     */
    public void keyPressed(final KeyEvent the_event)
    {
      final int key = the_event.getKeyCode();
      
      if (isGamePlayable())
      {
        processKey(key);
      }
    }
  }
}
