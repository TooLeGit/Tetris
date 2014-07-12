package tetris;
/*
 * TCSS 305 - Winter 2007 - Tetris Game
 * Author - Eric Smyth
 * Reformatted for Autumn 2008 TCSS 305 Code Standard by
 * Daniel M. Zimmerman
 */

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.util.ArrayList;
import java.util.List;

import javax.media.ControllerEvent;
import javax.media.ControllerListener;
import javax.media.EndOfMediaEvent;
import javax.media.Manager;
import javax.media.MediaLocator;
import javax.media.NoPlayerException;
import javax.media.Player;

/**
 * The MusicPlayer is used to play MP3 and WAV music files in the
 * tetris game.
 * 
 * @author Eric Smyth
 * @version 1.0
 */

public class MusicPlayer
{
  /**
   * The player.
   */
  
  private Player my_player;
  
  /**
   * The file being played.
   */
  
  private File my_file;
  
  /**
   * The playlist.
   */
  
  private List<File> my_playlist;
  
  /**
   * The current index within the playlist.
   */
  
  private int my_index;
  
  /**
   * Tracks if the music is paused or not.
   */
  
  private boolean my_paused_flag;
  

  /**
   * The newList method creates a new playlist using the passed
   * array of files.
   * 
   * @param the_files The array of files to add to the playlist.
   */
  
  public void newList(final File[] the_files)
  {
    my_playlist = new ArrayList<File>();
    
    for (int i = 0; i < the_files.length; i++)
    {
      my_playlist.add(the_files[i]);
    }
    
    my_file = my_playlist.get(0);
    my_index = 0;
    my_paused_flag = false;
    getSong();
  }
  
  /**
   * The changed method stops the current song and adds the passed
   * value to the index. The file at the new index is then played
   * 
   * @param the_change The change to the index
   */
  
  public void change(final int the_change)
  {
    if (isStarted())
    {
      final int new_index = my_index + the_change;
      
      if (new_index >= 0 && new_index < my_playlist.size() - 1)
      {
        my_index = new_index;
        my_file = my_playlist.get(my_index);
        my_player.stop();
        getSong();
      }
    }
  }
  
  /**
   * Used to verify if the player has a playlist loaded.
   * 
   * @return true if the player has a playlist.
   */
  public boolean hasList()
  {
    boolean result = false;
    
    if (my_playlist != null)
    {
      result = true;
    }
    
    return result;
  }
  
  /**
   * Used to check if a song is started.
   * 
   * @return true if there is a song playing.
   */
  public boolean isStarted()
  {    
    return my_player != null && my_player.getState() == Player.Started;
  }
  
  /**
   * Stops the current song if applicable.
   */
  public void stopPlay()
  {
    if (my_player != null)
    {
      my_player.stop();
      my_player.close();
    }
  }
  
  /**
   * Restarts a paused song.
   */
  
  public void play()
  {
    if (my_player != null)
    {
      my_player.start();
    }
  }
  
  /**
   * Pauses or unpauses the current song as applicable.
   */
  
  public void pause()
  {
    if (my_player != null)
    {
      if (my_paused_flag)
      {
        my_paused_flag = false;
        my_player.start();
      }
      else
      {
        my_paused_flag = true;
        my_player.stop();
      }
    }
  }
  
  //Private Methods
  
  /**
   * Loads the song in the current file.
   */
  
  @SuppressWarnings("deprecation")
  private void getSong()
  {
    try 
    {
      if (my_player != null)
      {
        my_player.stop();
        my_player.close();
        my_player = null;
      }
      final MediaLocator media_locator = new MediaLocator(my_file.toURL());
      my_player = Manager.createPlayer(media_locator);
      my_player.addControllerListener(new ControllerListener() {
        public void controllerUpdate(final ControllerEvent the_event) 
        {
          if (the_event instanceof EndOfMediaEvent)
          {
            change(1);
          }
        }
      });
      my_player.prefetch();
      my_player.realize();
      my_player.start();
    } 
    catch (final MalformedURLException e) 
    {
      System.err.println(e.getMessage());
    } 
    catch (final NoPlayerException e) 
    {
      System.err.println(e.getMessage());
    } 
    catch (final IOException e) 
    {
      System.err.println(e.getMessage());
    }
  }
}
