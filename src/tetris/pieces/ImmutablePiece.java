/*
 * TCSS 305 - Autumn 2012
 * Project Tetris
 */

package tetris.pieces;

/**
 * This interface defines the required operations of immutable Tetris
 * pieces. Your pieces will implement either this interface or the
 * MutablePiece interface, <i>but not both</i>. 
 * 
 * @author Daniel M. Zimmerman
 * @version Autumn 2012
 */
public interface ImmutablePiece
{
  /** 
   * @return the piece that results from moving this piece one
   * space to the left.
   */
  ImmutablePiece moveLeft();

  /** 
   * @return the piece that results from moving this piece one
   * space to the right.
   */
  ImmutablePiece moveRight();

  /** 
   * @return the piece that results from moving this piece one
   * space down.
   */
  ImmutablePiece moveDown();

  /** 
   * @return the piece that results from rotating this piece 90
   * degrees counterclockwise.
   */
  ImmutablePiece rotate();

  /**
   * @return the x coordinate of this piece.
   */
  int x();

  /**
   * @return the y coordinate of this piece.
   */
  int y();
}
