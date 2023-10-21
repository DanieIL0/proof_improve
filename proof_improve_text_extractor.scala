import isabelle._
import scala.collection.mutable

object Prooftextextractor {

  val emptyDict = scala.collection.mutable.Map[String, Int]()

  def countFreqs(xs: List[Int], dict: mutable.Map[String, Int]): mutable.Map[String, Int] = xs match {
    case Nil => dict
    case x :: rest =>
      val count = dict.getOrElse(x.toString, 0)
      dict(x.toString) = count + 1
      countFreqs(rest, dict)
  }

  def buildMapping(dict: mutable.Map[String, Int]): mutable.Map[String, String] = {
    val items = dict.toList
    val sortedItems = items.sortBy(_._2)
    val mapping = sortedItems.zipWithIndex.map { case ((x, _), i) => (x, i.toString) }
    mutable.Map(mapping: _*)
  }

  def compressList(mapping: mutable.Map[String, String], lst: List[Int]): List[Int] = {
    lst.map { x =>
      mapping.get(x.toString).flatMap(s => scala.util.Try(s.toInt).toOption).getOrElse(0)
    }
  }

  def compressInts(ints: List[Int]): List[Int] = {
    val freqDict = countFreqs(ints, emptyDict)
    val mapping = buildMapping(freqDict)
    compressList(mapping, ints)
  }

  def calculateEntropyScore(proofState: String): Int = {
    val ints = proofState.map(_.toInt).toList
    val compressedInts = compressInts(ints)
    compressedInts.length
  }

  def calculateLengthScore(proofState: String): Int = {
    proofState.length
  }
}
