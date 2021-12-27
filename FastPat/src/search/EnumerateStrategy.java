/**
 * created May 16, 2006
 * 
 * @by Marc Woerlein (woerlein@informatik.uni-erlangen.de)
 *
 * Copyright 2006 Marc Woerlein
 * 
 * This file is part of parsemis.
 *
 * Licence: 
 *  LGPL: http://www.gnu.org/licenses/lgpl.html
 *   EPL: http://www.eclipse.org/org/documents/epl-v10.php
 *   See the LICENSE file in the project's top-level directory for details.
 */
package search;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

import AlgorithmInterface.Algorithm;
import dataStructures.Canonizable;
import dataStructures.DFSCode;
import dataStructures.Frequency;
import dataStructures.Graph;
import dataStructures.HPListGraph;
import dataStructures.IntFrequency;
import dataStructures.Query;
import joinAlgorithm.JoinMNI;
import topKresults.MaxHeap;
import topKresults.MinHeap;
import utilities.Settings;

/**
 * @param <NodeType> the type of the node labels (will be hashed and checked
 *        with .equals(..))
 * @param <EdgeType> the type of the edge labels (will be hashed and checked
 *        with .equals(..))
 */
public class EnumerateStrategy<NodeType, EdgeType> implements Strategy<NodeType, EdgeType> {
	private Extender<NodeType, EdgeType> extender;
	private Graph kGraph; // KG
	private ArrayList<HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency>> TopKList;
	private static int[][] maxDegreeMatrix;// for degree checking
	private MinHeap<NodeType, EdgeType> minHeap;// top-k results
	private IntFrequency kthFreq; // k-th frequency in min-heap
	private HashMap<String, Integer> patternEdgeMap; // meta index

	public EnumerateStrategy(Graph kGraph, HashMap<String, Integer> patternEdgeMap) {
		this.kGraph = kGraph;
		this.patternEdgeMap = patternEdgeMap;
	}

	public ArrayList<HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency>> search(
			final Algorithm<NodeType, EdgeType> extend, DFSCode<NodeType, EdgeType> corePattern) {
		// Initialize top-k frequent pattern result min-heap
		minHeap = new MinHeap<NodeType, EdgeType>();
		ArrayList<Integer> sortedNodeLabels = kGraph.getSortedFreqLabels();
		maxDegreeMatrix = kGraph.getMaxDegreeMatrix();
		boolean addCorePattern = false;// if contains the core pattern in the top-k results

		// optimization: meta-index for pattern extension
		if (Settings.HMT) {
			extender = extend.PatExtMeta(patternEdgeMap, maxDegreeMatrix, sortedNodeLabels, kGraph);
		} else if (!Settings.HMT) {
			extender = extend.getExtender(0);
		}

		// Initialize max-heap to store candidate pattern set CS;
		MaxHeap<NodeType, EdgeType> maxHeap = new MaxHeap<NodeType, EdgeType>();
		List<HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency>> initialList = new ArrayList<HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency>>();
		HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency> qryMap = new HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency>();
		qryMap.put(corePattern, new IntFrequency(0));// CS <- (P,0);
		initialList.add(qryMap);
		maxHeap.initOriginList(initialList);
		maxHeap.makeHeap(0, initialList.size());

		OUT: while (maxHeap.getSize() != 0) {
			HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency> patternMap = maxHeap.popHeap(0);
			for (Entry<SearchLatticeNode<NodeType, EdgeType>, Frequency> entry : patternMap.entrySet()) {
				kthFreq = minHeap.getMinFrequency();// minHeap.top().frq
				SearchLatticeNode<NodeType, EdgeType> pattern = entry.getKey();
				Frequency parentMNI = entry.getValue();// MNI of parent's frequency
				if (parentMNI.compareTo(kthFreq) < 0) {
					System.out.println("parent's MNI is smaller than k-th frequency !!!");
					System.out.println("parentMNI:" + parentMNI);
					break OUT;
				}

				Frequency MNIfreq = null;
				if (Settings.UBJoin) {
					// Count the upper bound of MNI for candidate pattern P
					System.out.println("--- Count UB before Join: \n" + pattern);
					Query qry = new Query((HPListGraph<Integer, Double>) pattern.getHPlistGraph());
					JoinMNI kCPAA = new JoinMNI(qry, (DFSCode<NodeType, EdgeType>) pattern);
					IntFrequency UB = kCPAA.getUpperBound(kthFreq.intValue());
					System.out.println("UB: " + UB);
					if (UB.compareTo(kthFreq) > 0) {
						// count exact MNI by join algorithm
						MNIfreq = kCPAA.joinMNI();
						System.out.println("exact MNI by join: " + MNIfreq);
						if (MNIfreq.compareTo(kthFreq) > 0 || minHeap.getSize() < Settings.k) {
							// Update min-heap by pattern P
							if (addCorePattern)
								minHeap.addTopk(pattern, MNIfreq);
							addCorePattern = true;
							// pattern extension
							final Collection<SearchLatticeNode<NodeType, EdgeType>> children = extender
									.getChildren(pattern);
							for (SearchLatticeNode<NodeType, EdgeType> child : children) {
								final Canonizable can = (Canonizable) child;
								if (!can.isCanonical()) {// DFS code minimum
									System.out.println("Not Canonizable!!!");
									continue;
								}
								HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency> childMap = new HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency>();
								childMap.put(child, MNIfreq);
								maxHeap.insert(childMap);
							}
						}
					}
				} else if (Settings.UB) {
					// count upper bound of pattern
					IntFrequency UB = (IntFrequency) ((DFSCode<NodeType, EdgeType>) pattern).upperBound();
					if (UB.compareTo(kthFreq) > 0) {
						MNIfreq = ((DFSCode<NodeType, EdgeType>) pattern).eFrequency(kthFreq.intValue());
						System.out.println("exact MNI = " + MNIfreq);
						if (MNIfreq.compareTo(kthFreq) > 0 || minHeap.getSize() < Settings.k) {
							if (addCorePattern)
								minHeap.addTopk(pattern, MNIfreq);
							addCorePattern = true;
							final Collection<SearchLatticeNode<NodeType, EdgeType>> children = extender
									.getChildren(pattern);
							for (SearchLatticeNode<NodeType, EdgeType> child : children) {
								final Canonizable can = (Canonizable) child;
								if (!can.isCanonical()) {
									System.out.println("Not Canonizable!!!");
									continue;
								}
								HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency> childMap = new HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency>();
								childMap.put(child, MNIfreq);
								maxHeap.insert(childMap);
							}
						}
					}
				} else {// without upper bound
					int tau = kthFreq.intValue();
					if (Settings.BSDraft) {//early termination for kCP-B
						tau = 0;
					}
					// tau changed as minheap
					MNIfreq = ((DFSCode<NodeType, EdgeType>) pattern).frequency(tau);
					if (MNIfreq.compareTo(kthFreq) > 0 || minHeap.getSize() < Settings.k) {
						if (addCorePattern)
							minHeap.addTopk(pattern, MNIfreq);
						addCorePattern = true;
						final Collection<SearchLatticeNode<NodeType, EdgeType>> children = extender
								.getChildren(pattern);
						for (SearchLatticeNode<NodeType, EdgeType> child : children) {
							final Canonizable can = (Canonizable) child;
							if (!can.isCanonical()) {
								System.out.println("Not Canonizable!!!");
								continue;
							}
							HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency> childMap = new HashMap<SearchLatticeNode<NodeType, EdgeType>, Frequency>();
							childMap.put(child, MNIfreq);
							maxHeap.insert(childMap);
						}
					}
				}
				if (Settings.HMT) {
					// update meta index table
					patternEdgeMap = updatePatternEdgeMap(patternEdgeMap, kthFreq);
					OneEdgeExtension.sendPatternEdge(patternEdgeMap);
				}
				pattern.finalizeIt();
			}
		}
		System.out.println("Top-" + Settings.k + " List:\n" + minHeap.getTopKList());
		TopKList = minHeap.getTopKList();
		return TopKList;
	}

	public HashMap<String, Integer> updatePatternEdgeMap(HashMap<String, Integer> patternEdgeMap,
			IntFrequency kthFreq) {
		for (Iterator<Entry<String, Integer>> it = patternEdgeMap.entrySet().iterator(); it.hasNext();) {
			Entry<String, Integer> entry = it.next();
			int freq = entry.getValue();
			if (freq < kthFreq.intValue())
				it.remove();
		}
		return patternEdgeMap;
	}

}
