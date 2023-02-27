/*
 * This file is part of choco-solver, http://choco-solver.org/
 *
 * Copyright (c) 2020, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package NonWorkingOrOldPropagators_ForReference;

import main.TriviumAlban;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.DirectedGraphVar;
import org.chocosolver.solver.variables.Variable;
import org.chocosolver.util.ESat;
import utils.GraphEventType;
import utils.utilitaire;

/**
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 25/11/2020
 */
public class PropBlockSomepath extends Propagator<Variable> {
    private final TriviumAlban triv;
    private final DirectedGraphVar graph;
    //private final PairProcedure arcRemEvent = this::check_whenArcRemoved;
    //private final PairProcedure arcAddEvent = this::check_whenArcAdded;
    //private final IntProcedure nodeAddEvent = this::check_whenNodeAdded;
    //private final IntProcedure nodeRemEvent = i -> {};

    public static int[] usedInPath;

    public PropBlockSomepath(TriviumAlban triv) {
        super(new DirectedGraphVar[]{triv.graph}, PropagatorPriority.LINEAR, false);
        this.triv = triv;
        this.graph = triv.graph;
        //GraphDeltaMonitor gdm = graph.monitorDelta(this);
        usedInPath = new int[graph.getNbMaxNodes()];
    }


    @Override
    public int getPropagationConditions(int vIdx) {
        return GraphEventType.ALL_EVENTS;
    }

    @Override
    public void propagate(int idxVarInProp, int mask) throws ContradictionException {
/*
        gdm.freeze();
        if (GraphEventType.isAddNode(mask)) {
            gdm.forEachNode(nodeAddEvent, GraphEventType.ADD_NODE);
        }
        if (GraphEventType.isRemNode(mask)) {
            gdm.forEachNode(nodeRemEvent, GraphEventType.REMOVE_NODE);
        }
        if (GraphEventType.isAddArc(mask)) {
            gdm.forEachEdge(arcAddEvent, GraphEventType.ADD_EDGE);
        }
        if (GraphEventType.isRemArc(mask)) {
            gdm.forEachEdge(arcRemEvent, GraphEventType.REMOVE_EDGE);
        }
        gdm.unfreeze();

 */
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        //System.out.println("##################propagate sym");
        //utilitaire.graphVizExport(triv);
        for (int node : graph.getMandatoryNodes()) {
            if (triv.isNodeSink(node)) continue;
            if (triv.isNodeSource(node)) continue;
            check_whenNodeAdded(node);
        }
        //System.out.println("fin sym");
    }
/*
    public void check_whenArcAdded(int from, int to) throws ContradictionException {
        if (triv.isNodeSink(to)) return;
        check_whenNodeAdded(to);
    }
    //public void check_whenArcRemoved(int from,int to) throws ContradictionException{
    //}
*/

    static int endingNodes;

    private void setEndingNode(int endingNode) {
        endingNodes = endingNode;
        boolean newPrint= endingNodes==1656;
        if(print||newPrint) System.out.println("setting print to:"+newPrint);
        print =newPrint;// || endingNodes == -1656;
        if (triv.isNodeRegisterA(endingNode)) {
            buildPathtoA();
        } else if (triv.isNodeRegisterB(endingNode)) {
            buildPathtoB();
        } else if (triv.isNodeRegisterC(endingNode)) {
            buildPathtoC();
        } else {
            throw new RuntimeException("BUGGGG from PropBlockSomepath::setEndingNode");
        }
    }

    public void check_whenNodeAdded(int node) throws ContradictionException {
        //useless as I run on ALL mandatory nodes.
        //while(graph.getMandatorySuccessorsOf(node).size()==1 && !triv.isNodeSink(graph.getMandatorySuccessorsOf(node).min())){
        //    node = graph.getMandatorySuccessorsOf(node).min();
        //}

        if (print) System.out.println("searching from :" + utilitaire.getNodeName(node));
        setEndingNode(node);
        if (print) System.out.println("ending node set-ed");
        //System.out.println("checking removed node"+node);
        check_nodeAdd(node, 0);
    }

    public void check_nodeAdd(int startingNode, int pathLength) throws ContradictionException {
        //when a new arc is added, check if it is from a forbidden path.
        if (print) System.out.println("..." + startingNode + "-" + pathLength + " Mandpred:" + graph.getMandatoryPredecessorsOf(startingNode) + " Potpred:" + graph.getPotentialPredecessorOf(startingNode));

        if (isSymetryFound(startingNode, pathLength)) {
            setUsedInPaths(startingNode, pathLength);
            //if (print)
                System.out.println("###FAIL### found symetry starting node:" + startingNode + " pathlength:" + pathLength + " endingnodes:" + endingNodes + "-" + utilitaire.getNodeName(endingNodes));
            printPaths(startingNode, pathLength);

            //if(startingNode!=252)
            // checker : need to have found one path in symetry
            this.fails();
            //propagator idea : if only 1 node left on non mandatory paths
            /*
            //propagator : dont need a path !TODO
            int succ1 = startingNode+mirroredPath[startingNode/triv.nbMaxNodePerRegistre][pathLength][0][0];
            int succ2 = startingNode+mirroredPath[startingNode/triv.nbMaxNodePerRegistre][pathLength][1][0];
            graph.removeEdge(startingNode,succ1,this);
            graph.removeEdge(startingNode,succ2,this);
             */
        } else
            for (int pred : graph.getMandatoryPredecessorsOf(startingNode)) {
                if (triv.isArcDoubling(pred, startingNode)) continue;//do nothing with doubling pattern. (yet?)
                check_nodeAdd(pred, pathLength + triv.arcRoundDistance(pred, startingNode));
            }
    }

    public void setUsedInPaths(int startingNode, int pathLength) {
        if (print) System.out.println("CALLING setUsedInPaths");
        int[][] pathsFromThisNode = mirroredPath[startingNode / triv.nbMaxNodePerRegistre][pathLength];
        for (int[] path : pathsFromThisNode) {
            int node = startingNode;
            for (int i = 0; i < path.length - 1; i++) {
                node += path[i];
                if (usedInPath[node] % 1000 == pathLength
                        && usedInPath[node] / 1000 == startingNode) {
                    //same path ?
                    continue;//TODO should continue on all node of all path : return better. except for debugging.
                }
                if (usedInPath[node] != 0) {
                    //new path ?
                    if (print) System.out.println("##found a new sym on node: " + node);
                    if (print) System.out.print("old pathLen:" + usedInPath[node] % 1000);
                    if (print) System.out.println(" new pathLen:" + pathLength);
                    if (print) System.out.print("old starting:" + usedInPath[node] / 1000);
                    if (print) System.out.println(" new starting:" + startingNode);
                } else {
                    if (print) System.out.println("##first sym on node: " + node);
                    if (print) System.out.println(" new starting:" + startingNode);
                    if (print) System.out.println(" new pathLen:" + pathLength);
                    usedInPath[node] = startingNode * 1000 + pathLength;
                }
            }
        }
    }

    public boolean checkIfUsedInAnotherPath(int node, int startingNode, int pathLength) {
        if (usedInPath == null) return false;
        if (usedInPath[node] == 0) return false;
        if (print) System.out.println("checkIfUsedInAnotherPath:" + usedInPath[node] + " startingNode:" + startingNode + " pathlen:" + pathLength);
        int otherStarting = usedInPath[node] / 1000;
        if(otherStarting == startingNode) return false;
        int otherPathLen  = usedInPath[node] % 1000;
        if (otherPathLen != pathLength || otherStarting != startingNode){
            //different path.
            //it is a pb the ending node are not the same. lets compute them :
            if (mirroredPath[otherStarting / triv.nbMaxNodePerRegistre] == null) return true;
            if (mirroredPath[otherStarting / triv.nbMaxNodePerRegistre][otherPathLen] == null) return true;
            if (mirroredPath[otherStarting / triv.nbMaxNodePerRegistre][otherPathLen][0] == null) return true;
            for(int d:mirroredPath[otherStarting / triv.nbMaxNodePerRegistre][otherPathLen][0]) otherStarting+=d;
            for(int d:mirroredPath[startingNode  / triv.nbMaxNodePerRegistre][pathLength][0]  ) startingNode+=d;
            if(startingNode == otherStarting) {
                return false;//if they have the same end, it is not a problem.
            }
            return true;
        }
        return false;//it is the same path, let it go
    }

    public void printPaths(int startingNode, int pathLength) {
        int[][] pathsFromThisNode = mirroredPath[startingNode / triv.nbMaxNodePerRegistre][pathLength];
        if (pathsFromThisNode == null) return;

        int nbPath = 0;
        for (int[] path : pathsFromThisNode) {
            int currentNode = startingNode;
            if (print) System.out.println("path :" + (++nbPath) + "\t");
            for (int distance : path) {
                if (print) System.out.print(utilitaire.getNodeName(currentNode) + "\t");
                if (print)
                    System.out.print(" _\t" + (graph.getPotentialNodes().contains(currentNode) ? (graph.getMandatoryNodes().contains(currentNode) ? "mandatory " : "Potential  ") : "NotPresent"));
                if (print) System.out.print(" _\t" + graph.getPotentialSuccessorsOf(currentNode));
                if (print) System.out.println(" _\t" + graph.getPotentialSuccessorsOf(currentNode).size());
                currentNode += distance;
            }
            if (print) System.out.println(utilitaire.getNodeName(currentNode));
        }
    }

    int nbPAthAnalysed;
    static boolean print = false;//= endingNodes==1647 ||endingNodes == 1656;

    private boolean isSymetryFound(int startingNode, int pathLength) {
        //print = endingNodes==1647 ||endingNodes == 1656;
        if (!graph.getMandatoryNodes().contains(startingNode)) return false;
        int[][] pathsFromThisNode = mirroredPath[startingNode / triv.nbMaxNodePerRegistre][pathLength];
        if (print)System.out.println("startingNode/triv.nbMaxNodePerRegistre" + startingNode / triv.nbMaxNodePerRegistre);
        if (print)System.out.print("endingNodes:" + endingNodes + " " + utilitaire.getNodeName(endingNodes) + " analysing path of len:" + pathLength + " so starting node is:" + startingNode + " " + utilitaire.getNodeName(startingNode));
        if (pathsFromThisNode == null) {
            if(print) System.out.println("... no path found");
            return false;
        }
        if (print) System.out.println("...... found " + pathsFromThisNode.length + " paths, analysing");
        int nbPathAvailable = 0;
        boolean onePathUsedISFound = false;
        nbPAthAnalysed = 0;
        for (int[] path : pathsFromThisNode) {
            if (print) System.out.println("analysing path nb" + (++nbPAthAnalysed));
            int res = checkThisPath(startingNode, path, pathLength);
            if (res == 0) {
                if (print) System.out.println("unknonwn, skipping....");
                return false;//if one is unknown, cannot do nothing yet
            }
            if (res == 1) {
                if (print) System.out.println("found=1: could exist");
                nbPathAvailable++;
            }
            if (res == 2) {
                if (print) System.out.println("found=2: mandatory in this tree");
                nbPathAvailable++;
                onePathUsedISFound = true;
            }
            if (res == 12) {
                if (print) System.out.println("found=12: mandatory in this tree, and it is lock !!");
                return false;
            }
            if (res == -1) {
                if (print) System.out.println("found=-1: not a valid path");
            }
        }
        if (print) System.out.println("nbValidpathfound: " + nbPathAvailable);
        if (!onePathUsedISFound) return false;
        if (nbPathAvailable == 0) return false;
        return nbPathAvailable % 2 == 0;
    }

    // -1 the path is not valid (used somewhere else, or using not in graph-after round maxfor exemple-)
    //  0 we dont know yet
    // +1 the path is free
    // +2 the path is used in the current search tree
    // +10 the path is used, but locked from a previous symetry.
    private int checkThisPath(int startingNode, int[] path, int pathLength) {
        int currentNode = startingNode + path[0];
        int nextNode = currentNode + path[1];
        boolean used = true;
        int thisPathIsLocked = 0;
        for (int i = 2; i < path.length; i++) {
            if (triv.getRound(currentNode) >= triv.nbInnerRound) return -1;
            if (print) System.out.println("checking existence of node:" + currentNode);
            if (graph.getPotentialNodes().contains(currentNode)) {
                if (print) System.out.println("...it exist");
                if (!graph.getPotentialSuccessorsOf(currentNode).contains(nextNode)) return -1;
                if (graph.getPotentialSuccessorsOf(currentNode).size() > 1) return 0;
            }
            if (graph.getMandatoryNodes().contains(currentNode)) {
                if (print) System.out.print("its not mandatory");
                if (checkIfUsedInAnotherPath(currentNode, startingNode, pathLength)) {
                    if (print) System.out.println(", but is used in other path");
                    thisPathIsLocked = 10;
                } else {
                    if (print) System.out.println(", not in other path");
                }
            } else {
                if (print) System.out.println("its not mandatory");
                used = false;
            }

            currentNode = nextNode;
            nextNode += path[i];
        }
        if (print) System.out.println("checking existence of node:" + currentNode);
        if (triv.getRound(currentNode) >= triv.nbInnerRound) return -1;
        if (graph.getPotentialNodes().contains(currentNode)) {
            if (print) System.out.println("...it exist");
            if (!graph.getPotentialSuccessorsOf(currentNode).contains(nextNode)) return -1;
            if (graph.getPotentialSuccessorsOf(currentNode).size() != 1) return 0;
        }
        if (graph.getMandatoryNodes().contains(currentNode)) {
            if (print) System.out.print("its mandatory");
            if (checkIfUsedInAnotherPath(currentNode, startingNode, pathLength)) {
                if (print) System.out.println(", and is used in other path");
                thisPathIsLocked = 10;
            } else {
                if (print) System.out.println(", not in other path");
            }
        } else {
            if (print) System.out.println("its not mandatory");
            used = false;
        }

        return (used ? 2 + thisPathIsLocked : 1);
    }


    static int NBREGISTER = 3;
    static int MAXPATHLENGTH = 600;
    static int[][][][] mirroredPath;

    private void buildPathtoA() {
        mirroredPath = new int[NBREGISTER][MAXPATHLENGTH][][];
        mirroredPath[0][270] = new int[][]{{69, 2066, -931, -934}, {2066, -931, -934, 69}};
        mirroredPath[0][285] = new int[][]{{69, 2066, -916, -934}, {2066, -916, -934, 69}};
        mirroredPath[0][288] = new int[][]{{2111, -916, -907}, {2066, 87, -931, -934}};
        mirroredPath[0][297] = new int[][]{{69, 2066, -931, -907}, {2066, -931, -907, 69}};
        mirroredPath[0][312] = new int[][]{{69, 2066, -916, -907}, {2066, -916, -907, 69}};
        mirroredPath[0][315] = new int[][]{{69, 2111, -931, -934}, {2111, -931, -934, 69}, {2066, 87, -931, -907}};
        mirroredPath[0][330] = new int[][]{{69, 2111, -916, -934}, {2111, -916, -934, 69}, {2066, 87, -916, -907}};
        mirroredPath[0][339] = new int[][]{{69, 69, 2066, -931, -934}, {69, 2066, -931, -934, 69}, {2066, -931, -934, 69, 69}, {2111, -916, 78, -934}};
        mirroredPath[0][342] = new int[][]{{69, 2111, -931, -907}, {2111, -931, -907, 69}};
        mirroredPath[0][348] = new int[][]{{69, 2066, -931, 78, -934}, {2066, -931, 78, -934, 69}, {2111, 87, -916, -934}};
        mirroredPath[1][282] = new int[][]{{-934, 2066, -916, -934}, {78, -934, 69, 69}};
        mirroredPath[1][294] = new int[][]{{-934, 2066, -931, -907}, {-907, 2066, -931, -934}};
        mirroredPath[1][300] = new int[][]{{-907, 69, 69, 69}, {78, 78, 78, -934}};
        mirroredPath[1][309] = new int[][]{{-934, 2066, -916, -907}, {-907, 2066, -916, -934}, {78, -907, 69, 69}};
        mirroredPath[1][327] = new int[][]{{-934, 2111, -916, -934}, {78, 78, 78, -907}};
        mirroredPath[1][336] = new int[][]{{-934, 69, 2066, -931, -934}, {-934, 2066, -931, -934, 69}, {-907, 2066, -916, -907}};
        mirroredPath[1][339] = new int[][]{{-934, 2111, -931, -907}, {-907, 2111, -931, -934}};
        mirroredPath[1][345] = new int[][]{{-934, 2066, -931, 78, -934}, {78, -934, 2066, -931, -934}};
        mirroredPath[2][291] = new int[][]{{-931, 78, 78, -934}, {87, -931, -934, 69}};
        mirroredPath[2][300] = new int[][]{{-931, -907, 69, 69}, {87, -931, 78, -934}};
        mirroredPath[2][306] = new int[][]{{-916, 78, 78, -934}, {87, -916, -934, 69}};
        mirroredPath[2][309] = new int[][]{{-931, 78, -907, 69}, {87, 87, -931, -934}};
        mirroredPath[2][315] = new int[][]{{-916, -907, 69, 69}, {87, -916, 78, -934}};
        mirroredPath[2][318] = new int[][]{{-931, 78, 78, -907}, {87, -931, -907, 69}};
        mirroredPath[2][324] = new int[][]{{-916, 78, -907, 69}, {87, 87, -916, -934}};
        mirroredPath[2][333] = new int[][]{{-916, 78, 78, -907}, {87, -916, -907, 69}};
        mirroredPath[2][336] = new int[][]{{-931, -934, 2066, -931, -934}, {87, 87, -931, -907}};
        mirroredPath[2][342] = new int[][]{{-931, -934, 69, 69, 69}, {87, -916, 78, -907}};


    }

    private void buildPathtoB() {
        mirroredPath = new int[NBREGISTER][MAXPATHLENGTH][][];

        mirroredPath[0][273] = new int[][]{{69, 69, 2066, -931}, {2111, -916, 78}};
        mirroredPath[0][282] = new int[][]{{69, 2066, -931, 78}, {2111, 87, -916}};
        mirroredPath[0][291] = new int[][]{{69, 2066, 87, -931}, {2066, -931, 78, 78}};
        mirroredPath[0][306] = new int[][]{{69, 2066, 87, -916}, {2066, -916, 78, 78}};
        mirroredPath[0][336] = new int[][]{{69, 2111, 87, -931}, {2066, -931, -934, 2066, -931}, {2111, -931, 78, 78}};
        mirroredPath[1][279] = new int[][]{{-934, 2066, -931, 78}, {78, -934, 2066, -931}};

        //thisone
        mirroredPath[1][288] = new int[][]{{-907, 2111, -916}, {-934, 2066, 87, -931}};


        mirroredPath[1][294] = new int[][]{{-934, 2066, -916, 78}, {78, -934, 2066, -916}};
        mirroredPath[1][306] = new int[][]{{-907, 2066, -931, 78}, {78, -907, 2066, -931}};
        mirroredPath[1][312] = new int[][]{{-907, 69, 2066, -916}, {78, 78, 78, 78}};
        mirroredPath[1][321] = new int[][]{{-907, 2066, -916, 78}, {78, -907, 2066, -916}};


        //thisone
        mirroredPath[1][324] = new int[][]{{-934, 2111, -931, 78}, {78, -934, 2111, -931}};

        mirroredPath[1][339] = new int[][]{{-934, 69, 69, 2066, -931}, {-934, 2111, -916, 78}, {78, -934, 2111, -916}};
        mirroredPath[1][348] = new int[][]{{-934, 69, 2066, -931, 78}, {-934, 2111, 87, -916}, {78, -934, 69, 2066, -931}};
        mirroredPath[2][285] = new int[][]{{-931, -934, 2066, -916}, {-916, -934, 2066, -931}};
        mirroredPath[2][312] = new int[][]{{-931, -907, 2066, -916}, {-916, -907, 2066, -931}, {87, -931, 78, 78}};
        mirroredPath[2][327] = new int[][]{{-916, -907, 2066, -916}, {87, -916, 78, 78}};
        mirroredPath[2][330] = new int[][]{{-931, -934, 2111, -916}, {-916, -934, 2111, -931}, {87, 87, 87, -931}};

    }

    private void buildPathtoC() {
        mirroredPath = new int[NBREGISTER][MAXPATHLENGTH][][];

        mirroredPath[0][267] = new int[][]{{69, 2111, 87}, {2066, -931, -934, 2066}};
        mirroredPath[0][309] = new int[][]{{69, 2066, 87, 87}, {2066, -916, -907, 2066}};
        mirroredPath[0][312] = new int[][]{{2066, -931, -934, 2111}, {2111, -931, -934, 2066}};
        mirroredPath[0][327] = new int[][]{{2066, -916, -934, 2111}, {2111, -916, -934, 2066}, {2066, 87, 87, 87}};
        mirroredPath[0][336] = new int[][]{{69, 69, 2111, 87}, {69, 2066, -931, -934, 2066}, {2066, -931, -934, 69, 2066}};
        mirroredPath[0][339] = new int[][]{{2066, -931, -907, 2111}, {2111, -931, -907, 2066}};
        mirroredPath[1][246] = new int[][]{{-934, 69, 2111}, {-907, 2066, 87}};
        mirroredPath[1][288] = new int[][]{{-934, 69, 2066, 87}, {78, 78, -934, 2066}};
        mirroredPath[1][297] = new int[][]{{-907, 69, 69, 2066}, {78, -934, 2066, 87}};
        mirroredPath[1][306] = new int[][]{{-934, 2066, 87, 87}, {78, -907, 69, 2066}};
        mirroredPath[1][315] = new int[][]{{-934, 69, 69, 2111}, {-907, 69, 2066, 87}, {78, 78, -907, 2066}};
        mirroredPath[1][333] = new int[][]{{-934, 69, 2111, 87}, {-934, 2066, -931, -934, 2066}, {-907, 2066, 87, 87}, {78, 78, -934, 2111}};
        mirroredPath[1][342] = new int[][]{{-907, 69, 69, 2111}, {78, -934, 2111, 87}};
        mirroredPath[2][261] = new int[][]{{-916, -934, 2111}, {87, 87, 87}};
        mirroredPath[2][288] = new int[][]{{-931, -934, 2066, 87}, {-916, -907, 2111}, {87, -931, -934, 2066}};
        mirroredPath[2][303] = new int[][]{{-916, -934, 2066, 87}, {87, -916, -934, 2066}};
        mirroredPath[2][315] = new int[][]{{-931, -934, 69, 2111}, {-931, -907, 2066, 87}, {87, -931, -907, 2066}};
        mirroredPath[2][330] = new int[][]{{-916, -934, 69, 2111}, {-916, -907, 2066, 87}, {87, -916, -907, 2066}};
        mirroredPath[2][333] = new int[][]{{-931, -934, 2111, 87}, {87, -931, -934, 2111}};
        mirroredPath[2][339] = new int[][]{{-931, -934, 69, 69, 2066}, {-916, 78, -934, 2111}};
        mirroredPath[2][348] = new int[][]{{-916, -934, 2111, 87}, {-931, 78, -934, 69, 2066}, {87, -916, -934, 2111}, {87, 87, 87, 87}};

    }


    @Override
    public ESat isEntailed() {
        return ESat.UNDEFINED;
    }
}
