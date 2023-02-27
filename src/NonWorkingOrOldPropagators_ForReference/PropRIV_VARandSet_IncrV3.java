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
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.SetVar;
import org.chocosolver.solver.variables.Variable;
import org.chocosolver.solver.variables.delta.IGraphDeltaMonitor;
import org.chocosolver.solver.variables.events.GraphEventType;
import org.chocosolver.util.ESat;
import org.chocosolver.util.objects.setDataStructures.ISet;
import org.chocosolver.util.procedure.IntProcedure;
import org.chocosolver.util.procedure.PairProcedure;
import utils.utilitaire;

/**
 * <br/>
 *
 * @author Alban DERRIEN
 * @since 01/03/2022
 *  * First version of the incremental propag. didnt work, tried V2 V1 and reccursiv'.
 */
public class PropRIV_VARandSet_IncrV3 extends Propagator<Variable> {

    private final IGraphDeltaMonitor gdm;
    private final IntProcedure nodeEventAdd;
    private final IntProcedure nodeEventRem;
    private final PairProcedure arcEventAdd;
    private final PairProcedure arcEventRem;

    private final DirectedGraphVar graph;
    private final TriviumAlban trivium;

    public final IntVar[] RIV;
    final SetVar[] nodesCanReach;
    public final int NBTOREACH;
    public boolean[] shouldBeChecked;


    public PropRIV_VARandSet_IncrV3(TriviumAlban triviumData) {
        super(new DirectedGraphVar[]{triviumData.graph}, PropagatorPriority.CUBIC, true);
        this.graph = triviumData.graph;
        this.trivium = triviumData;
        this.RIV = triviumData.RIV;
        this.NBTOREACH = triviumData.graph.getMandatoryPredecessorsOf(triviumData.idxSink).size();
        this.nodesCanReach = triviumData.RIVset;
        this.shouldBeChecked = new boolean[trivium.graph.getNbMaxNodes()];

        this.gdm = graph.monitorDelta(this);
        this.nodeEventAdd = i -> {
            shouldIPrint("newModif on node:" + i + " call=nodeEventAdd");
            newModif(i, 1);
        };
        this.nodeEventRem = i -> {
            shouldIPrint("newModif on node:" + i + " call=nodeEventRem");
            newModif(i, 2);//nothing to be done here.
        };
        this.arcEventAdd = (i, j) -> {
            shouldIPrint("newModif on node:" + i + " call=arcEventAdd");
            newModif(i, 3);
            shouldIPrint("newModif on node:" + i + " call=arcEventAdd");
            newModif(j, 4);
        };
        this.arcEventRem = (i, j) -> {
            shouldIPrint("newModif on node:" + i + " call=arcEventRem");
            newModif(i, 5);
            shouldIPrint("newModif on node:" + i + " call=arcEventRem");
            newModif(j, 6);
        };
    }

    private int[] getNeighboor(int node) {
        int nbN = graph.getPotentialPredecessorOf(node).size() + graph.getPotentialSuccessorsOf(node).size();
        int[] res = new int[nbN];
        for (int p : graph.getPotentialPredecessorOf(node)) res[--nbN] = p;
        for (int s : graph.getPotentialSuccessorsOf(node)) res[--nbN] = s;
        return res;
    }


    private boolean updateLB(int node, int newlb) throws ContradictionException {
        if (newlb > RIV[node].getUB()) {//useless we haveremove all arcs, but it is logical.
            removeNode(node);//filtering 3/3
            return true;
        } else if (newlb > RIV[node].getLB()) {
            RIV[node].updateLowerBound(newlb, this);
            return true;
        }
        return false;
    }

    private boolean updateUB(int node, int newub) throws ContradictionException {
        if (newub < RIV[node].getLB()) {
            removeNode(node);//filtering 3/3
            return true;
        } else if (newub < RIV[node].getUB()) {
            RIV[node].updateUpperBound(newub, this);
            return true;
        }
        return false;
    }

    public boolean removeItemFromNode(int node, int v) throws ContradictionException {
        if (nodesCanReach[node].getLB().contains(v)) {
            //if you cannot join a node, but is mandatory : this node is node a valid one.
            return removeNode(node);
        }
        if (nodesCanReach[node].getUB().contains(v)) {
            nodesCanReach[node].remove(v, this);
            return true;
        }
        return false;
    }

    private boolean removeNode(int node) throws ContradictionException {
        if (graph.getPotentialNodes().contains(node)) {
            graph.removeNode(node, this);
            return true;
        } else {
            //here you cannot have any neighboor so nothing to do.
            return false;
        }
    }

    public boolean enforceItemFromNode(int node, int v) throws ContradictionException {
        if (nodesCanReach[node].getLB().contains(v)) {
            return false;//already enforced.
        }
        if (nodesCanReach[node].getUB().contains(v)) {
            nodesCanReach[node].force(v, this);
            return true;//enforcing.
        }
        //nodes do not contains v, inconsistent, removing it.
        return removeNode(node);
    }

    private boolean checkNodeHasPredsAndSuccs(int node) throws ContradictionException {
        //if(trivium.isNodeSink(node) || trivium.isNodeSource(node)) return true;//no check for those. (is it even needed ?)
        if (graph.getPotentialSuccessorsOf(node).size() == 0 && !trivium.isNodeSink(node)) {//maybe be 'this' has remove previous nodes.
            //removeNode(node);
            return false;
        }
        if (graph.getPotentialPredecessorOf(node).size() == 0 && !trivium.isNodeSource(node)) {//maybe be 'this' has remove succ nodes.
            //removeNode(node);
            return false;
        }
        return true;
    }


    private boolean computeRivLB() throws ContradictionException {
        boolean doneSomething = false;
        //starting from the source, we are computing each value down to the sink.
        for (int node : utilitaire.roundCroissant(trivium.graph.getPotentialNodes())) {
            if (trivium.isNodeSink(node)) continue;//constant to 0
            if (trivium.isNodeSource(node)) continue;//constant
            //if (graph.getPotentialPredecessorOf(trivium.idxSink).contains(node)) continue;//constant to 1
            if (!checkNodeHasPredsAndSuccs(node)) continue;
            computeRearchableFromPreds(node);
            if (computeRIVLB(node)) {
                doneSomething = true;
            }
        }
        return doneSomething;
    }

    private boolean computeRIVLB(int node) throws ContradictionException {

        int newLB;
        int minPredLB = NBTOREACH;
        boolean doneSomething = false;
        for (int p : graph.getPotentialPredecessorOf(node)) {
            if (trivium.isArcDoubling(p, node)) {
                int doubling2 = trivium.getOtherDoubling(p, node);
                if (!graph.getPotentialNodes().contains(doubling2)) {
                    //2  System.out.println("RIV removing arc1:"+p +" :"+node);
                    graph.removeEdge(p, node, this);//filtering 1/3
                    doneSomething = true;
                    continue;
                }
                newLB = RIV[p].getLB() - RIV[doubling2].getUB();
            } else {
                newLB = RIV[p].getLB();
            }

            if (newLB > RIV[node].getUB()) {
                //2  System.out.println("RIV removing arc2:"+p +" :"+node);
                graph.removeEdge(p, node, this);//filtering 2/3
                doneSomething = true;
            }
            minPredLB = Math.min(minPredLB, newLB);
        }

        //link with set :
        minPredLB = Math.max(minPredLB, nodesCanReach[node].getLB().size());

        boolean updated = updateLB(node, minPredLB);
        return doneSomething || updated;
    }

    private boolean computeRearchableFromPreds(int node) throws ContradictionException {
        boolean doneSomething = false;
        for (int v : nodesCanReach[node].getUB()) {
            //for UB, you only need that on pred may got it.
            if (!oneSupportFromUB(graph.getPotentialPredecessorOf(node), v)) {
                if (removeItemFromNode(node, v)) doneSomething = true;
            }
            if (anyMandPredAskIt(node, v) || allPotPredAskIt(node, v)) {
                if (enforceItemFromNode(node, v)) doneSomething = true;
            }
        }
        return doneSomething;
    }

    private boolean computeRivUB() throws ContradictionException {
        boolean doneSomething = false;
        //starting from the IV nodes, we are computing each value up to the source.
        for (int node : utilitaire.roundDecroissant(trivium.graph.getPotentialNodes())) {
            if (trivium.isNodeSink(node)) continue;//should not even be updated :)
            if (graph.getPotentialPredecessorOf(trivium.idxSink).contains(node)) continue;
            if (!checkNodeHasPredsAndSuccs(node)) continue;


            if (computeRearchableIVFromSuccs(node)) {
                shouldIPrint2("reachFrom Succ :" + node);
                doneSomething = true;
            }

            if (node == 230 ) {
                shouldIPrint2("status before updating 230:");
                shouldIPrint2(getNodeStatus(230));
            }
            if (node == 2339 ) {
                shouldIPrint2("status before updating 2339:");
                shouldIPrint2(getNodeStatus(2339));
            }
            if (node == 2340 ) {
                shouldIPrint2("status before updating 2340:");
                shouldIPrint2(getNodeStatus(2340));
            }

            if (computeRIVUB(node)) {
                shouldIPrint2("status after:");
                shouldIPrint2(getNodeStatus(230));
                shouldIPrint2(getNodeStatus(2339));
                shouldIPrint2(getNodeStatus(2340));

                doneSomething = true;
            }
        }
        return doneSomething;
    }

    private void shouldIPrint(String s) {
        //if(model.getSolver().getNodeCount()==50)
        // System.out.println(s);
    }

    private String getNodeStatus(int node) {
        String out = "";
        out += ("isMandatory ? " + graph.getMandatoryNodes().contains(node));
        out += "\n" + ("isPotential ? " + graph.getPotentialNodes().contains(node));
        out += "\n" + ("" + node + " Ppred:" + graph.getPotentialPredecessorOf(node) + " Psuccs:" + graph.getPotentialSuccessorsOf(node));
        out += "\n" + ("        #Ppred:" + graph.getPotentialPredecessorOf(node).size() + " #Psuccs:" + graph.getPotentialSuccessorsOf(node).size());
        out += "\n" + ("                  Mpred:" + graph.getMandatoryPredecessorsOf(node) + " Msuccs:" + graph.getMandatorySuccessorsOf(node));
        out += "\n" + ("                  #Mpred:" + graph.getMandatoryPredecessorsOf(node).size() + " #Msuccs:" + graph.getMandatorySuccessorsOf(node).size());
        out += "\n" + ("RIV:" + RIV[node]);
        out += "\n" + ("²²²²²");
        return out;
    }

    private void shouldIPrint2(String s) {
        //if(model.getSolver().getNodeCount()==50)
        if (outOfFirstPropag) System.out.println(s);
    }

    private boolean computeRIVUB(int node) throws ContradictionException {
        int maxUB = 0;
        //basic version is max of successors
        ISet potSucc = trivium.graph.getPotentialSuccessorsOf(node);
        for (int succ : potSucc) {
            maxUB = Math.max(maxUB, RIV[succ].getUB());
        }//may test for not doubling, is it faster ?
        //but for doubling, it is the sum of both !

        int idxd1 = trivium.shift.double1SuccIndex(node);
        int idxd2 = trivium.shift.double2SuccIndex(node);


        //Fast computation (from arthur) : sum of both doubling succ.
        //if(potSucc.contains(idxd1) && potSucc.contains(idxd2) ){
        //    RivUB[node] = Math.max(RivUB[node], RivUB[idxd1]+RivUB[idxd2]);
        //}
        //return;

        //no smart computation if we are at the last nodes.
        boolean smartComputation = !(potSucc.contains(idxd1) && potSucc.contains(idxd2) && trivium.getRound(idxd1) > trivium.nbInnerRound);
        if (!smartComputation) {
            if (potSucc.contains(idxd1) && potSucc.contains(idxd2)) {
                maxUB = Math.max(maxUB, RIV[idxd1].getUB() + RIV[idxd2].getUB());
            }
        } else
            //smart computation (from arthur) : computing one step after for doubling
            //because some idx are the same and thus count twice !
            if (potSucc.contains(idxd1)) {
                //succ of idxd2 from short, self and long are not overlapping with any of idxd1 succ.
                //so compute direct with idxd1.
                int nextStepIdx = trivium.shift.shortSuccIndex(idxd2);
                if (graph.getPotentialSuccessorsOf(idxd2).contains(nextStepIdx)) {
                    maxUB = Math.max(maxUB, RIV[idxd1].getUB() + RIV[nextStepIdx].getUB());
                }
                nextStepIdx = trivium.shift.selfSuccIndex(idxd2);
                if (graph.getPotentialSuccessorsOf(idxd2).contains(nextStepIdx)) {
                    maxUB = Math.max(maxUB, RIV[idxd1].getUB() + RIV[nextStepIdx].getUB());
                }
                nextStepIdx = trivium.shift.longSuccIndex(idxd2);
                if (graph.getPotentialSuccessorsOf(idxd2).contains(nextStepIdx)) {
                    maxUB = Math.max(maxUB, RIV[idxd1].getUB() + RIV[nextStepIdx].getUB());
                }

                if (graph.getPotentialSuccessorsOf(idxd2).contains(trivium.shift.double1SuccIndex(idxd2))) {
                    //but after doublingSucc of idxd2, some may overlap with succ of idxd1.
                    int sumDouble2Double = RIV[trivium.shift.double1SuccIndex(idxd2)].getUB() +
                            RIV[trivium.shift.double2SuccIndex(idxd2)].getUB();
                    //if(sumDouble2Double>RivUB[idxd2]) System.out.println("greater Than");
                    sumDouble2Double = Math.min(sumDouble2Double, RIV[idxd2].getUB());

                    int maxFromDouble1Succ = 0;
                    if (graph.getPotentialSuccessorsOf(idxd1).contains(trivium.shift.selfSuccIndex(idxd1)))
                        maxFromDouble1Succ = Math.max(maxFromDouble1Succ, RIV[trivium.shift.selfSuccIndex(idxd1)].getUB());
                    if (graph.getPotentialSuccessorsOf(idxd1).contains(trivium.shift.shortSuccIndex(idxd1)))
                        maxFromDouble1Succ = Math.max(maxFromDouble1Succ, RIV[trivium.shift.shortSuccIndex(idxd1)].getUB());
                    if (graph.getPotentialSuccessorsOf(idxd1).contains(trivium.shift.double1SuccIndex(idxd1))) {
                        int riv = RIV[trivium.shift.double1SuccIndex(idxd1)].getUB();
                        //WRONG does not work !!!!  counter exemple : iv672_1.
                        // int penality = Math.max(0, -RIV[idxd1].getUB() +RIV[trivium.shift.double1SuccIndex(idxd1)].getUB() +RIV[trivium.shift.double2SuccIndex(idxd1)].getUB());
                        //maxFromDouble1Succ = Math.max(maxFromDouble1Succ, riv-penalty);
                        maxFromDouble1Succ = Math.max(maxFromDouble1Succ, riv);
                    }
                    maxUB = Math.max(maxUB, sumDouble2Double + maxFromDouble1Succ);
                }
            }

        //link with set :
        maxUB = Math.min(maxUB, nodesCanReach[node].getUB().size());

        if (node == 230) {
            shouldIPrint2("status just before updateUB(" + node + "," + maxUB + ")");
            shouldIPrint2(getNodeStatus(230));
        }
        return updateUB(node, maxUB);
    }

    private boolean computeRearchableIVFromSuccs(int node) throws ContradictionException {
        int supportLB;
        boolean doneSomething = false;
        ISet succs = graph.getPotentialSuccessorsOf(node);
        //if(succs.contains(trivium.idxSink)) return false;//do nothing with last nodes, they are the constants
        if (succs.size() == 0) {
            //System.out.println("can we go there?");//yes during first propag
            return false; //we can do better, but not our place here.
        }
        for (int v : nodesCanReach[node].getUB()) {
            if (!oneSupportFromUB(succs, v)) {
                if (removeItemFromNode(node, v)) doneSomething = true;
            }
            supportLB = 0;
            for (int succ : succs) {
                if (nodesCanReach[succ].getLB().contains(v)) {
                    supportLB++;
                } else if (trivium.isArcDoubling(node, succ)) {//if this succ does not ask for it, but the otherdouble is, it is still ok.
                    int other = trivium.getOtherDoubling(node, succ);
                    if (succs.contains(other) && nodesCanReach[other].getLB().contains(v)) {
                        supportLB++;
                    }
                }
            }
            if (supportLB == succs.size()) {
                if (enforceItemFromNode(node, v)) doneSomething = true;
            }
        }
        return doneSomething;
    }


    private boolean isEdgeAsks(int from, int to, int v) {
        //if pred dont needs it, he dont ask it
        if (!nodesCanReach[from].getLB().contains(v)) {
            return false;
        }
        //from here preds need it.
        //but you also dont can be sure to ask it is pred is doubling and other doubling can provide
        //is edge is normal, he ask for it.
        if (!trivium.isArcDoubling(from, to)) {
            return true;
        }
        //if the other doubling can provide it, you cannot ask for it on any side.
        int other = trivium.getOtherDoubling(from, to);
        if (nodesCanReach[other].getUB().contains(v)) {
            return false;
        }
        return true;
    }

    private boolean allPotPredAskIt(int node, int v) {
        if (graph.getPotentialPredecessorOf(node).size() == 0) return false;
        for (int l : graph.getPotentialPredecessorOf(node)) {
            if (!isEdgeAsks(l, node, v)) {
                return false;
            }
        }
        return true;
    }

    private boolean anyMandPredAskIt(int node, int v) {
        for (int l : graph.getMandatoryPredecessorsOf(node)) {
            if (isEdgeAsks(l, node, v)) {
                return true;
            }
        }
        return false;
    }

    private boolean oneSupportFromUB(ISet list, int v) {
        for (int l : list) {
            if (nodesCanReach[l].getUB().contains(v)) {
                return true;
            }
        }
        return false;
    }


    private void newModif(int node, int reason) throws ContradictionException {
        shouldBeChecked[node] = true;
        setShouldBeCheckOfNeighboor(node, getNeighboor(node));

        for (int n : getNeighboor(node))
            for (int ss : graph.getPotentialSuccessorsOf(n)) {
                shouldBeChecked[ss] = true;
            }
    }

    @Override
    public int getPropagationConditions(int vIdx) {
        return GraphEventType.REMOVE_EDGE.getMask()
                + GraphEventType.REMOVE_NODE.getMask()// remove node is catch by removed arcs (preds and succ are removed)
                + GraphEventType.ADD_EDGE.getMask()
                + GraphEventType.ADD_NODE.getMask()//might be catch by add edge : TODO try removing this one.
                ;
    }

    @Override
    public void propagate(int idxVarInProp, int mask) throws ContradictionException {
        System.out.println("IN");
        shouldIPrint2(getNodeStatus(230));
        //System.out.println("433 is here ?"+graph.getPotentialNodes().contains(433));
        for (int i = 0; i < shouldBeChecked.length; i++) shouldBeChecked[i] = false;

        gdm.forEachEdge(arcEventRem, GraphEventType.REMOVE_EDGE);
        gdm.forEachEdge(arcEventAdd, GraphEventType.ADD_EDGE);
        gdm.forEachNode(nodeEventRem, GraphEventType.REMOVE_NODE);
        gdm.forEachNode(nodeEventAdd, GraphEventType.ADD_NODE);
        //System.out.println("MID");
        checkThemUB();
        int cpt = 0;
        for (int i : graph.getPotentialNodes()) if (shouldBeChecked[i]) cpt++;
        //System.out.println(cpt*100/graph.getPotentialNodes().size());
        checkThemLB();
        filter();
        //filter();
        //System.out.println("OUT");
        //System.out.println("502 is here ?"+graph.getPotentialNodes().contains(502));
        //System.out.println("433 is here ?"+graph.getPotentialNodes().contains(433));
        System.out.println("OUT");
    }

    private void checkThemUB() throws ContradictionException {
        //UB first
        //starting from the IV nodes, we are computing each value up to the source.
        for (int node : utilitaire.roundDecroissant(trivium.graph.getPotentialNodes())) {
            if (!shouldBeChecked[node]) continue;
            if (trivium.isNodeSink(node)) continue;//should not even be updated :)
            if (graph.getPotentialPredecessorOf(trivium.idxSink).contains(node)) continue;
            int[] previousNeiboor = getNeighboor(node);
            if (!checkNodeHasPredsAndSuccs(node)) {
                setShouldBeCheckOfNeighboor(node, previousNeiboor);

                continue;
            }
            boolean bool1 = computeRearchableIVFromSuccs(node);
            boolean bool2 = computeRIVUB(node);
            if (bool1 || bool2) {
                shouldIPrint("updating UB: " + node + " Ppred:" + graph.getPotentialPredecessorOf(node) + " Psuccs:" + graph.getPotentialSuccessorsOf(node));
                shouldIPrint("                  Mpred:" + graph.getMandatoryPredecessorsOf(node) + " Msuccs:" + graph.getMandatorySuccessorsOf(node));
                shouldIPrint("                  Mpred:" + graph.getMandatoryPredecessorsOf(node).size() + " Msuccs:" + graph.getMandatorySuccessorsOf(node).size());
                setShouldBeCheckOfNeighboor(node, previousNeiboor);

                for (int n : graph.getPotentialPredecessorOf(node))
                    for (int ss : graph.getPotentialSuccessorsOf(n)) {
                        //shouldBeChecked[ss] = true;
                    }
            }
            if (bool2) {
            }
        }
    }

    private void checkThemLB() throws ContradictionException {
        //starting from the source, we are computing each value down to the sink.
        for (int node : utilitaire.roundCroissant(trivium.graph.getPotentialNodes())) {
            if (!shouldBeChecked[node]) continue;
            if (trivium.isNodeSink(node)) continue;//constant to 0
            if (trivium.isNodeSource(node)) continue;//constant
            //if (graph.getPotentialPredecessorOf(trivium.idxSink).contains(node)) continue;//constant to 1

            int[] previousNeiboor = getNeighboor(node);
            if (!checkNodeHasPredsAndSuccs(node)) {
                setShouldBeCheckOfNeighboor(node, previousNeiboor);
                continue;
            }
            boolean bool1 = computeRearchableFromPreds(node);
            boolean bool2 = computeRIVLB(node);
            if (bool1 || bool2) {
                setShouldBeCheckOfNeighboor(node, previousNeiboor);
            } else setPreviousDouble(node);
        }
    }

    private void setPreviousDouble(int node) {
        int[] doublingP = trivium.getDoublingPred(node);
        if (doublingP.length == 1) {
            shouldBeChecked[doublingP[0]] = true;
        }
        if (doublingP.length == 2) {
            shouldBeChecked[doublingP[1]] = true;
        }
    }

    private void setShouldBeCheckOfNeighboor(int node, int[] prevN) {
        for (int n : prevN) {
            shouldBeChecked[n] = true;
            for (int pp : graph.getPotentialPredecessorOf(n)) {
                //shouldBeChecked[pp] = true;
            }
            for (int ss : graph.getPotentialSuccessorsOf(n)) {
                //shouldBeChecked[ss] = true;
            }
        }
        setPreviousDouble(node);
    }

    public void checkOnPotentialNodes() throws ContradictionException {
        boolean doneSomething = false;
        for (int node : graph.getPotentialNodes()) {
            if ((graph.getPotentialSuccessorsOf(node).size() == 0 && !trivium.isNodeSink(node)) ||
                    (graph.getPotentialPredecessorOf(node).size() == 0 && !trivium.isNodeSource(node))) {
                graph.removeNode(node, this);
                doneSomething = true;
            }
        }
        if (doneSomething) checkOnPotentialNodes();
    }


    boolean outOfFirstPropag = false;

    private void filter() throws ContradictionException {
        if (computeRivUB()) {
            if (outOfFirstPropag)
                System.out.println("in filter : computeRivUB filtered something after all others, search node=" + trivium.m.getSolver().getNodeCount());
        }
        if (computeRivLB()) {
            if (outOfFirstPropag)
                System.out.println("in filter : computeRivLB filtered something after all others, search node=" + trivium.m.getSolver().getNodeCount());
        }
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        checkOnPotentialNodes();
        filter();
        checkOnPotentialNodes();
        //useless after this point, but who knows ? its free.
        filter();
        checkOnPotentialNodes();
        filter();
        System.out.println("Out of 1st propag.");
        outOfFirstPropag = true;
        gdm.startMonitoring();
    }

    @Override
    public ESat isEntailed() {
        return ESat.UNDEFINED;
    }
}
