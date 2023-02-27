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
 * first try to do an incremental propgator, never really worked.
 *   tried V1 V2 V3 and reccursiv'.
 */
public class PropRIV_VARandSet_recurssively extends Propagator<Variable> {

    private final IGraphDeltaMonitor gdm;
    private final IntProcedure nodeEventAdd;
    private final IntProcedure nodeEventRem;
    private final PairProcedure arcEventAdd;
    private final PairProcedure arcEventRem;

    private final DirectedGraphVar graph;
    private final TriviumAlban trivium;

    public final IntVar[] RIV;
    final SetVar nodesCanReach[];
    public final int NBTOREACH;




    public PropRIV_VARandSet_recurssively(TriviumAlban triviumData) {
        super(new DirectedGraphVar[]{triviumData.graph}, PropagatorPriority.CUBIC, true);
        this.graph = triviumData.graph;
        this.trivium = triviumData;
        this.RIV = triviumData.RIV;
        this.NBTOREACH = triviumData.graph.getMandatoryPredecessorsOf(triviumData.idxSink).size();
        this.nodesCanReach = triviumData.RIVset;

        this.gdm = graph.monitorDelta(this);
        this.nodeEventAdd = i -> {
            newModif(i,1);
        };
        this.nodeEventRem = i -> {
            newModif(i,1);//nothing to be done here.
        };
        this.arcEventAdd = (i, j) -> {
            newModif(i,1);
            newModif(j,1);
        };
        this.arcEventRem = (i, j) -> {
            newModif(i,1);
            newModif(j,1);
        };
    }
    static int whichnode=610;

    private void newModif(int node, int profondeur)throws ContradictionException{
        if(node==whichnode) System.out.println("newmodif with node:"+node);
        if (!checkNodeHasPredsAndSuccs(node)) return;
        if (trivium.isNodeSink(node)) return;//constant
        if(node==whichnode) {
            System.out.println("newmodif checkNodeHasPredsAndSuccs: OK");
            for(int s:graph.getPotentialSuccessorsOf(node)){

                System.out.println("succs:"+s);
                for(int ss:graph.getPotentialSuccessorsOf(s)){
                    //System.out.println("ss:"+ss);
                }
                for(int ss:graph.getPotentialPredecessorOf(s)){
                    //System.out.println("ss:"+ss);
                }
            }
            for(int s:graph.getPotentialPredecessorOf(node)){
                System.out.println("preds:"+s);
                for(int ss:graph.getPotentialSuccessorsOf(s)){
                    System.out.println("ps:"+ss);
                }
                for(int ss:graph.getPotentialPredecessorOf(s)){
                    System.out.println("pp:"+ss);
                }
            }
        }

        boolean bool1 = false;
        boolean bool2 = false;
        boolean bool3 = false;
        boolean bool4 = false;

        for(int v:graph.getPotentialPredecessorOf(node)){
            if (trivium.isNodeSink(v))continue;
            boolean isIn = false;
            for(int t:trivium.getTenNeighboors(node)){
                if(t==v) isIn=true;
            }
            if(!isIn){
                System.out.println("QQQQQQQ BIG BUG node="+node+" not found int getTenNeighboors:"+v);
                for(int t:trivium.getTenNeighboors(node)){
                    System.out.print(t+", ");
                }System.out.println();
            }
        }
        for(int v:graph.getPotentialSuccessorsOf(node)){
            if (trivium.isNodeSink(v))continue;
            boolean isIn = false;
            for(int t:trivium.getTenNeighboors(node)){
                if(t==v) isIn=true;
            }
            if(!isIn){
                System.out.println("QQQQQQQ BIG BUG2 node="+node+" not found int getTenNeighboors:"+v);
                for(int t:trivium.getTenNeighboors(node)){
                    System.out.print(t+", ");
                }System.out.println();
            }
        }
        //bool1 = computeRearchableFromSuccs(node);
        bool2 = computeRIVUB(node);
        if (!trivium.isNodeSource(node)) {
            //bool3 = computeRearchableFromPreds(node);
            bool4 = computeRIVLB(node);
        }
        if(bool1 ||bool2 ||bool3 ||bool4)
        {
            System.out.print("done something to node:"+node+" succs=");
            for(int s:trivium.getTenNeighboors(node)){//graph.getPotentialSuccessorsOf(node)){
                System.out.print(s+", ");
            }System.out.println();

            for(int s:trivium.getTenNeighboors(node)){//graph.getPotentialSuccessorsOf(node)){
                //for(int ss:trivium.getTenNeighboors(s)){//graph.getPotentialSuccessorsOf(node)){
                    //for(int sss:trivium.getTenNeighboors(ss)){//graph.getPotentialSuccessorsOf(node)){
                    newModif(s,1);
                    //}
                //}
            }
        }
        else
        {
            if(node==whichnode) System.out.println("done nothing with node:"+node);
            /*
            //even if nothing, go ask doubling pred.
            for(int d:trivium.getDoublingPred(node))
                if(checkNodeValidity(d))
                    for(int p: trivium.getFivePred(d))
                        newModif(p);
             */
            //even if nothing, go ask doubling pred.
            if(profondeur<2) {
                //for(int d : graph.getPotentialSuccessorsOf(node)) newModif(d, profondeur + 1);
                //for(int d : graph.getPotentialPredecessorOf(node)) newModif(d, profondeur + 1);
                for(int s:trivium.getTenNeighboors(node))newModif(s, profondeur + 1);
            }
        }
    }



    private void filter() throws ContradictionException {
        for(int node:graph.getPotentialNodes()){
            if(!checkNodeHasPredsAndSuccs(node)){
                System.out.println("in filter : checkNodeHasPredsAndSuccs filtered something after all others, search node="+node+" node count:"+trivium.m.getSolver().getNodeCount());
            }
        }

        //System.out.println("filter RIV IN");
        //utilitaire.graphVizExport(trivium);
        if(computeRivUB()){
            System.out.println("in filter : computeRivUB filtered something after all others, search node="+trivium.m.getSolver().getNodeCount());

        }
        //System.out.println("filter RIV MID");
        if(computeRivLB()){
            System.out.println("in filter : computeRivLB filtered something after all others, search node="+trivium.m.getSolver().getNodeCount());
        }
        //computeRivUB();

        //utilitaire.graphVizExport(trivium,this);
        //System.out.println("RIV OUT");
        //utilitaire.graphVizExport(trivium,this);
    }
    private boolean updateLB(int node, int newlb) throws ContradictionException {
        if(newlb>RIV[node].getUB()){//useless we haveremove all arcs, but it is logical.
            //2  System.out.println("RIV removing node:"+node);
            graph.removeNode(node,this);//filtering 3/3
            return true;
        }else if(newlb>RIV[node].getLB()) {
            RIV[node].updateLowerBound(newlb,this);
            return true;
        }
        return false;
    }
    private boolean updateUB(int node, int newub) throws ContradictionException {
        if(newub<RIV[node].getLB()){
            //2  System.out.println("RIV removing node:"+node);
            graph.removeNode(node,this);//filtering 3/3
            return true;
        }else if(newub<RIV[node].getUB()){
            RIV[node].updateUpperBound(newub,this);
            return true;
        }
        return false;
    }
    public boolean removeItemFromNode(int node, int v) throws ContradictionException{
        if(nodesCanReach[node].getLB().contains(v)) {
            //if you cannot join a node, but is mandatory : this node is node a valid one.
            return removeNode(node);
        }
        if(nodesCanReach[node].getUB().contains(v)){
            nodesCanReach[node].remove(v, this);
            return true;
        }
        return false;
    }
    private boolean removeNode(int node)throws ContradictionException{
        if(graph.getPotentialNodes().contains(node)){//this node is not valid.
            System.out.println("removing node:"+node);
            ISet succs = graph.getPotentialSuccessorsOf(node);
            ISet preds = graph.getPotentialPredecessorOf(node);
            for(int p:preds) System.out.println("queing p:"+p);
            for(int s:succs) System.out.println("queing s:"+s);
            graph.removeNode(node, this);

            for(int p:preds) System.out.println("queing:"+p);
            for(int s:succs) System.out.println("queing:"+s);
            for(int p:preds) newModif(p,1);
            for(int s:succs) newModif(s,1);
            System.out.println("removed node:"+node);
            return true;
        }else{
            System.out.println("removed already node:"+node);
            //here you cannot have any neighboor
            return false;
        }
    }
    public boolean enforceItemFromNode(int node, int v) throws ContradictionException{
        //System.out.print("enforcing "+utilitaire.getNodeName(v)+"\tfrom "+nodesCanReach[node].getName()+"...");
        if(nodesCanReach[node].getLB().contains(v)) {
            return false;//already enforced.
        }
        if(nodesCanReach[node].getUB().contains(v)){
            nodesCanReach[node].force(v, this);
            return true;//enforcing.
        }
        //nodes do not contains v, inconsistent, removing it.
        return removeNode(node);
    }

    private boolean checkNodeHasPredsAndSuccs(int node)throws ContradictionException {
        //if(trivium.isNodeSink(node) || trivium.isNodeSource(node)) return true;//no check for those. (is it even needed ?)
        if(graph.getPotentialSuccessorsOf(node).size()==0 && !trivium.isNodeSink(node)) {//maybe be 'this' has remove previous nodes.
            if(graph.getPotentialNodes().contains(node)) System.out.println("removing node no Succ:"+node);
            removeNode(node);
            return false;
        }
        if(graph.getPotentialPredecessorOf(node).size()==0 && !trivium.isNodeSource(node)) {//maybe be 'this' has remove succ nodes.
            if(graph.getPotentialNodes().contains(node)) System.out.println("removing node no Pred:"+node);
            removeNode(node);
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
            //computeRearchableFromPreds(node);
            if(computeRIVLB(node)){
                doneSomething = true;
                System.out.println("filtered something after all others: node="+node+"   search count ="+trivium.m.getSolver().getNodeCount());
            }
        }
        return doneSomething;
    }

    private boolean computeRIVLB(int node) throws ContradictionException {

        int newLB;
        int minPredLB=NBTOREACH;
        boolean doneSomething = false;
        for (int p : graph.getPotentialPredecessorOf(node)) {
            if (trivium.isArcDoubling(p, node)) {
                int doubling2 = trivium.getOtherDoubling(p, node);
                if(!graph.getPotentialNodes().contains(doubling2)) {
                   //2  System.out.println("RIV removing arc1:"+p +" :"+node);
                    graph.removeEdge(p,node,this);//filtering 1/3
                    doneSomething = true;
                    continue;
                }
                newLB = RIV[p].getLB() - RIV[doubling2].getUB();
            } else {
                newLB = RIV[p].getLB();
            }

            if(newLB>RIV[node].getUB()){
               //2  System.out.println("RIV removing arc2:"+p +" :"+node);
                graph.removeEdge(p,node,this);//filtering 2/3
                doneSomething = true;
            }
            minPredLB = Math.min(minPredLB,newLB );
        }

        //link with set :
        minPredLB = Math.max(minPredLB,nodesCanReach[node].getLB().size());

        boolean updated = updateLB(node, minPredLB);
        return doneSomething || updated;
    }
    private boolean computeRearchableFromPreds(int node) throws ContradictionException {
        boolean doneSomething = false;
        for (int v : nodesCanReach[node].getUB()) {
            //for UB, you only need that on pred may got it.
            if (!oneSupportFromUB(graph.getPotentialPredecessorOf(node), v)) {
                if(removeItemFromNode(node, v)) doneSomething = true;
            }
            if (anyMandPredAskIt(node, v) || allPotPredAskIt(node, v)) {
                if(enforceItemFromNode(node, v)) doneSomething = true;
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
            //computeRearchableFromSuccs(node);
            if(computeRIVUB(node)){
                doneSomething = true;
            }
        }
        return doneSomething;
    }
    private boolean computeRIVUB(int node)throws ContradictionException  {
        int maxUB=0;
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
        boolean smartComputation = !(potSucc.contains(idxd1) && potSucc.contains(idxd2) && trivium.getRound(idxd1)>trivium.nbInnerRound);
        if(!smartComputation){
            if(potSucc.contains(idxd1) && potSucc.contains(idxd2)){
                maxUB = Math.max(maxUB, RIV[idxd1].getUB()+RIV[idxd2].getUB());
            }
        }else
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
                sumDouble2Double = Math.min(sumDouble2Double,RIV[idxd2].getUB());

                int maxFromDouble1Succ = 0;
                if(graph.getPotentialSuccessorsOf(idxd1).contains(trivium.shift.selfSuccIndex(idxd1)))
                    maxFromDouble1Succ = Math.max(maxFromDouble1Succ,RIV[trivium.shift.selfSuccIndex(idxd1)].getUB());
                if(graph.getPotentialSuccessorsOf(idxd1).contains(trivium.shift.shortSuccIndex(idxd1)))
                    maxFromDouble1Succ = Math.max(maxFromDouble1Succ,RIV[trivium.shift.shortSuccIndex(idxd1)].getUB());
                if(graph.getPotentialSuccessorsOf(idxd1).contains(trivium.shift.double1SuccIndex(idxd1))) {
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
        maxUB = Math.min(maxUB,nodesCanReach[node].getUB().size());

        return updateUB(node,maxUB);
    }
    private boolean computeRearchableFromSuccs(int node) throws ContradictionException {
        int supportLB;
        boolean doneSomething = false;
        ISet succs = graph.getPotentialSuccessorsOf(node);
        //if(succs.contains(trivium.idxSink)) return false;//do nothing with last nodes, they are the constants
        if(succs.size() == 0){
            //System.out.println("can we go there?");//yes during first propag
            return true; //we can do better, but not our place here.
        }
        for (int v : nodesCanReach[node].getUB()) {
            if (!oneSupportFromUB(succs,v)) {
                if(removeItemFromNode(node, v)) doneSomething = true;
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
                if(enforceItemFromNode(node, v)) doneSomething = true;
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
        if(graph.getPotentialPredecessorOf(node).size()==0) return false;
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




    @Override
    public int getPropagationConditions(int vIdx) {
        return    GraphEventType.REMOVE_EDGE.getMask()
                + GraphEventType.REMOVE_NODE.getMask()// remove node is catch by removed arcs (preds and succ are removed)
                + GraphEventType.ADD_EDGE.getMask()
                + GraphEventType.ADD_NODE.getMask()//might be catch by add edge : TODO try removing this one.
                ;
    }

    @Override
    public void propagate(int idxVarInProp, int mask) throws ContradictionException {
        System.out.println("START");
        //trivium.exportArcFromCurrentState();
        for(int node:graph.getPotentialNodes()){
            if(!checkNodeHasPredsAndSuccs(node)){
                System.out.println("checkNodeHasPredsAndSuccs filtered something after all others, search node="+node+" getNodeCount:"+trivium.m.getSolver().getNodeCount());
            }
        }
        System.out.println("MID1");
        gdm.forEachEdge(arcEventRem, GraphEventType.REMOVE_EDGE);
        gdm.forEachEdge(arcEventAdd, GraphEventType.ADD_EDGE);
        gdm.forEachNode(nodeEventRem, GraphEventType.REMOVE_NODE);
        gdm.forEachNode(nodeEventAdd, GraphEventType.ADD_NODE);
        System.out.println("MID2");
        filter();
        System.out.println("MID3");
        filter();
        System.out.println("END");
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        System.out.println("In of 1st propag : ");
        filter();
        System.out.println("middle 1 of 1st propag : ");
        filter();
        System.out.println("middle 2 of 1st propag : ");
        filter();
        System.out.println("middle 3 of 1st propag : ");
        filter();
        System.out.println("Out of 1st propag.");
        gdm.startMonitoring();
    }

    @Override
    public ESat isEntailed() {
        return ESat.UNDEFINED;
    }
}
