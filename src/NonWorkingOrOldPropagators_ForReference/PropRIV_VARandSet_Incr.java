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
 * First version of the incremental propag. didnt work, tried V2 V3 and reccursiv'.
 */
public class PropRIV_VARandSet_Incr extends Propagator<Variable> {

    private final IGraphDeltaMonitor gdm;
    private final IntProcedure nodeEventAdd;
    private final IntProcedure nodeEventRem;
    private final PairProcedure arcEventAdd;
    private final PairProcedure arcEventRem;
    private int minModif;
    private int maxModif;

    private final DirectedGraphVar graph;
    private final TriviumAlban trivium;

    public final IntVar[] RIV;
    final SetVar nodesCanReach[];
    public final int NBTOREACH;


    public PropRIV_VARandSet_Incr(TriviumAlban triviumData) {
        super(new DirectedGraphVar[]{triviumData.graph}, PropagatorPriority.CUBIC, true);
        this.graph = triviumData.graph;
        this.trivium = triviumData;
        this.RIV = triviumData.RIV;
        this.NBTOREACH = triviumData.graph.getMandatoryPredecessorsOf(triviumData.idxSink).size();
        this.nodesCanReach = triviumData.RIVset;

        this.gdm = graph.monitorDelta(this);
        this.nodeEventAdd = i -> {
            newModif(i);
        };
        this.nodeEventRem = i -> {
            newModif(i);
        };
        this.arcEventAdd = (i, j) -> {
            newModif(i);
            newModif(j);
        };
        this.arcEventRem = (i, j) -> {
            newModif(i);
            newModif(j);
        };

    }
    private void newModif(int node){
        minModif = Math.min(trivium.getRound(node),minModif);
        maxModif = Math.max(trivium.getRound(node),maxModif);
    }



    private void filter() throws ContradictionException {
        for(int node:graph.getPotentialNodes()){
            if(graph.getPotentialSuccessorsOf(node).size()==0 && !trivium.isNodeSink(node)) {
                graph.removeNode(node,this);
                newModif(node);
            }
            if(graph.getPotentialPredecessorOf(node).size()==0 && !trivium.isNodeSource(node)) {
                graph.removeNode(node,this);
                newModif(node);
            }
        }
        //System.out.println("RIV IN");
        //utilitaire.graphVizExport(trivium);
        computeRivUB();
        //System.out.println("RIV MID");
        computeRivLB();
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
            //System.out.print("removing "+utilitaire.getNodeName(v)+"\tfrom "+nodesCanReach[node].getName()+"...");
            graph.removeNode(node, this);
            return true;
            //System.out.println("..done");
        }
        if(nodesCanReach[node].getUB().contains(v)){
            nodesCanReach[node].remove(v, this);
            return true;
        }
        return false;
    }
    public boolean enforceItemFromNode(int node, int v) throws ContradictionException{
        //System.out.print("enforcing "+utilitaire.getNodeName(v)+"\tfrom "+nodesCanReach[node].getName()+"...");
        if(nodesCanReach[node].getLB().contains(v)) {
            return false;//already enforced.
        }
        if(nodesCanReach[node].getUB().contains(v)){
            nodesCanReach[node].force(v, this);
            return true;//enforcing.
        }else{//this node is not valid.
            graph.removeNode(node, this);
            return true;
        }
    }

    private boolean checkNodeValidity(int node)throws ContradictionException {
        if(trivium.isNodeSink(node) || trivium.isNodeSource(node)) return true;//no check for those. (is it even needed ?)
        if (graph.getPotentialPredecessorOf(node).size() == 0) {//maybe be 'this' has remove previous nodes.
            if(graph.getPotentialNodes().contains(node)){
                //System.out.println("removing node no pred:"+node+" is mand:"+graph.getMandatoryNodes().contains(node));
                //System.out.print(node+",");
                graph.removeNode(node, this);
            }
            return false;
        }
        if (graph.getPotentialSuccessorsOf(node).size() == 0) {//maybe be 'this' has remove succ nodes.
            if(graph.getPotentialNodes().contains(node)){
                //System.out.println("removing node no succ:"+node+" is mand:"+graph.getMandatoryNodes().contains(node));
                graph.removeNode(node, this);
            }
            return false;
        }
        return true;
    }

    private void computeRivLB() throws ContradictionException {
        boolean bool1=false, bool2 = false;
        //starting from the source, we are computing each value down to the sink.
        for (int node : utilitaire.roundCroissant(trivium.graph.getPotentialNodes())) {
            if(trivium.getRound(node)<minModif-120) continue;
            if(trivium.getRound(node)>maxModif+120) return;
            if (trivium.isNodeSink(node)) continue;//constant to 0
            if (trivium.isNodeSource(node)) continue;//constant
            if (graph.getPotentialPredecessorOf(trivium.idxSink).contains(node)) continue;//constant to 1
            if (!checkNodeValidity(node)) continue;
            bool1 = computeRearchableFromPreds(node);
            bool2 = computeRIVLB(node);
            if(bool1 || bool2){
                newModif(node);
            }
        }
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

    int delta = 300;
    private void computeRivUB() throws ContradictionException {
        boolean bool1, bool2;
        //starting from the IV nodes, we are computing each value up to the source.
        for (int node : utilitaire.roundDecroissant(trivium.graph.getPotentialNodes())) {
            if(trivium.getRound(node)>maxModif+120) continue;
            //boolean wantedToSkip = trivium.getRound(node)>maxModif+0;
            if(trivium.getRound(node)<minModif-delta) return;
            if (trivium.isNodeSink(node)) continue;//should not even be updated :)
            if (graph.getPotentialPredecessorOf(trivium.idxSink).contains(node)) continue;

            //int interested=2492;
            //if(wantedToSkip && node == interested)System.out.println("before "+nodesCanReach[node]+" succs:"+graph.getPotentialSuccessorsOf(node));
            bool1 = computeRearchableFromSuccs(node);
            bool2 = computeRIVUB(node);
            //if(wantedToSkip && node == interested)System.out.println("after  "+nodesCanReach[node]+" succs:"+graph.getPotentialSuccessorsOf(node));
            if(bool1 || bool2){
                //if(wantedToSkip)System.out.println("I wanted to skip "+node +"("+utilitaire.getNodeName(node)+") maxnode was:"+maxModif + bool1+bool2);
                newModif(node);
            }
        }
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
        if(potSucc.contains(idxd1) && potSucc.contains(idxd2) && trivium.getRound(idxd1)>trivium.nbInnerRound){
            maxUB = Math.max(maxUB, RIV[idxd1].getUB()+RIV[idxd2].getUB());
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
        if(succs.size() == 0) return false; //we can do better, but not our place here.
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
        minModif = trivium.nbRound;
        maxModif = 0;

        gdm.forEachEdge(arcEventRem, GraphEventType.REMOVE_EDGE);
        gdm.forEachEdge(arcEventAdd, GraphEventType.ADD_EDGE);
        gdm.forEachNode(nodeEventRem, GraphEventType.REMOVE_NODE);
        gdm.forEachNode(nodeEventAdd, GraphEventType.ADD_NODE);
        filter();
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        minModif = -10000;
        maxModif = 10000;
        filter();
        filter();
        gdm.startMonitoring();
    }

    @Override
    public ESat isEntailed() {
        return ESat.UNDEFINED;
    }
}
