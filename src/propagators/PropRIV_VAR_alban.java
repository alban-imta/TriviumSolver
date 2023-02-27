/*
 * This file is part of choco-solver, http://choco-solver.org/
 *
 * Copyright (c) 2020, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package propagators;

import main.TriviumAlban;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.DirectedGraphVar;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.Variable;
import org.chocosolver.util.ESat;
import org.chocosolver.util.objects.setDataStructures.ISet;
import utils.GraphEventType;
import utils.utilitaire;

/**
 * <br/>
 *
 * @author Alban DERRIEN
 * @since 01/03/2023
 * Compute the Reacheable IV, using one (IntVar) variable for each node
 */
public class PropRIV_VAR_alban extends Propagator<Variable> {

    private final DirectedGraphVar graph;
    private final TriviumAlban trivium;

    public final IntVar[] RIV;
    public final int NBTOREACH;


    public PropRIV_VAR_alban(TriviumAlban triviumData) {
        super(new DirectedGraphVar[]{triviumData.graph}, PropagatorPriority.CUBIC, false);
        this.graph = triviumData.graph;
        this.trivium = triviumData;
        this.RIV = triviumData.RIV;
        this.NBTOREACH = triviumData.graph.getMandatoryPredecessorsOf(triviumData.idxSink).size();
    }




    private void filter() throws ContradictionException {
        for(int node:graph.getPotentialNodes()){
            if(graph.getPotentialSuccessorsOf(node).size()==0 && !trivium.isNodeSink(node)) graph.removeNode(node,this);
            if(graph.getPotentialPredecessorOf(node).size()==0 && !trivium.isNodeSource(node)) graph.removeNode(node,this);
        }
        //System.out.println("RIV IN");
        //utilitaire.graphVizExport(trivium);
        computeRivUB();
        //System.out.println("RIV MID");
        computeRivLB();

        linkWithRIVSet();
        //utilitaire.graphVizExport(trivium,this);
        //System.out.println("RIV OUT");
        //utilitaire.graphVizExport(trivium,this);
    }
    private void linkWithRIVSet() throws ContradictionException {
        for(int n:graph.getPotentialNodes()){
            updateLB(n,trivium.RIVset[n].getLB().size());
            updateUB(n,trivium.RIVset[n].getUB().size());
        }
    }
    private void updateLB(int node, int newlb) throws ContradictionException {
        if(newlb>RIV[node].getUB()){//useless we haveremove all arcs, but it is logical.
            //2  System.out.println("RIV removing node:"+node);
            graph.removeNode(node,this);//filtering 3/3
        }else{
            RIV[node].updateLowerBound(newlb,this);
        }
    }
    private void updateUB(int node, int newub) throws ContradictionException {
        if(newub<RIV[node].getLB()){//useless we haveremove all arcs, but it is logical.
            //2  System.out.println("RIV removing node:"+node);
            graph.removeNode(node,this);//filtering 3/3
        }else{
            RIV[node].updateUpperBound(newub,this);
        }
    }

    private void computeRivLB() throws ContradictionException {
        //starting from the source, we are computing each value down to the sink.
        for (int node : utilitaire.roundCroissant(trivium.graph.getPotentialNodes())) {
            if (trivium.isNodeSink(node)) continue;//constant to 0
            if (trivium.isNodeSource(node)) continue;//constant
            if (graph.getPotentialPredecessorOf(trivium.idxSink).contains(node)) continue;//constant to 1
            computeRIVLB(node);
        }
    }
    private void computeRIVLB(int node) throws ContradictionException {
        if (graph.getPotentialPredecessorOf(node).size() == 0) {//maybe be 'this' has remove previous nodes.
            if(graph.getPotentialNodes().contains(node)){
                graph.removeNode(node, this);
            }
            return;
        }
        if (graph.getPotentialSuccessorsOf(node).size() == 0) {//maybe be 'this' has remove succ nodes.
            if(graph.getPotentialNodes().contains(node)){
                graph.removeNode(node, this);
            }
        }
        int newLB;
        int minPredLB=NBTOREACH;
        for (int p : graph.getPotentialPredecessorOf(node)) {
            if (trivium.isArcDoubling(p, node)) {
                int doubling2 = trivium.getOtherDoubling(p, node);
                if(!graph.getPotentialNodes().contains(doubling2)) {
                    graph.removeEdge(p,node,this);//filtering 1/3
                    continue;
                }
                newLB = RIV[p].getLB() - RIV[doubling2].getUB();
            } else {
                newLB = RIV[p].getLB();
            }
            if(newLB>RIV[node].getUB()){
                graph.removeEdge(p,node,this);//filtering 2/3
            }
            minPredLB = Math.min(minPredLB,newLB );
        }
        updateLB(node, minPredLB);
    }

    private void computeRivUB() throws ContradictionException {
        //starting from the IV nodes, we are computing each value up to the source.
        for (int node : utilitaire.roundDecroissant(trivium.graph.getPotentialNodes())) {
            if (trivium.isNodeSink(node)) continue;
            if (graph.getPotentialPredecessorOf(trivium.idxSink).contains(node)) continue;
            computeRIVUB(node);
        }
    }
    private void computeRIVUB(int node)throws ContradictionException  {
        int maxUB=0;
        //basic version is max of successors
        ISet potSucc = trivium.graph.getPotentialSuccessorsOf(node);
        for (int succ : potSucc) {
            maxUB = Math.max(maxUB, RIV[succ].getUB());
        }//may test for not doubling, is it faster ?
        //but for doubling, it is the sum of both !

        int idxd1 = trivium.shift.double1SuccIndex(node);
        int idxd2 = trivium.shift.double2SuccIndex(node);
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
        updateUB(node,maxUB);
    }


    @Override
    public int getPropagationConditions(int vIdx) {
        return GraphEventType.REMOVE_EDGE.getMask() + GraphEventType.ADD_NODE.getMask();
    }

    @Override
    public void propagate(int idxVarInProp, int mask) throws ContradictionException {
        filter();
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        filter();
        filter();
    }

    @Override
    public ESat isEntailed() {
        return ESat.TRUE;
    }
}
