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
import org.chocosolver.util.objects.setDataStructures.ISet;
import utils.GraphEventType;
import utils.utilitaire;

import java.util.Arrays;

/**
 * <br/>
 *
 * @author Alban DERRIEN
 * @since 01/03/2022
 * First version of the RIV propagator. have been upgraded to variable version.
 */
public class PropRIV_alban extends Propagator<Variable> {

    final DirectedGraphVar graph;
    final TriviumAlban trivium;
    //to add a change !


    public PropRIV_alban(TriviumAlban triviumData) {
        super(new DirectedGraphVar[]{triviumData.graph}, PropagatorPriority.LINEAR, false);
        this.graph = triviumData.graph;
        this.trivium = triviumData;
    }


    public int[] RivUB;
    public int[] RivLB;

    private void filter() throws ContradictionException {
        for(int node:graph.getPotentialNodes()){
            if(graph.getPotentialSuccessorsOf(node).size()==0 && !trivium.isNodeSink(node)) graph.removeNode(node,this);
            if(graph.getPotentialPredecessorOf(node).size()==0 && !trivium.isNodeSource(node)) graph.removeNode(node,this);
        }
        //System.out.println("RIV INIT");
        initRIV();
        //System.out.println("RIV IN");
        //utilitaire.graphVizExport(trivium);
        computeRivUB();
        //System.out.println("RIV MID");
        computeRivLB();
        //utilitaire.graphVizExport(trivium,this);
        //System.out.println("RIV OUT");
        //utilitaire.graphVizExport(trivium,this);
    }

    public void initRIV(){
        RivUB = new int[graph.getNbMaxNodes()];
        Arrays.fill(RivUB, 0);
        for (int i : graph.getPotentialPredecessorOf(trivium.idxSink)) {
            RivUB[i] = 0;
        }
        for (int i : trivium.instance.iv) {
            RivUB[i + trivium.nbInnerRound + trivium.nbMaxNodePerRegistre] = 1;
        }

        RivLB = new int[graph.getNbMaxNodes()];
        Arrays.fill(RivLB, 80);
        RivLB[trivium.idxSource] = trivium.instance.nAct;
    }
    public void printState(int node){
       //2  System.out.println("state of node:"+node +" is mandatory:"+graph.getMandatoryNodes().contains(node));
       //2  System.out.println("potentia pred:"+graph.getPotentialPredecessorOf(node));
       //2  System.out.println("mandator pred:"+graph.getMandatoryPredecessorsOf(node));
       //2  System.out.println("potentia succ:"+graph.getPotentialSuccessorsOf(node));
       //2  System.out.println("mandator succ:"+graph.getMandatorySuccessorsOf(node));
    }
    private void computeRivLB() throws ContradictionException {
        //starting from the source, we are computing each value down to the sink.
        for (int node : utilitaire.roundCroissant(trivium.graph.getPotentialNodes())) {
            if (trivium.isNodeSink(node)) continue;
            if (trivium.isNodeSource(node)) continue;
            computeRIVLB(node);
        }
    }

    private void computeRIVLB(int node) throws ContradictionException {
        if (graph.getPotentialPredecessorOf(node).size() == 0) {//maybe be 'this' has remove previous nodes.
            RivLB[node]=0;
            RivUB[node]=80;
            if(graph.getPotentialNodes().contains(node)){
                //System.out.println("removing node no pred:"+node+" is mand:"+graph.getMandatoryNodes().contains(node));
                //System.out.print(node+",");
                graph.removeNode(node, this);
                //System.out.print("DONE 1");
            }
            return;
        }
        if (graph.getPotentialSuccessorsOf(node).size() == 0) {//maybe be 'this' has remove succ nodes.
            RivLB[node]=0;
            RivUB[node]=80;
            if(graph.getPotentialNodes().contains(node)){
                //System.out.println("removing node no succ:"+node+" is mand:"+graph.getMandatoryNodes().contains(node));
                graph.removeNode(node, this);
                //System.out.print("DONE 2");
            }
            //return;
        }
        int newLB;
        for (int p : graph.getPotentialPredecessorOf(node)) {
            if (trivium.isArcDoubling(p, node)) {
                int doubling2 = trivium.getOtherDoubling(p, node);
                if(!graph.getPotentialNodes().contains(doubling2)) {
                   //2  System.out.println("RIV removing arc1:"+p +" :"+node);
                    graph.removeEdge(p,node,this);//filtering 1/2
                    continue;
                }
                newLB = RivLB[p] - RivUB[doubling2];
            } else {
                newLB = RivLB[p];
            }
            if(newLB>RivUB[node]){
               //2  System.out.println("RIV removing arc2:"+p +" :"+node);
                graph.removeEdge(p,node,this);//filtering 2/2
            }
            RivLB[node] = Math.min(RivLB[node],newLB );
        }
        RivLB[node] = Math.max(RivLB[node], 0);

        //useless we have already removed all arcs.
        //if (RivUB[node] < RivLB[node]) {
        //    graph.removeNode(node, this);
        //}
    }

    private void computeRivUB() throws ContradictionException {
        //starting from the IV nodes, we are computing each value up to the source.
        for (int node : utilitaire.roundDecroissant(trivium.graph.getPotentialNodes())) {
            computeRIVUB(node);
        }
        if (RivUB[trivium.idxSource] < trivium.instance.nAct) {
            //System.out.println("RIV UB fails.");
            this.fails();
            //System.out.print("DONE 3");
        }
    }
    private void computeRIVUB(int round) {
        //basic version is max of successors
        ISet potSucc = trivium.graph.getPotentialSuccessorsOf(round);
        for (int succ : potSucc) {
            RivUB[round] = Math.max(RivUB[round], RivUB[succ]);
        }//may test for not doubling, is it faster ?
        //but for doubling, it is the sum of both !

        int double1 = trivium.shift.double1SuccIndex(round);
        int double2 = trivium.shift.double2SuccIndex(round);


        //Fast computation (from arthur) : sum of both doubling succ.
        //if(potSucc.contains(double1) && potSucc.contains(double2) ){
        //    RivUB[round] = Math.max(RivUB[round], RivUB[double1]+RivUB[double2]);
        //}
        //return;

        //no smart computation if we are at the last nodes.
        if(potSucc.contains(double1) && potSucc.contains(double2)&&trivium.getRound(double1)>trivium.nbInnerRound){
            RivUB[round] = Math.max(RivUB[round], RivUB[double1]+RivUB[double2]);
        }else
        //smart computation (from arthur) : computing one step after for doubling
        //because some idx are the same and thus count twice !
        if (potSucc.contains(double1)) {
            //succ of double2 from short, self and long are not overlapping with any of double1 succ.
            //so compute direct with double1.
            int nextStepIdx = trivium.shift.shortSuccIndex(double2);
            if (graph.getPotentialSuccessorsOf(double2).contains(nextStepIdx)) {
                RivUB[round] = Math.max(RivUB[round], RivUB[double1] + RivUB[nextStepIdx]);
            }
            nextStepIdx = trivium.shift.selfSuccIndex(double2);
            if (graph.getPotentialSuccessorsOf(double2).contains(nextStepIdx)) {
                RivUB[round] = Math.max(RivUB[round], RivUB[double1] + RivUB[nextStepIdx]);
            }
            nextStepIdx = trivium.shift.longSuccIndex(double2);
            if (graph.getPotentialSuccessorsOf(double2).contains(nextStepIdx)) {
                RivUB[round] = Math.max(RivUB[round], RivUB[double1] + RivUB[nextStepIdx]);
            }

            if (graph.getPotentialSuccessorsOf(double2).contains(trivium.shift.double1SuccIndex(double2))) {
                //but after doublingSucc of double2, some may overlap with succ of double1.
                int sumDouble2Double = RivUB[trivium.shift.double1SuccIndex(double2)] +
                        RivUB[trivium.shift.double2SuccIndex(double2)];
                //if(sumDouble2Double>RivUB[double2]) System.out.println("greater Than");
                sumDouble2Double = Math.min(sumDouble2Double,RivUB[double2]);

                int maxFromDouble1Succ = 0;
                if(graph.getPotentialSuccessorsOf(double1).contains(trivium.shift.selfSuccIndex(double1)))
                    maxFromDouble1Succ = Math.max(maxFromDouble1Succ,RivUB[trivium.shift.selfSuccIndex(double1)]);
                if(graph.getPotentialSuccessorsOf(double1).contains(trivium.shift.shortSuccIndex(double1)))
                    maxFromDouble1Succ = Math.max(maxFromDouble1Succ,RivUB[trivium.shift.shortSuccIndex(double1)]);
                if(graph.getPotentialSuccessorsOf(double1).contains(trivium.shift.double1SuccIndex(double1))) {
                    int riv = RivUB[trivium.shift.double1SuccIndex(double1)];
                    //nono watch iv_672_1
                    // int penality = Math.max(0, -RivUB[double1] +RivUB[trivium.shift.double1SuccIndex(double1)] +RivUB[trivium.shift.double2SuccIndex(double1)]);
                    //maxFromDouble1Succ = Math.max(maxFromDouble1Succ, riv-penality);
                    maxFromDouble1Succ = Math.max(maxFromDouble1Succ, riv);
                }
                RivUB[round] = Math.max(RivUB[round], sumDouble2Double + maxFromDouble1Succ);
            }
        }
    }

    public void printRIV() {
        for (int round = trivium.nbMaxNodePerRegistre; round >= 0; round--) {
           //2  System.out.println(round + "\t" + RivUB[round] + "\t" + RivUB[round + trivium.nbMaxNodePerRegistre] + "\t" + RivUB[round + 2 * trivium.nbMaxNodePerRegistre]);
        }
    }


    @Override
    public int getPropagationConditions(int vIdx) {
        return GraphEventType.REMOVE_EDGE.getMask() + GraphEventType.ADD_NODE.getMask();
    }

    @Override
    public void propagate(int idxVarInProp, int mask) throws ContradictionException {
        propagate(mask);
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        filter();
        //filter();
    }

    @Override
    public ESat isEntailed() {
        return ESat.TRUE;
    }
}
