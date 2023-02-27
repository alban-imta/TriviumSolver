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
 * @author Alban DERRIEN
 * @since 01/03/2023
 * first step to work on the modulo information. its of no interest i guess : delete or ignore this file.
 */
public class PropTrio_alban extends Propagator<Variable> {

    final DirectedGraphVar graph;
    final TriviumAlban trivium;
    //to add a change !
    int numberOfZeroDoubling,numberOfTwoDoubling,numberOfOneDoubling;


    public PropTrio_alban(TriviumAlban triviumData) {
        super(new DirectedGraphVar[]{triviumData.graph}, PropagatorPriority.LINEAR, false);
        this.graph = triviumData.graph;
        this.trivium = triviumData;
        computeNumberOfNodePerTrio();
    }


    int nZero,nOne,nTwo;
    public void computeNumberOfNodePerTrio(){
        nZero=0;
        nOne=0;
        nTwo=0;
        System.out.println("Mandatory nodes:");
        for(int i:graph.getMandatoryNodes()){
            System.out.println(i);
        }
        System.out.println("----");
        for(int i=1;i<=80;i++){
            int j = (i+trivium.nbInnerRound+1000);
            if(!graph.getPotentialNodes().contains(j)) continue;
            System.out.println(j);
            int m = (i+trivium.nbInnerRound)%3;
            if(m==0){
                nZero++;
            }else if(m==1){
                nOne++;
            }else {
                nTwo++;
            }
        }
        //correction d'un etat pour test.
        //nTwo++;
        System.out.println("nZero="+nZero);
        System.out.println("nOne="+nOne);
        System.out.println("nTwo corrigé="+nTwo);
        numberOfZeroDoubling = (nOne+nTwo)/2;
        numberOfOneDoubling = (nZero+nTwo-1)/2;
        numberOfTwoDoubling = (nZero+nOne-1)/2;
        System.out.println("numberOfZeroDoubling="+numberOfZeroDoubling);
        System.out.println("numberOfOneDoubling="+numberOfOneDoubling);
        System.out.println("numberOfTwoDoubling="+numberOfTwoDoubling);
    }


    private void filter() throws ContradictionException {
        for(int node:graph.getPotentialNodes()){
            if(graph.getPotentialSuccessorsOf(node).size()==0 && !trivium.isNodeSink(node)) graph.removeNode(node,this);
            if(graph.getPotentialPredecessorOf(node).size()==0 && !trivium.isNodeSource(node)) graph.removeNode(node,this);
        }
        //System.out.println("RIV INIT");
        int cpt0=0;
        int cpt1=0;
        int cpt2=0;
        //1st count them
        for(int node:graph.getMandatoryNodes()){
            if(graph.getMandatorySuccessorsOf(node).size()>0){
                if(trivium.isArcDoubling(node, graph.getMandatorySuccessorsOf(node).min())){
                    int m = utilitaire.getModuloTroisOfNode(node);
                    if(m==0){
                        cpt0++;
                    }else if(m==1){
                        cpt1++;
                    }else if (m==2){
                        cpt2++;
                    }else{
                        System.out.println("bug PropTrio_alban error 1 : got "+m);
                    }
                }
            }
        }
        for (int node : graph.getPotentialNodes()) {
            if (utilitaire.getModuloTroisOfNode(node)==0 && cpt0==numberOfZeroDoubling){
                removePotentialDoubling(node);
            }
            if (utilitaire.getModuloTroisOfNode(node)==1 && cpt1==numberOfOneDoubling){
                removePotentialDoubling(node);
            }
            if (utilitaire.getModuloTroisOfNode(node)==2 && cpt2==numberOfTwoDoubling){
                removePotentialDoubling(node);
            }
        }

        //System.out.println("RIV OUT");
    }
    public void removePotentialDoubling(int node) throws ContradictionException {
        if(graph.getMandatorySuccessorsOf(node).size()==0){//remove only if not already set.
            for(int succ:trivium.getDoublingSucc(node)){
                graph.removeEdge(node,succ,this);
            }
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
    }

    @Override
    public ESat isEntailed() {
        return ESat.UNDEFINED;
    }
}
