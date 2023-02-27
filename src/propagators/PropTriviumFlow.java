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
import org.chocosolver.solver.variables.Variable;
import org.chocosolver.solver.variables.delta.IGraphDeltaMonitor;
import org.chocosolver.util.ESat;
import org.chocosolver.util.objects.setDataStructures.ISet;
import org.chocosolver.util.procedure.IntProcedure;
import org.chocosolver.util.procedure.PairProcedure;
import utils.GraphEventType;

/**
 * <br/>
 *
 * @author Alban
 * @since 25/02/2023
 * this propagator ensure the correcteness and soundness (of the graph representing) of trivium
 * based on the propagator from Charles prudhomme @cprudhom
 */
public class PropTriviumFlow extends Propagator<Variable> {
    private final TriviumAlban triv;
    private final DirectedGraphVar graph;
    private final IGraphDeltaMonitor gdm;
    private final PairProcedure arcRemEvent = this::check_whenArcRemoved;
    private final PairProcedure arcAddEvent = this::check_whenArcAdded;
    private final IntProcedure nodeAddEvent = this::check_whenNodeAdded;
    private final IntProcedure nodeRemEvent = i -> {};



    public PropTriviumFlow(TriviumAlban triv) {
        super(new DirectedGraphVar[]{triv.graph}, PropagatorPriority.UNARY, true);
        this.triv = triv;
        this.graph = triv.graph;
        this.gdm = graph.monitorDelta(this);

    }

    @Override
    public int getPropagationConditions(int vIdx) {
        return GraphEventType.ALL_EVENTS;
    }

    @Override
    public void propagate(int idxVarInProp, int mask) throws ContradictionException {

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
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        checkOnPotentialNodes();
        checkOnMandatoryNodes();//same as "when arc removed" fine react function.
        check_nbSuccFromMandatoryNodes();//same as "when arc added" fine react function.
        //utilitaire.graphVizExport(triv);
        gdm.startMonitoring();
    }

    public void checkOnPotentialNodes()throws ContradictionException{
        boolean doneSomething = false;
        for(int node:graph.getPotentialNodes()){
            if((graph.getPotentialSuccessorsOf(node).size()==0 && !triv.isNodeSink(node))||
               (graph.getPotentialPredecessorOf(node).size()==0 && !triv.isNodeSource(node))){
                graph.removeNode(node,this);
                doneSomething = true;
            }
        }
        if(doneSomething)checkOnPotentialNodes();
    }


    public void checkOnMandatoryNodes() throws ContradictionException{

        for(int node:graph.getMandatoryNodes()) {
            //RULES of predecessor :
            // there is at least one, so enforce it if it is the only one.
            ISet preds = graph.getPotentialPredecessorOf(node);
            if (preds.size() == 1 && !graph.getMandatoryPredecessorsOf(node).contains(preds.min())) {
                graph.enforceEdge(preds.min(), node, this);
            }
            else if (preds.size() == 0 && !triv.isNodeSource(node)) {//and fails if none.
                this.fails();
            }
            //RULES OF SUCCESSOR.
            //rules 1 : no rules for the sink succ.
            if(triv.isNodeSink(node)) continue;
            ISet potSuccs = graph.getPotentialSuccessorsOf(node);
            //rules 2 : there is at least one
            if(potSuccs.size()==0){
                this.fails();
            }
            else if(potSuccs.size()==1){ //enforce it if there is only one potential left.
                if(!graph.getMandatorySuccessorsOf(node).contains(potSuccs.min())){
                    graph.enforceEdge(node,potSuccs.min(),this);
                }
            }
            //rules 3 enforce doubling if  there is only those 2 potential left.
            else if(potSuccs.size()==2){
                if(triv.isArcDoubling(node, potSuccs.min()) &&
                   triv.isArcDoubling(node, potSuccs.max()) ){
                    if(!graph.getMandatorySuccessorsOf(node).contains(potSuccs.min())){
                        graph.enforceEdge(node,potSuccs.min(),this);
                    }
                    if(!graph.getMandatorySuccessorsOf(node).contains(potSuccs.max())) {
                        graph.enforceEdge(node, potSuccs.max(), this);
                    }
                }
            }
        }
    }
    public void check_nbSuccFromMandatoryNodes()throws ContradictionException{
        for(int node:graph.getMandatoryNodes()) {
            ISet mandSuccs = graph.getMandatorySuccessorsOf(node);

            if(mandSuccs.size()==1 && triv.isArcDoubling(node,mandSuccs.min())){
                graph.enforceEdge(node,triv.getOtherDoubling(node,mandSuccs.min()),this);
                mandSuccs = graph.getMandatorySuccessorsOf(node);//we have change this Set : refresh.
            }
            if(mandSuccs.size()==2){//check that if 2 then it is the doubling
                if(!(triv.isArcDoubling(node, mandSuccs.min()) &&
                        triv.isArcDoubling(node, mandSuccs.max()) )){
                    this.fails();
                }
            }
            if(mandSuccs.size()>2){//never more than 2.
                this.fails();
            }

            //if there is a mandatory, remove other one from potentials (you need to be sure that both doubling are here, hence after previous check.
            if(mandSuccs.size()>0) {
                for (int otherSucc : graph.getPotentialSuccessorsOf(node)) {
                    if (!mandSuccs.contains(otherSucc)) {
                        graph.removeEdge(node, otherSucc, this);
                    }
                }
            }
        }
    }

    public void check_whenArcAdded(int from, int to)throws ContradictionException{
        //if we add a doubling, add the other one.
        if(triv.isArcDoubling(from,to) &&!graph.getMandatorySuccessorsOf(from).contains(triv.getOtherDoubling(from,to))){
            graph.enforceEdge(from,triv.getOtherDoubling(from,to),this);
        }

        ISet mandSuccs = graph.getMandatorySuccessorsOf(from);
        if(mandSuccs.size()>2){//never more than 2.
            this.fails();
        } else if(mandSuccs.size()==2){//check that if 2 then it is the doubling
            if(!(triv.isArcDoubling(from, mandSuccs.min()) &&
                    triv.isArcDoubling(from, mandSuccs.max()) )){
                this.fails();
            }
        }

        for (int otherSucc : graph.getPotentialSuccessorsOf(from)) {
            if (!mandSuccs.contains(otherSucc)) {
                graph.removeEdge(from, otherSucc, this);
            }
        }
    }
    public void check_whenArcRemoved(int from,int to) throws ContradictionException{

        int other = triv.getOtherDoubling(from,to);
        if(triv.isArcDoubling(from, to) && graph.getPotentialSuccessorsOf(from).contains(other)){
            graph.removeEdge(from, other,this);
        }

        //looking for succ of nodes "from"
        ISet Succs = graph.getPotentialSuccessorsOf(from);
        if(Succs.size()==0 && !graph.getPotentialNodes().contains(from)){//no more left : fails
            graph.removeNode(from, this);
        }
        if (Succs.size()==1 && graph.getMandatoryNodes().contains(from) &&!graph.getMandatorySuccessorsOf(from).contains(Succs.min())) {//one left only : enforce.
            graph.enforceEdge(from, Succs.min(), this);
        }
        if (Succs.size()==2 && graph.getMandatoryNodes().contains(from)) {
            //if 2 succ     re doubling, enforce them.
            if(triv.isArcDoubling(from, Succs.min()) && triv.isArcDoubling(from, Succs.max())){
                if(!graph.getMandatorySuccessorsOf(from).contains(Succs.min())) {
                    graph.enforceEdge(from, Succs.min(), this);
                }
                if(!graph.getMandatorySuccessorsOf(from).contains(Succs.max())) {
                    graph.enforceEdge(from, Succs.max(), this);
                }
            }
        }

        //looking for preds of node "to"
        ISet Preds = graph.getPotentialPredecessorOf(to);
        if(Preds.size()==0 && graph.getPotentialNodes().contains(to)){
            graph.removeNode(to, this);
        }
        if (Preds.size()==1 && graph.getMandatoryNodes().contains(to) &&!graph.getMandatorySuccessorsOf(Preds.min()).contains(to)) {
            graph.enforceEdge(Preds.min(),to, this);
        }
    }
    public void check_whenNodeAdded(int node)throws ContradictionException{

        ISet potSuccs = graph.getPotentialSuccessorsOf(node);
        if(potSuccs.size()==0){
            this.fails();
        }
        else if(potSuccs.size()==1){ //enforce it if there is only one potential left.
            graph.enforceEdge(node,potSuccs.min(),this);
        } else if(potSuccs.size()==2){//enforce doubling if  there is only those 2 potential left.
            if(triv.isArcDoubling(node, potSuccs.min()) && triv.isArcDoubling(node, potSuccs.max())){
                if(!graph.getMandatorySuccessorsOf(node).contains(potSuccs.min())){
                    graph.enforceEdge(node,potSuccs.min(),this);
                }
                if(!graph.getMandatorySuccessorsOf(node).contains(potSuccs.max())) {
                    graph.enforceEdge(node, potSuccs.max(), this);
                }
            }
        }
        ISet preds = graph.getPotentialPredecessorOf(node);
        if (preds.size() == 0) {//and fails if none.
            this.fails();
        }else if (preds.size() == 1 && !graph.getMandatorySuccessorsOf(preds.min()).contains(node)) {
            graph.enforceEdge(preds.min(), node, this);
        }

    }


    @Override
    public ESat isEntailed() {
        return ESat.UNDEFINED;
    }
}