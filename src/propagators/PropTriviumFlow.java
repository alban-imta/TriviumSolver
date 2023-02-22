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
 * @author Charles Prud'homme
 * @since 25/11/2020
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
    public PropTriviumFlow(DirectedGraphVar subGraph, TriviumAlban trivInfos) {
        super(new DirectedGraphVar[]{subGraph}, PropagatorPriority.UNARY, true);
        this.triv = trivInfos;
        this.graph = subGraph;
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
        //System.out.println("end of Calling PropTriviumFlow");
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        //2System.out.println("Calling !");
       //printState(467);
        checkOnPotentialNodes();
        checkOnMandatoryNodes();//same as "when arc removed" fine react function.
        check_nbSuccFromMandatoryNodes();//same as "when arc added" fine react function.
        //check_NodesNbArc();//check if a node can not be link to another one.
        //printState(467);
        //utilitaire.graphVizExport(triv);
        gdm.startMonitoring();
    }

    public void assertOnlyOnePred() throws ContradictionException{

        for(int node:graph.getMandatoryNodes()) {
            if(triv.isNodeSink(node)) continue;
            /*
            if(graph.getPotentialPredecessorOf(node).size()==1) {
                graph.enforceEdge(graph.getPotentialPredecessorOf(node).min(),node,this);
                continue;
            }
            if(graph.getMandatoryPredecessorsOf(node).size()==0) continue;
            */
            if(graph.getMandatoryPredecessorsOf(node).size()>1) this.fails();


        }
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
                //2System.out.println("enforce arc9:"+preds.min()+" :"+node);
                graph.enforceEdge(preds.min(), node, this);
            }
            else if (preds.size() == 0 && !triv.isNodeSource(node)) {//and fails if none.
                //2System.out.println("Fail7 :"+node);
                this.fails();
            }
            //RULES OF SUCCESSOR.
            //rules 1 : no rules for the sink succ.
            if(triv.isNodeSink(node)) continue;
            ISet potSuccs = graph.getPotentialSuccessorsOf(node);
            //rules 2 : there is at least one
            if(potSuccs.size()==0){
                //2System.out.println("Fail8 :"+node);
                this.fails();
            }
            else if(potSuccs.size()==1){ //enforce it if there is only one potential left.
                if(!graph.getMandatorySuccessorsOf(node).contains(potSuccs.min())){
                    //2System.out.println("enforce arc6:"+node+" :"+potSuccs.min()+" coz only succ");
                    graph.enforceEdge(node,potSuccs.min(),this);
                }
            }
            //rules 3 enforce doubling if  there is only those 2 potential left.
            else if(potSuccs.size()==2){
                if(triv.isArcDoubling(node, potSuccs.min()) &&
                   triv.isArcDoubling(node, potSuccs.max()) ){
                    if(!graph.getMandatorySuccessorsOf(node).contains(potSuccs.min())){
                        //2System.out.println("enforce arc5a:"+node+" :"+potSuccs.min());
                        graph.enforceEdge(node,potSuccs.min(),this);
                    }
                    if(!graph.getMandatorySuccessorsOf(node).contains(potSuccs.max())) {
                        //2System.out.println("enforce arc5b:" + node + " :"+potSuccs.max());
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
                    //2System.out.println("Fail1:"+node+" mand succs:"+mandSuccs);
                    this.fails();
                }
            }
            if(mandSuccs.size()>2){//never more than 2.
                //2System.out.println("Fail2");
                this.fails();
            }

            //if there is a mandatory, remove other one from potentials (you need to be sure that both doubling are here, hence after previous check.
            if(mandSuccs.size()>0) {
                for (int otherSucc : graph.getPotentialSuccessorsOf(node)) {
                    if (!mandSuccs.contains(otherSucc)) {
                        //2System.out.println("removing arc1:"+node+"-"+otherSucc);
                        graph.removeEdge(node, otherSucc, this);
                    }
                }
            }
        }
    }
    public void check_NodesNbArc()throws ContradictionException{
        for(int node:graph.getPotentialNodes()) {
            if(triv.isNodeSink(node)) continue;
            if(triv.isNodeSource(node)) continue;
            if(graph.getPotentialSuccessorsOf(node).size()==0 || graph.getPotentialPredecessorOf(node).size()==0){
                graph.removeNode(node,this);
            }
        }
    }


    public void printState(int node){
        //2System.out.println("state of node:"+node +" is mandatory:"+graph.getMandatoryNodes().contains(node));
        //2System.out.println("potentia pred:"+graph.getPotentialPredecessorOf(node));
        //2System.out.println("mandator pred:"+graph.getMandatoryPredecessorsOf(node));
        //2System.out.println("potentia succ:"+graph.getPotentialSuccessorsOf(node));
        //2System.out.println("mandator succ:"+graph.getMandatorySuccessorsOf(node));
    }
    public void check_whenArcAdded(int from, int to)throws ContradictionException{
        //if we add a doubling, add the other one.
        if(triv.isArcDoubling(from,to) &&!graph.getMandatorySuccessorsOf(from).contains(triv.getOtherDoubling(from,to))){
            //2System.out.println("enforce arc4:"+from+" :"+to+" coz arc was added:"+from+":"+to);
            graph.enforceEdge(from,triv.getOtherDoubling(from,to),this);
        }

        ISet mandSuccs = graph.getMandatorySuccessorsOf(from);
        if(mandSuccs.size()>2){//never more than 2.
            //2System.out.println("Fail3 :"+from+" :"+to+" coz arc was added:"+from+":"+to);
            this.fails();
        } else if(mandSuccs.size()==2){//check that if 2 then it is the doubling
            if(!(triv.isArcDoubling(from, mandSuccs.min()) &&
                    triv.isArcDoubling(from, mandSuccs.max()) )){
                //2System.out.println("Fail4 :"+from+" :"+to+" coz arc was added:"+from+":"+to);
                this.fails();
            }
        }

        for (int otherSucc : graph.getPotentialSuccessorsOf(from)) {
            if (!mandSuccs.contains(otherSucc)) {
                //2System.out.println("removing arc2:"+from+" :"+otherSucc+" coz arc was added:"+from+":"+to);
                graph.removeEdge(from, otherSucc, this);
            }
        }
    }
    public void check_whenArcRemoved(int from,int to) throws ContradictionException{

        int other = triv.getOtherDoubling(from,to);
        if(triv.isArcDoubling(from, to) && graph.getPotentialSuccessorsOf(from).contains(other)){
            //2System.out.println("removing arc3:"+from+":"+ triv.getOtherDoubling(from,to)+" coz arc was removed:"+from+":"+to);
            graph.removeEdge(from, other,this);
        }

        //looking for succ of nodes "from"
        ISet Succs = graph.getPotentialSuccessorsOf(from);
        if(Succs.size()==0 && !graph.getPotentialNodes().contains(from)){//no more left : fails
            //System.out.println("removing node5:"+from+" coz arc was removed:"+from+":"+to);
            graph.removeNode(from, this);
        }
        if (Succs.size()==1 && graph.getMandatoryNodes().contains(from) &&!graph.getMandatorySuccessorsOf(from).contains(Succs.min())) {//one left only : enforce.
            //2System.out.println("enforce arc3:"+from+" :"+Succs.min()+" coz arc was removed:"+from+":"+to);
            graph.enforceEdge(from, Succs.min(), this);
        }
        if (Succs.size()==2 && graph.getMandatoryNodes().contains(from)) {
            //if 2 succ     re doubling, enforce them.
            if(triv.isArcDoubling(from, Succs.min()) && triv.isArcDoubling(from, Succs.max())){
                if(!graph.getMandatorySuccessorsOf(from).contains(Succs.min())) {
                    //2System.out.println("enforce arc1a:" + from + " :" + Succs.min() + " coz arc was removed:" + from + ":" + to);
                    graph.enforceEdge(from, Succs.min(), this);
                }
                if(!graph.getMandatorySuccessorsOf(from).contains(Succs.max())) {
                    //2System.out.println("enforce arc1b:" + from + " :" + Succs.max() + " coz arc was removed:" + from + ":" + to);
                    graph.enforceEdge(from, Succs.max(), this);
                }
            }
        }

        //looking for preds of node "to"
        ISet Preds = graph.getPotentialPredecessorOf(to);
        if(Preds.size()==0 && graph.getPotentialNodes().contains(to)){

            //System.out.print(to+",");
            graph.removeNode(to, this);
        }
        if (Preds.size()==1 && graph.getMandatoryNodes().contains(to) &&!graph.getMandatorySuccessorsOf(Preds.min()).contains(to)) {
            //2System.out.println("enforce arc2:"+Preds.min()+" :"+to+" coz arc was removed:"+from+":"+to);
            graph.enforceEdge(Preds.min(),to, this);
        }
    }
    public void check_whenNodeAdded(int node)throws ContradictionException{

        ISet potSuccs = graph.getPotentialSuccessorsOf(node);
        if(potSuccs.size()==0){
            //2System.out.println("Fail5 :"+node);
            this.fails();
        }
        else if(potSuccs.size()==1){ //enforce it if there is only one potential left.
            graph.enforceEdge(node,potSuccs.min(),this);
        } else if(potSuccs.size()==2){//enforce doubling if  there is only those 2 potential left.
            if(triv.isArcDoubling(node, potSuccs.min()) && triv.isArcDoubling(node, potSuccs.max())){
                if(!graph.getMandatorySuccessorsOf(node).contains(potSuccs.min())){
                    //2System.out.println("enforce arc7a:"+node+" :"+potSuccs.min());
                    graph.enforceEdge(node,potSuccs.min(),this);
                }
                if(!graph.getMandatorySuccessorsOf(node).contains(potSuccs.max())) {
                    //2System.out.println("enforce arc7b:" + node + " :" + potSuccs.max());
                    graph.enforceEdge(node, potSuccs.max(), this);
                }
            }
        }
        ISet preds = graph.getPotentialPredecessorOf(node);
        if (preds.size() == 0) {//and fails if none.
            //2System.out.println("Fail6 :"+node);
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

//source->B82[color=orange]; source->B83[color=orange]; B82->A173[color=orange]; B82->A174[color=orange]; B83->B161[color=orange]; B161->A252[color=orange]; B161->A253[color=orange]; A173->C239[color=orange]; A174->C283[color=orange]; A174->C284[color=orange]; C239->B321[color=orange]; C239->B322[color=orange]; A252->C318[color=orange]; A253->C362[color=orange]; A253->C363[color=orange]; C283->B365[color=orange]; C283->B366[color=orange]; C284->B353[color=orange]; C318->B402[color=orange]; B321->A387[color=orange]; B322->A413[color=orange]; B322->A414[color=orange]; B353->A446[color=orange]; C362->B444[color=orange]; C362->B445[color=orange]; C363->C450[color=orange]; B365->A431[color=orange]; B366->A457[color=orange]; B366->A458[color=orange]; A387->C496[color=orange]; A387->C497[color=orange]; B402->A495[color=orange]; A413->A482[color=orange]; A414->C525[color=orange]; A431->C542[color=orange]; B444->A510[color=orange]; B445->A538[color=orange]; A446->A515[color=orange]; C450->C537[color=orange]; A457->A526[color=orange]; A458->C569[color=orange]; A482->C548[color=orange]; A495->C561[color=orange]; C496->B578[color=orange]; C496->B579[color=orange]; C497->C584[color=orange]; A510->C576[color=orange]; A515->C581[color=orange]; C525->B594[color=orange]; A526->C592[color=orange]; C537->iv12[color=orange]; A538->C604[color=orange]; C542->iv17[color=orange]; C548->iv23[color=orange]; C561->iv21[color=orange]; C569->iv44[color=orange]; C576->iv36[color=orange]; B578->iv47[color=orange]; B579->x36[color=orange]; C581->iv56[color=orange]; C584->iv59[color=orange]; C592->iv52[color=orange]; B594->iv63[color=orange]; C604->iv64[color=orange]; iv12->sink[color=orange]; iv17->sink[color=orange]; iv21->sink[color=orange]; iv23->sink[color=orange]; iv36->sink[color=orange]; x36->sink[color=orange]; iv44->sink[color=orange]; iv47->sink[color=orange]; iv52->sink[color=orange]; iv56->sink[color=orange]; iv59->sink[color=orange]; iv63->sink[color=orange]; iv64->sink[color=orange];
