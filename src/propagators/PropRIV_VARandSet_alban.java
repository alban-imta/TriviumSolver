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
import org.chocosolver.solver.variables.SetVar;
import org.chocosolver.solver.variables.Variable;
import org.chocosolver.util.ESat;
import org.chocosolver.util.objects.setDataStructures.ISet;
import org.chocosolver.util.tools.ArrayUtils;
import utils.utilitaire;

/**
 * <br/>
 *
 * @author Alban DERRIEN
 * @since 01/03/2022
 */
public class PropRIV_VARandSet_alban extends Propagator<Variable> {

    private final DirectedGraphVar graph;
    private final TriviumAlban trivium;

    public final IntVar[] RIV;
    final SetVar nodesCanReach[];
    public final int NBTOREACH;


    public PropRIV_VARandSet_alban(TriviumAlban triviumData) {
        super(ArrayUtils.append(new Variable[]{triviumData.graph},triviumData.RIV), PropagatorPriority.CUBIC, true);
        this.graph = triviumData.graph;
        this.trivium = triviumData;
        this.RIV = triviumData.RIV;
        this.NBTOREACH = triviumData.graph.getMandatoryPredecessorsOf(triviumData.idxSink).size();
        this.nodesCanReach = triviumData.RIVset;
    }




    private void filter() throws ContradictionException {
        //System.out.println("RIV IN");
        //utilitaire.graphVizExport(trivium);
        computeRivUB();
        //System.out.println("RIV MID");
        computeRivLB();//some LB filtering is based on UB : should be computed after UB.
        //computeRivUB();

        //utilitaire.graphVizExport(trivium,this);
        //System.out.println("RIV OUT");
        //utilitaire.graphVizExport(trivium,this);
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
        if(newub<RIV[node].getLB()){
            //System.out.println("RIV removing node:"+node);
            graph.removeNode(node,this);//filtering 3/3
            //System.out.println("done..");
        }else{
            //System.out.println("updating UB:"+node);
            RIV[node].updateUpperBound(newub,this);
            //System.out.println("done..");
        }
    }
    public void removeItemFromNode(int node, int v) throws ContradictionException{
        if (nodesCanReach[node].getLB().contains(v)) {
            //if you cannot join a node, but is mandatory : this node is node a valid one.
            //System.out.print("removing "+utilitaire.getNodeName(v)+"\tfrom "+nodesCanReach[node].getName()+"...");
            graph.removeNode(node, this);
            //System.out.println("..done");
        } else {
            //System.out.print("removing "+utilitaire.getNodeName(v)+"\tfrom "+nodesCanReach[node].getName()+"...");
            nodesCanReach[node].remove(v, this);
            //System.out.println("..done");
        }
    }
    public void enforceItemFromNode(int node, int v) throws ContradictionException{

        //System.out.print("enforcing "+utilitaire.getNodeName(v)+"\tfrom "+nodesCanReach[node].getName()+"...");
        nodesCanReach[node].force(v, this);
        //System.out.println("..done");

    }

    private boolean checkNodeValidity(int node)throws ContradictionException {
        if(trivium.isNodeSink(node) || trivium.isNodeSource(node)) return true;//no check for those.
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
        //starting from the source, we are computing each value down to the sink.
        for (int node : utilitaire.roundCroissant(trivium.graph.getPotentialNodes())) {
            if (trivium.isNodeSink(node)) continue;//constant
            if (trivium.isNodeSource(node)) continue;//constant
            //if (graph.getPotentialPredecessorOf(trivium.idxSink).contains(node)) continue;//constant
            //if (!checkNodeValidity(node)) continue;
            computeRearchableFromPreds(node);
            computeRIVLB(node);
        }
    }
    private void computeRIVLB(int node) throws ContradictionException {

        int newLB;
        int minPredLB=NBTOREACH;
        for (int p : graph.getPotentialPredecessorOf(node)) {
            if (trivium.isArcDoubling(p, node)) {
                int doubling2 = trivium.getOtherDoubling(p, node);
                if(!graph.getPotentialNodes().contains(doubling2)) {
                    //System.out.println("RIV removing arc1:"+p +" :"+node);
                    graph.removeEdge(p,node,this);//filtering 1/3
                    //System.out.println("done..");
                    continue;
                }
                newLB = RIV[p].getLB() - RIV[doubling2].getUB();
            } else {
                newLB = RIV[p].getLB();
            }

            if(newLB>RIV[node].getUB()){
                // System.out.println("RIV removing arc2:"+p +" :"+node);
                graph.removeEdge(p,node,this);//filtering 2/3
                //System.out.println("done..");
            }
            minPredLB = Math.min(minPredLB,newLB );
        }

        //link with set :
        minPredLB = Math.max(minPredLB,nodesCanReach[node].getLB().size());

        updateLB(node, minPredLB);
    }
    private void computeRearchableFromPreds(int node) throws ContradictionException {
        for (int v : nodesCanReach[node].getUB()) {
            //for UB, you only need that on pred may got it.
            if (!oneSupportFromUB(graph.getPotentialPredecessorOf(node), v)) {
                removeItemFromNode(node, v);
            }
            if (anyMandPredAskIt(node, v) || allPotPredAskIt(node, v)) {
                enforceItemFromNode(node, v);
            }
        }
    }

    private void computeRivUB() throws ContradictionException {
        //starting from the IV nodes, we are computing each value up to the source.
        for (int node : utilitaire.roundDecroissant(trivium.graph.getPotentialNodes())) {
            if (trivium.isNodeSink(node)) continue;
            //removed coz now sink got them all !
            //if (graph.getPotentialPredecessorOf(trivium.idxSink).contains(node)) continue;
            computeRearchableFromSuccs(node);
            computeRIVUB(node);
        }
    }
    private void computeRIVUB(int node)throws ContradictionException  {
        int maxUB=0;
        int newUB;
        //basic version is max of successors
        ISet potSucc = trivium.graph.getPotentialSuccessorsOf(node);
        for (int succ : potSucc) {
            newUB = RIV[succ].getUB();

            if(!trivium.isArcDoubling(node, succ) && newUB<RIV[node].getLB()){
                //System.out.println("RIV removing arc2:"+succ +" :"+node+" mand?:"+trivium.graph.getMandatorySuccessorsOf(node).contains(succ));
                graph.removeEdge(node,succ,this);//filtering 2/3
                //System.out.println("done...");
            }
            maxUB = Math.max(maxUB, newUB);
        }//may test for not doubling, is it faster ?
        //but for doubling, it is the sum of both !

        int idxd1 = trivium.shift.double1SuccIndex(node);
        int idxd2 = trivium.shift.double2SuccIndex(node);


        //Fast computation (from arthur) : sum of both doubling succ.
        //if(potSucc.contains(idxd1) && potSucc.contains(idxd2) ){
        //    RivUB[node] = Math.max(RivUB[node], RivUB[idxd1]+RivUB[idxd2]);
        //}
        //return;


        boolean smartComputation = !(potSucc.contains(idxd1) && potSucc.contains(idxd2) && trivium.getRound(idxd1)>trivium.nbInnerRound);
        if(!smartComputation){//no smart computation if we are at the last nodes.
            if(potSucc.contains(idxd1) && potSucc.contains(idxd2)){
                maxUB = Math.max(maxUB, RIV[idxd1].getUB()+RIV[idxd2].getUB());
            }
        }else //smart computation (from arthur) : computing one step after for doubling//because some idx are the same and thus count twice !
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

        updateUB(node,maxUB);
    }
    private void computeRearchableFromSuccs(int node) throws ContradictionException {
        int supportLB;
        ISet succs = graph.getPotentialSuccessorsOf(node);
        if(succs.size() == 0) return; //we can do better, but not our place here.
        for (int v : nodesCanReach[node].getUB()) {
            if (!oneSupportFromUB(succs,v)) {
                removeItemFromNode(node, v);
            }
            supportLB = 0;
            for (int succ : succs) {
                if (nodesCanReach[succ].getLB().contains(v)) {
                    supportLB++;
                } else if (trivium.isArcDoubling(node, succ)) {//if this succ does not ask for it, but the otherdouble is, it is still ok.
                    int other = trivium.getOtherDoubling(node, succ);
                    if (other == -1) continue;
                    if (succs.contains(other) && nodesCanReach[other].getLB().contains(v)) {
                        supportLB++;
                    }
                }
            }
            if (supportLB == succs.size()) {
                enforceItemFromNode(node, v);
            }
        }
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
        if (other == -1) return true;
        if (nodesCanReach[other] == null) return true;
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

    public int getRIVLB(int node){
        return RIV[node].getLB();
    }
    public int getRIVUB(int node){
        return RIV[node].getUB();
    }

    /*
    @Override
    public int getPropagationConditions(int vIdx) {
        return GraphEventType.REMOVE_EDGE.getMask() + GraphEventType.ADD_NODE.getMask();
    }
*/
    @Override
    public void propagate(int idxVarInProp, int mask) throws ContradictionException {
        //System.out.println("new Call");
        filter();
        //System.out.println("out Call");

        //propagate(mask);
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        filter();
        filter();
        filter(); //how many is enough ? maybe 3 ! 4 to be sure.
        filter();


        int size=0;
        for(int i=0;i<trivium.RIV.length;i++){
            if(!trivium.graph.getPotentialNodes().contains(i)) continue;
            size = Math.max(size,trivium.RIV[i].getDomainSize());
            //System.out.println("trivium.RIV["+i+"]="+trivium.RIV[i]);
        }
        System.out.println("current max size="+size);

        //System.out.println("#####################OUT FIRST PROPAG#####################");
    }

    @Override
    public ESat isEntailed() {
        return ESat.UNDEFINED;
    }
}
