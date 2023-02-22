package utils;

/*
 * Copyright (c) 1999-2014, Ecole des Mines de Nantes
 * All rights reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the Ecole des Mines de Nantes nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE REGENTS AND CONTRIBUTORS BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Created by IntelliJ IDEA.
 * User: Jean-Guillaume Fages
 * Date: 08/08/12
 * Time: 15:27
 */


import main.TriviumAlban;
import org.chocosolver.solver.search.strategy.decision.GraphDecision;
import org.chocosolver.solver.search.strategy.strategy.GraphStrategy;
import org.chocosolver.solver.variables.DirectedGraphVar;
import org.chocosolver.solver.variables.GraphVar;

public class MyGraphSearch extends GraphStrategy {


    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************


    // variables
    //private final GraphDecisionOperator decisionType;
    private int from, to;
    private final TriviumAlban triv;
    private final DirectedGraphVar g;

    /**
     * Search strategy for graphs
     *
     * @param graphVar   varriable to branch on
     */
    /*public MyGraphSearch(DirectedGraphVar graphVar) {
        this(graphVar,100000);//to not use the modulo.
    }*/
    public MyGraphSearch(DirectedGraphVar graphVar, TriviumAlban triv) {
        super(new GraphVar[]{graphVar}, null, null, null,null,true);
        //decisionType = new DecisionOperatorFactory.GraphEnforceDecision();
        this.g = triv.graph;
        this.triv = triv;
    }


    @Override
    public GraphDecision getDecision() {
        if (g == null) {
            return null;
        }
        if (g.isInstantiated()) {
            return null;
        }
        //System.out.print("computing decision ...");

        int size=0;
        for(int i=0;i<triv.RIV.length;i++){
            if(!triv.graph.getPotentialNodes().contains(i)) continue;
            size = Math.max(size,triv.RIV[i].getDomainSize());
        }
        //System.out.println("current max size="+size);


        computeNext();
        //System.out.println("...from="+from+" to="+to);
        //TriviumAlban.printJavaCodeOfGraphVar((DirectedGraphVar) g);
        if (from==-1) return null;
        return g.getModel().getSolver().getDecisionPath().makeGraphEdgeDecision(g, operator, from, to);
    }

    private void computeNext() {
        from = -1;
        for(int node : utilitaire.roundCroissant(g.getMandatoryNodes())){
            if(g.getMandatorySuccessorsOf(node).size()==0){//pas de mandatory, mais des potentiels.
                for(int succ:g.getPotentialSuccessorsOf(node)){
                    if(!triv.isArcDoubling(node,succ)){
                        from = node;
                        to = succ;
                        return;
                    }
                }
            }
        }//si on va la, on a pas trouvé de double.
        for(int node : utilitaire.roundCroissant(g.getMandatoryNodes())){
            if(g.getMandatorySuccessorsOf(node).size()==0 &&
                    g.getPotentialSuccessorsOf(node).size()>0){//pas de mandatory, mais des potentiels.
                from = node;
                to = g.getPotentialSuccessorsOf(node).min();
                return;
            }
        }
        //throw new UnsupportedOperationException("No potential Successor found.");
    }

}
