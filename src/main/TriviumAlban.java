package main;


import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.DirectedGraphVar;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.SetVar;
import org.chocosolver.util.objects.graphs.DirectedGraph;
import org.chocosolver.util.objects.setDataStructures.SetType;
import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.CmdLineParser;
import org.kohsuke.args4j.Option;
import propagators.*;
import utils.MyGraphSearch;
import utils.Shift;
import utils.utilitaire;

import java.time.LocalTime;
import java.util.*;


public class TriviumAlban {



    @Option(name = "-i",
            aliases = {"--instance"},
            usage = "Instance à charger (default: iv_672_2). not used atm : forced to default from code.",
            required = true)
    public utils.Instances instance;

    public int nbRound;
    public int lastBit;
    public int nbInnerRound;
    public static int nbMaxNodePerRegistre;
    public int[] registreA,registreB,registreC;
    public final int idxSource,idxSink;
    public final Shift shift;
    public Model m;

    public SetVar[] RIVset;
    public IntVar[] RIV;

    public DirectedGraphVar graph;

    public boolean  startPrinting = false;

    public static void main(String[] args) throws CmdLineException {
        //iv672_2
        args = "-i iv672_2".split(" ");

        // option : GRAPHFROMEXPORTARC or  GRAPHFROMMODEL
        //from model means from the complete graph (creating all 5 nodes for every previously constructed node.)
        //from export arc  means the graph is constructed from a previously build graph (can be used to start from a wanted point in search, if used after an solution's export)
        TriviumAlban ta = new TriviumAlban(GRAPHFROMMODEL,args);// GRAPHFROMEXPORTARC GRAPHFROMMODEL

        ta.solveTrivium();
        //System.out.println(nbArc);
        //printListOfArc();
    }


    public TriviumAlban(int gcmIndex,String... args) throws CmdLineException {
        CmdLineParser cmdparser = new CmdLineParser(this);
        try {
            cmdparser.parseArgument(args);
        } catch (CmdLineException e) {
            System.err.println(e.getMessage());
            System.err.println("TriviumWithGraph -r <round> -i <instance> -b <bit>");
            cmdparser.printUsage(System.err);
            throw e;
        }
        this.lastBit=instance.positionOutputBit;
        this.nbRound=instance.nbRound;
        this.nbMaxNodePerRegistre = 1000;//1k pour lecture facile. can be set to smthg like nbRound+offSet for complete automatic;
        this.nbInnerRound = nbRound-lastBit;
        this.idxSource = instance.registerOutputBit*nbMaxNodePerRegistre;
        this.idxSink   = 3*nbMaxNodePerRegistre;
        this.shift = new Shift(this);
        this.m = new Model();

        if(gcmIndex == GRAPHFROMMODEL) createGraphFromModel();
        if(gcmIndex == GRAPHFROMEXPORTARC) createGraphFromArcList();
        utilitaire.setTriviumVar(this);
    }
    /*
     * functions to build graphs
     * */

    /**
     *
    builds graph from scratch builds all 5 succs from node round 0 up to nbRound.
     */
    public void createGraphFromModel(){
        SetType dftSetType = SetType.RANGESET;
        DirectedGraph glb = new DirectedGraph(m,3*nbMaxNodePerRegistre+1, dftSetType,false);
        DirectedGraph gub = new DirectedGraph(m,3*nbMaxNodePerRegistre+1, dftSetType,false);


        this.registreA = new int[nbMaxNodePerRegistre];
        this.registreB = new int[nbMaxNodePerRegistre];
        this.registreC = new int[nbMaxNodePerRegistre];


        if(instance.registerOutputBit == 0) registreA[0]=1;
        else if(instance.registerOutputBit == 1) registreB[0]=1;
        else if(instance.registerOutputBit == 2) registreC[0]=1;
        else System.err.println("activateAllNodesExceptSome : wrong registerOutputBit");
        for(int i=0;i<nbRound;i++){
            if (registreA[i]>0) {
                registreA[i+Shift.A_self] ++;
                registreC[i+Shift.A_short] ++;
                registreC[i+Shift.A_long]++;
                registreC[i+Shift.A_double1]++;
                registreC[i+Shift.A_double2]++;
            }
            if (registreB[i]>0) {
                registreB[i+Shift.B_self] ++;
                registreA[i+Shift.B_short] ++;
                registreA[i+Shift.B_long] ++;
                registreA[i+Shift.B_double1] ++;
                registreA[i+Shift.B_double2] ++;
            }
            if (registreC[i]>0) {
                registreC[i+Shift.C_self] ++;
                registreB[i+Shift.C_short] ++;
                registreB[i+Shift.C_long] ++;
                registreB[i+Shift.C_double1] ++;
                registreB[i+Shift.C_double2] ++;
            }
        }

        //create a graph with n first node register A (0 to nbMaxNodePerRegistre-1),
        // then register b (nbMaxNodePerRegistre to 2nbMaxNodePerRegistre-1)
        // then register C (2nbMaxNodePerRegistre to 3nbMaxNodePerRegistre-1)
        for(int i=0;i<=nbInnerRound;i++){
            if(registreA[i]>0) {
                gub.addEdge(i,i+Shift.A_self);
                gub.addEdge(i,i+2*nbMaxNodePerRegistre+Shift.A_short);
                gub.addEdge(i,i+2*nbMaxNodePerRegistre+Shift.A_long);
                gub.addEdge(i,i+2*nbMaxNodePerRegistre+Shift.A_double1);
                gub.addEdge(i,i+2*nbMaxNodePerRegistre+Shift.A_double2);
            }
            if(registreB[i]>0) {
                gub.addEdge(i+nbMaxNodePerRegistre,i+nbMaxNodePerRegistre+Shift.B_self);
                gub.addEdge(i+nbMaxNodePerRegistre,i+Shift.B_short);
                gub.addEdge(i+nbMaxNodePerRegistre,i+Shift.B_long);
                gub.addEdge(i+nbMaxNodePerRegistre,i+Shift.B_double1);
                gub.addEdge(i+nbMaxNodePerRegistre,i+Shift.B_double2);
            }
            if(registreC[i]>0) {
                gub.addEdge(i+2*nbMaxNodePerRegistre,i+2*nbMaxNodePerRegistre+Shift.C_self);
                gub.addEdge(i+2*nbMaxNodePerRegistre,i+  nbMaxNodePerRegistre+Shift.C_short);
                gub.addEdge(i+2*nbMaxNodePerRegistre,i+  nbMaxNodePerRegistre+Shift.C_long);
                gub.addEdge(i+2*nbMaxNodePerRegistre,i+  nbMaxNodePerRegistre+Shift.C_double1);
                gub.addEdge(i+2*nbMaxNodePerRegistre,i+  nbMaxNodePerRegistre+Shift.C_double2);
            }
        }


        manageSourceAndSink(glb,gub);

        //enforceSolution(glb,gub);
        //manageZ(glb,gub);
        //limitSolution(glb,gub);
        graph = m.digraphVar("trivium", glb, gub);
    }

    /**
    *builds graph from a predetermined list of arcs.
    *the list can be build by printJavaCodeOfGraphVar().
     * */
    public void createGraphFromArcList(){
        SetType dftSetType = SetType.RANGESET;
        DirectedGraph glb = new DirectedGraph(m,3*nbMaxNodePerRegistre+1, dftSetType,false);
        DirectedGraph gub = new DirectedGraph(m,3*nbMaxNodePerRegistre+1, dftSetType,false);
        //for(int i=0;i<nbArc;i++){gub.addEdge(arcListFrom[i],arcListTo[i]);}

        gub.addEdge(1454,1532);	gub.addEdge(2593,1662);	gub.addEdge(467,2578);	gub.addEdge(2578,1647);	gub.addEdge(482,2593);	gub.addEdge(2000,1083);	gub.addEdge(2000,1082);	gub.addEdge(1620,3000);	gub.addEdge(2563,1647);	gub.addEdge(1686,3000);	gub.addEdge(2317,1399);	gub.addEdge(2317,1400);	gub.addEdge(484,2595);	gub.addEdge(253,2362);	gub.addEdge(253,2363);	gub.addEdge(2362,1446);	gub.addEdge(1392,485);	gub.addEdge(1633,3000);	gub.addEdge(2595,1664);	gub.addEdge(2454,2541);	gub.addEdge(1161,253);	gub.addEdge(1161,252);	gub.addEdge(443,2509);	gub.addEdge(527,2593);	gub.addEdge(2285,2372);	gub.addEdge(497,2563);	gub.addEdge(2362,2449);	gub.addEdge(2283,1365);	gub.addEdge(2283,1366);	gub.addEdge(2283,1367);	gub.addEdge(512,2578);	gub.addEdge(2362,1431);	gub.addEdge(1542,1620);	gub.addEdge(529,2595);	gub.addEdge(2285,1368);	gub.addEdge(2285,1369);	gub.addEdge(2285,1367);	gub.addEdge(2240,1323);	gub.addEdge(2240,1322);	gub.addEdge(432,2498);	gub.addEdge(2509,1578);	gub.addEdge(2372,1455);	gub.addEdge(2372,1454);	gub.addEdge(1369,460);	gub.addEdge(2585,1654);	gub.addEdge(1082,1160);	gub.addEdge(1369,461);	gub.addEdge(2449,2536);	gub.addEdge(413,482);	gub.addEdge(1399,491);	gub.addEdge(1399,490);	gub.addEdge(1508,1586);	gub.addEdge(173,2239);	gub.addEdge(460,529);	gub.addEdge(2570,1654);	gub.addEdge(173,2282);	gub.addEdge(173,2283);	gub.addEdge(2587,1656);	gub.addEdge(434,2500);	gub.addEdge(2370,1454);	gub.addEdge(1610,3000);	gub.addEdge(1625,3000);	gub.addEdge(2572,1656);	gub.addEdge(1401,467);	gub.addEdge(1431,497);	gub.addEdge(2602,1686);	gub.addEdge(2282,1351);	gub.addEdge(1446,512);	gub.addEdge(321,2431);	gub.addEdge(321,2430);	gub.addEdge(2604,1673);	gub.addEdge(175,2284);	gub.addEdge(175,2285);	gub.addEdge(2430,2517);	gub.addEdge(1365,458);	gub.addEdge(2458,1542);	gub.addEdge(490,2556);	gub.addEdge(460,2526);	gub.addEdge(419,2485);	gub.addEdge(252,2362);	gub.addEdge(252,2361);	gub.addEdge(1444,510);	gub.addEdge(1532,1610);	gub.addEdge(2576,1645);	gub.addEdge(1547,1625);	gub.addEdge(1082,173);	gub.addEdge(458,527);	gub.addEdge(1367,458);	gub.addEdge(1367,459);	gub.addEdge(415,484);	gub.addEdge(1082,174);	gub.addEdge(1367,460);	gub.addEdge(1322,388);	gub.addEdge(415,2526);	gub.addEdge(1322,413);	gub.addEdge(1322,414);	gub.addEdge(2517,1586);	gub.addEdge(1391,482);	gub.addEdge(1391,483);	gub.addEdge(1453,519);	gub.addEdge(2485,1569);	gub.addEdge(485,2551);	gub.addEdge(1500,1578);	gub.addEdge(243,2309);	gub.addEdge(2500,1569);	gub.addEdge(1440,506);	gub.addEdge(1365,1443);	gub.addEdge(2500,2587);	gub.addEdge(1455,521);	gub.addEdge(2485,2572);	gub.addEdge(252,321);	gub.addEdge(389,2500);	gub.addEdge(442,2508);	gub.addEdge(2549,1633);	gub.addEdge(2363,1445);	gub.addEdge(2363,1446);	gub.addEdge(2551,1620);	gub.addEdge(2498,1567);	gub.addEdge(2284,1368);	gub.addEdge(2498,2585);	gub.addEdge(1664,3000);	gub.addEdge(2361,2448);	gub.addEdge(2284,1366);	gub.addEdge(2284,1367);	gub.addEdge(2239,1321);	gub.addEdge(2361,1430);	gub.addEdge(2239,1322);	gub.addEdge(412,2478);	gub.addEdge(1586,1664);	gub.addEdge(1647,3000);	gub.addEdge(2284,1353);	gub.addEdge(2536,1620);	gub.addEdge(2361,1443);	gub.addEdge(2361,1444);	gub.addEdge(2284,2371);	gub.addEdge(1662,3000);	gub.addEdge(483,2549);	gub.addEdge(1645,3000);	gub.addEdge(1323,415);	gub.addEdge(1323,414);	gub.addEdge(2448,1532);	gub.addEdge(491,2602);	gub.addEdge(1569,1647);	gub.addEdge(2478,1547);	gub.addEdge(1443,536);	gub.addEdge(2541,1610);	gub.addEdge(1323,416);	gub.addEdge(461,2572);	gub.addEdge(251,2317);	gub.addEdge(1368,459);	gub.addEdge(1368,460);	gub.addEdge(1083,1161);	gub.addEdge(1368,461);	gub.addEdge(2508,2595);	gub.addEdge(1430,1508);	gub.addEdge(538,2604);	gub.addEdge(2556,1625);	gub.addEdge(2309,1392);	gub.addEdge(2371,2458);	gub.addEdge(2541,1625);	gub.addEdge(2526,1610);	gub.addEdge(2283,2370);	gub.addEdge(1567,1645);	gub.addEdge(2371,1453);	gub.addEdge(2371,1455);	gub.addEdge(1445,538);	gub.addEdge(493,2604);	gub.addEdge(1673,3000);	gub.addEdge(2371,1454);	gub.addEdge(1400,493);	gub.addEdge(2371,1440);	gub.addEdge(174,2240);	gub.addEdge(510,2576);	gub.addEdge(2431,1500);	gub.addEdge(1366,432);	gub.addEdge(1656,3000);	gub.addEdge(519,2585);	gub.addEdge(174,243);	gub.addEdge(1160,251);	gub.addEdge(1160,252);	gub.addEdge(1321,1399);	gub.addEdge(174,2283);	gub.addEdge(1366,1444);	gub.addEdge(174,2284);	gub.addEdge(416,485);	gub.addEdge(2309,1391);	gub.addEdge(1323,1401);	gub.addEdge(506,2572);	gub.addEdge(1368,434);	gub.addEdge(521,2587);	gub.addEdge(1654,3000);	gub.addEdge(1321,413);	gub.addEdge(1351,442);	gub.addEdge(1321,412);	gub.addEdge(1351,443);	gub.addEdge(1578,1656);	gub.addEdge(1353,1431);	gub.addEdge(388,2454);	gub.addEdge(1368,1446);	gub.addEdge(1083,175);	gub.addEdge(536,2602);	gub.addEdge(1083,174);	gub.addEdge(1366,459);	gub.addEdge(459,2570);	gub.addEdge(414,483);	gub.addEdge(1323,389);	gub.addEdge(1353,419);


        //instance 3-1 avec papillon.
        //gub.addEdge(1454,1532);	gub.addEdge(2593,1662);	gub.addEdge(467,2578);	gub.addEdge(2578,1647);	gub.addEdge(482,2593);	gub.addEdge(1453,519);	gub.addEdge(2000,1083);	gub.addEdge(2000,1082);	gub.addEdge(603,672);	gub.addEdge(2585,1654);	gub.addEdge(413,482);	gub.addEdge(1082,1160);	gub.addEdge(2449,2536);	gub.addEdge(1399,491);	gub.addEdge(1399,490);	gub.addEdge(1620,3000);	gub.addEdge(491,2602);	gub.addEdge(1569,1647);	gub.addEdge(460,529);	gub.addEdge(1686,3000);	gub.addEdge(461,2572);	gub.addEdge(1443,534);	gub.addEdge(251,2317);	gub.addEdge(1443,535);	gub.addEdge(2500,1569);	gub.addEdge(535,604);	gub.addEdge(1368,461);	gub.addEdge(2556,1625);	gub.addEdge(2587,1656);	gub.addEdge(2317,1399);	gub.addEdge(434,2500);	gub.addEdge(2500,2587);	gub.addEdge(2317,1400);	gub.addEdge(1610,3000);	gub.addEdge(673,3000);	gub.addEdge(389,2500);	gub.addEdge(1625,3000);	gub.addEdge(2572,1656);	gub.addEdge(1633,3000);	gub.addEdge(2371,1453);	gub.addEdge(2549,1633);	gub.addEdge(1401,467);	gub.addEdge(493,2604);	gub.addEdge(1673,3000);	gub.addEdge(2371,1454);	gub.addEdge(1400,493);	gub.addEdge(174,2240);	gub.addEdge(2595,1664);	gub.addEdge(2602,1686);	gub.addEdge(510,2576);	gub.addEdge(604,673);	gub.addEdge(1656,3000);	gub.addEdge(2604,1673);	gub.addEdge(1664,3000);	gub.addEdge(175,2284);	gub.addEdge(519,2585);	gub.addEdge(175,2285);	gub.addEdge(1160,251);	gub.addEdge(1160,252);	gub.addEdge(1647,3000);	gub.addEdge(490,2556);	gub.addEdge(2536,1620);	gub.addEdge(2362,2449);	gub.addEdge(2361,1443);	gub.addEdge(252,2362);	gub.addEdge(2361,1444);	gub.addEdge(672,3000);	gub.addEdge(252,2361);	gub.addEdge(2284,2371);	gub.addEdge(1323,1401);	gub.addEdge(1444,510);	gub.addEdge(1368,434);	gub.addEdge(529,2595);	gub.addEdge(1532,1610);	gub.addEdge(1654,3000);	gub.addEdge(2576,1645);	gub.addEdge(1662,3000);	gub.addEdge(534,603);	gub.addEdge(483,2549);	gub.addEdge(1367,460);	gub.addEdge(1645,3000);	gub.addEdge(1322,413);	gub.addEdge(2285,1368);	gub.addEdge(1322,414);	gub.addEdge(1083,175);	gub.addEdge(1083,174);	gub.addEdge(2285,1367);	gub.addEdge(414,483);	gub.addEdge(1323,389);	gub.addEdge(2240,1323);	gub.addEdge(2240,1322);



        manageSourceAndSink(glb,gub);//to add mandatory nodes.
        //manageZ(glb,gub);
        //limitSolution(glb,gub);
        //enforceSolution(glb,gub);
        graph = m.digraphVar("trivium", glb, gub);
    }
    public void manageSourceAndSink(DirectedGraph glb,DirectedGraph gub){
        glb.addNode(idxSource);
        gub.addNode(idxSource);
        glb.addNode(idxSink);
        gub.addNode(idxSink);

        for(int i=1;i<=80;i++){
            //from register A: nothing is mandatory, so it's added to GUB only.
            int j=i+nbInnerRound;
            for(int k:glb.getSuccessorsOf(j)) {//should do nothing.
                System.err.println("manageSourceAndSink(DirectedGraph glb,DirectedGraph gub) error1");
                glb.removeEdge(j,k);
                gub.removeEdge(j,k);
            }

            gub.addEdge(j,idxSink);
        }
        for( int i=0;i<instance.iv.length;i++){
            //from register B : only IV which must be in the solution
            int j=instance.iv[i]+nbInnerRound+nbMaxNodePerRegistre;
            for(int k:glb.getSuccessorsOf(j)) {
                System.err.println("manageSourceAndSink(DirectedGraph glb,DirectedGraph gub) error2");
                glb.removeEdge(j,k);
                gub.removeEdge(j,k);
            }
            glb.addEdge(j,idxSink);
            gub.addEdge(j,idxSink);
        }
        for(int i=0;i<=111;i++){
            int j =i+nbInnerRound+2*nbMaxNodePerRegistre;
            for(int k:glb.getSuccessorsOf(j)) {
                System.err.println("manageSourceAndSink(DirectedGraph glb,DirectedGraph gub) error3");
                glb.removeEdge(j,k);
                gub.removeEdge(j,k);
            }
        }
        for(int i:new int[]{109,110,111}){
            //from register C: only the last 3 can be in the solution
            if(i+nbInnerRound+2*nbMaxNodePerRegistre>idxSink)System.err.println("manageSourceAndSink error4");
            gub.addEdge(i+nbInnerRound+2*nbMaxNodePerRegistre,idxSink);
        }
    }



    /*
    Utility Functions
     */

    public boolean isNodeRegisterA(int nodes){
        return nodes<nbMaxNodePerRegistre;
    }
    public boolean isNodeRegisterB(int nodes){
        return nodes>=nbMaxNodePerRegistre && nodes<2*nbMaxNodePerRegistre;
    }
    public boolean isNodeRegisterC(int nodes){
        return nodes>=2*nbMaxNodePerRegistre && nodes<3*nbMaxNodePerRegistre;
    }
    public boolean isNodeSink(int nodes){
        return nodes==idxSink;
    }
    public boolean isNodeSource(int nodes){
        return nodes==idxSource;
    }
    public int arcRoundDistance(int from, int to){
        if(getRound(to)-getRound(from)<0) {
            System.out.println("BUGGGG arcRoundDistance from"+from+">"+to+"to");
        }
        if(isNodeSink(to)){
            System.out.println("BUGGGG arcRound what is the distance from sink ?");
        }
        return (3*nbMaxNodePerRegistre+to-from)%nbMaxNodePerRegistre;
    }
    public int getOtherDoubling(int from, int to){
        if(!isArcDoubling(from,to)) return -1;
        int d = arcRoundDistance(from, to);
        if(d==82 || d==91||d==109) return to+1;
        return to-1;
    }
    public boolean isArcDoubling(int from, int to){
        if(isNodeSink(to)) return false;
        int d = arcRoundDistance(from, to);
        if(d==82) return true;
        if(d==83) return true;
        if(d==91) return true;
        if(d==92) return true;
        if(d==109) return true;
        return d == 110;
    }
    public boolean isArcDouble1(int from, int to){
        if(isNodeSink(to)) return false;
        int d = arcRoundDistance(from, to);
        if(d==82) return true;
        if(d==91) return true;
        return d == 109;
    }
    public boolean isArcDouble2(int from, int to){
        if(isNodeSink(to)) return false;
        int d = arcRoundDistance(from, to);
        if(d==83) return true;
        if(d==92) return true;
        return d == 110;
    }
    public boolean isArcShort(int from, int to){
        if(isNodeSink(to)) return false;
        int d = arcRoundDistance(from, to);
        if(d==66) return true;
        return d == 69 && isNodeRegisterC(from);
    }
    public boolean isArcLong(int from, int to){
        if(isNodeSink(to)) return false;
        int d = arcRoundDistance(from, to);
        if(d==93) return true;
        if(d==111) return true;
        return d == 84;
    }
    public boolean isArcSelf(int from, int to){
        if(isNodeSink(to)) return false;
        int d = arcRoundDistance(from, to);
        if(d==78) return true;
        if(d==87) return true;
        return d == 69 && isNodeRegisterA(from);
    }
    public boolean isArcSink(int from, int to){
        return isNodeSink(to);
    }
    public boolean isArcValid(int from, int to){
        if (isArcSink(from, to)) return true;
        if(from%nbMaxNodePerRegistre >nbRound) return false;
        if(to%nbMaxNodePerRegistre >nbRound) return false;
        if (isArcSelf(from, to)) return true;
        if (isArcShort(from, to)) return true;
        if (isArcLong(from, to)) return true;
        if (isArcDoubling(from, to)) return true;
        return false;
    }

    public int[] getFivePred(int to){
        int[] res = new int[]{};
        if(isNodeSink(to)) return res;
        if(isNodeSource(to)) return res;
        int from = to+nbMaxNodePerRegistre;
        if(isNodeRegisterA(to))res =  new int[]{from-66,from-91,from-92,from-93,to-69};
        if(isNodeRegisterB(to))res =  new int[]{from-69,from-82,from-83,from-84,to-78};
        from = to-2*nbMaxNodePerRegistre;
        if(isNodeRegisterC(to))res =  new int[]{from-66,from-109,from-110,from-111,to-87};
        return keepOnlyValidPred(res);
    }
    public int[] getFiveSucc(int from){
        int[] res = new int[]{};
        if(isNodeSink(from)) return res;
        //if(isNodeSource(from)) return res;
        int to = from-nbMaxNodePerRegistre;
        if(isNodeRegisterB(from))res= new int[]{to+66,to+91,to+92,to+93,from+78};
        if(isNodeRegisterC(from))res= new int[]{to+69,to+82,to+83,to+84,from+87};
        to = from+2*nbMaxNodePerRegistre;
        if(isNodeRegisterA(from))res= new int[]{to+66,to+109,to+110,to+111,from+69};
        return keepOnlyValidPred(res);
    }
    public int[] getDoublingSucc(int from){
        int[] res = new int[]{};
        if(isNodeSink(from)) return res;
        if(isNodeSource(from)) return res;
        int to = from-nbMaxNodePerRegistre;
        if(isNodeRegisterB(from))res= new int[]{to+91,to+92};
        if(isNodeRegisterC(from))res= new int[]{to+82,to+83};
        to = from+2*nbMaxNodePerRegistre;
        if(isNodeRegisterA(from))res= new int[]{to+109,to+110};
        return keepOnlyValidPred(res);
    }
    public int[] getDoublingPred(int to){
        int[] res = new int[]{};
        if(isNodeSink(to)) return res;
        if(isNodeSource(to)) return res;
        int from = to+nbMaxNodePerRegistre;
        if(isNodeRegisterA(to))res =  new int[]{from-91,from-92};
        if(isNodeRegisterB(to))res =  new int[]{from-82,from-83};
        from = to-2*nbMaxNodePerRegistre;
        if(isNodeRegisterC(to))res =  new int[]{from-109,from-110};
        return keepOnlyValidPred(res);
    }
    public int[]keepOnlyValidPred(int[]neighbors){
        int nbV=0;
        for(int n:neighbors){
            if(isValidNumber(n)) nbV++;
        }
        int[] res =new int[nbV];
        int idxV = 0;
        for(int n:neighbors){
            if(isValidNumber(n)) res[idxV++]=n;
        }
        return res;
    }
    public boolean isValidNumber(int round){
        //288 but may be it can be better ?
        //like switch by register ?
        if(isNodeSink(round)) return true;
        if(isNodeSource(round)) return true;
        if(isNodeRegisterA(round))
            return (round+nbMaxNodePerRegistre)%nbMaxNodePerRegistre<nbRound+80;
        if(isNodeRegisterB(round))
            return (round+nbMaxNodePerRegistre)%nbMaxNodePerRegistre<nbRound+80;
        if(isNodeRegisterC(round))
            return (round+nbMaxNodePerRegistre)%nbMaxNodePerRegistre<nbRound+129;
        System.out.println("isValidNumber() : should never go there");
        return false;
    }
    public int[] getTenNeighboors(int node){
        int[] preds = getFivePred(node);
        int[] succs = getFiveSucc(node);
        int[]res = new int[preds.length+succs.length];
        System.arraycopy(preds, 0, res, 0, preds.length);
        System.arraycopy(succs, 0, res, 0 + preds.length, succs.length);
        return res;
    }



    public int getRound(int node){
        if(isNodeSource(node)) return 0;
        if(isNodeSink(node)) return nbRound+1;
        return node%nbMaxNodePerRegistre;
    }


    public int getNumberFromName(String name){
        if(name.equals("sink")) return idxSink;
        if(name.equals("source")) return idxSource;
        int r = name.charAt(0)-65;
        int i = Integer.parseInt(name.substring(1));
        return r*nbMaxNodePerRegistre+i;
    }


    /*
    Printing Functions
    */
    public static void printJavaCodeOfGraphVar(DirectedGraphVar g){
        StringBuilder sb = new StringBuilder();
        for(int from:utilitaire.roundCroissant(g.getPotentialNodes())){
            sb.append("gub.addNode(").append(from).append(");");
            if(g.getMandatoryNodes().contains(from)){
                sb.append("glb.addNode(").append(from).append(");");
            }
            for(int to:g.getPotentialSuccessorsOf(from)){
                sb.append("gub.addEdge(").append(from).append(",").append(to).append(");");
                if(g.getMandatorySuccessorsOf(to).contains(from)){
                    sb.append("glb.addEdge(").append(from).append(",").append(to).append(");");
                }
            }
        }
        System.out.println(sb);
    }
    public void printJavaCodeOfSolution(){
        StringBuilder sb = new StringBuilder();

        sb.append("this.lastBit=66;\n");
        sb.append("this.nbRound=672;\n");
        sb.append("this.nbInnerRound = nbRound-lastBit;\n");
        sb.append("this.idxSource = 2*nbMaxNodePerRegistre;//TODO change this to a variable.\n");
        sb.append("this.idxSink   = 3*nbMaxNodePerRegistre;\n");
        sb.append("this.nbMaxNodePerRegistre=1000;\n");
        sb.append("this.registreA = new int[]{");



        for(int i=0;i<nbMaxNodePerRegistre;i++){
            sb.append(registreA[i]).append(",");
        }
        sb.setLength(sb.length() - 1);
        sb.append("};\nthis.registreB = new int[]{");
        for(int i=0;i<nbMaxNodePerRegistre;i++){
            sb.append(registreB[i]).append(",");
        }
        sb.setLength(sb.length() - 1);
        sb.append("};\nthis.registreC = new int[]{");
        for(int i=0;i<nbMaxNodePerRegistre;i++){
            sb.append(registreC[i]).append(",");
        }
        sb.setLength(sb.length() - 1);
        sb.append("};\n");
        System.out.println(sb);
    }

    public static  HashSet<Integer>arcList= new HashSet<>();
    public static int nbArc=0;
    public void exportArcFromSolution(){
        for(int node:graph.getMandatoryNodes()){
            for(int succ:graph.getMandatorySuccessorsOf(node)){
                arcList.add(node*10*nbMaxNodePerRegistre+succ);
                nbArc++;
            }
        }
    }
    public void exportArcFromCurrentState(){
        for(int node:graph.getPotentialNodes()){
            if(graph.getMandatoryNodes().contains(node)){
                System.out.print("\tglb.addNode("+ node+");");
                System.out.print("\tgub.addNode("+ node+");");
            }else{
                System.out.print("\tgub.addNode("+ node+");");
            }
            for(int succ:graph.getPotentialSuccessorsOf(node)){
                if(graph.getMandatorySuccessorsOf(node).contains(succ)){
                    System.out.print("\tglb.addEdge("+ node+","+succ+");");
                    System.out.print("\tgub.addEdge("+ node+","+succ+");");
                }else{
                    System.out.print("\tgub.addEdge("+ node+","+succ+");");
                }
            }
        }
        System.out.println();
    }


    public static void printStats(HashMap<String, Integer> map){
        int[] sizeCount = new int[80];
        int[] sizeCountDistinct = new int[80];

        for(Map.Entry<String, Integer> entry : map.entrySet()){
            sizeCountDistinct[entry.getKey().split("x").length-1]++;
            sizeCount[entry.getKey().split("x").length-1]+=entry.getValue();
        }
        for(int i=0;i<sizeCount.length;i++){
            if(sizeCount[i]==0) continue;
            System.out.println(i+":\tdistinct #"+sizeCountDistinct[i]+"\tTotal #"+sizeCount[i]);
        }

    }
    public static void printListOfArc(){
        System.out.println("nbElem:"+arcList.size());
        System.out.println("nbAdded:"+nbArc);
        for(int a:arcList){
            System.out.print("\tgub.addEdge("+a/(10*nbMaxNodePerRegistre)+","+a%(10*nbMaxNodePerRegistre)+");");
        }
        System.out.println();
    }
    /*
    // exemple 675_4 a 3 path miroir !
    public void enforceSolution675_4(DirectedGraph glb,DirectedGraph gub){
        if(false) return;
        ArrayList<Integer> enforceCube = new ArrayList<>(List.of(31));
        if(!enforceCube.isEmpty())
            for(int i=1;i<=80;i++){
                //from register A: nothing is mandatory, so its added to GUB only.
                int j=i+nbInnerRound;
                if(enforceCube.contains(i)){
                    glb.addEdge(j,idxSink);
                }else{gub.removeNode(j);
                }
            }
        //add constant z109/110/111
        //gub.removeEdge(109+nbInnerRound+2*nbMaxNodePerRegistre,idxSink);
        //gub.removeEdge(110+nbInnerRound+2*nbMaxNodePerRegistre,idxSink);
        //gub.removeEdge(111+nbInnerRound+2*nbMaxNodePerRegistre,idxSink);
        //other way to remove nodes.//pas 26
        ArrayList<Integer> removeXi=new ArrayList<>();
        removeXi = new ArrayList<>(List.of());
        for(int i:removeXi){
            gub.removeNode(i+nbInnerRound);
        }
        ArrayList<Integer> remove = new ArrayList<>(List.of(1445,459,390,414,503,608
                ,2458
                //copy pasting:

                ,135,150,1156,160,161,162,1169,1170,1171,176,177,2201,204,213,2216,219,222,
                2226,226,2227,227,2228,228,229,230,231,1234,235,236,237,238,239,240,2242,2243,
                1243,2244,2245,245,2246,246,1247,247,1248,248,1249,249,251,252,253,254,255,1256,
                1257,1258,2259,2260,260,2261,261,262,263,264,2269,2270,1270,2271,2272,2273,273,
                2279,282,1283,1284,1285,2286,2287,2288,288,291,2292,2293,2294,2295,1295,295,2296,
                1296,296,2297,1297,297,1298,298,1299,299,1300,300,2301,2302,2303,2304,304,2305,305,
                2306,306,307,1308,308,309,2311,1311,2312,1312,2313,1313,313,2314,1314,314,2315,1315,
                315,316,2317,317,2318,318,2319,2320,320,2321,1321,321,2322,322,2323,323,2324,324,325,
                2326,326,327,1328,2329,1329,329,2330,1330,330,2331,331,2332,332,2333,333,1334,334,2335,
                1335,335,2336,1336,336,2337,2338,1338,338,2339,339,2340,340,2341,341,2342,342,1343,1344,
                1345,2346,2347,347,2348,1348,348,2349,349,2350,350,2351,1351,351,2355,1355,2356,1356,2357,
                1357,357,2358,2359,2360,360,2361,1361,361,2362,1362,362,2363,1363,363,2364,1364,364,2365,
                365,2366,366,367,368,2369,369,1370,1371,1372,2373,1373,373,2374,1374,374,2375,1375,1376,
                1377,377,378,2379,1379,379,2380,1380,380,2381,1381,2382,1382,382,2383,1383,383,2384,1384,
                384,1385,385,2386,1386,386,2387,387,2388,2389,1389,2390,1390,2391,2392,2393,1394,394,2395,
                1395,395,396,2397,2398,1398,398,2399,1399,399,2400,2401,2402,2404,404,2405,2406,1406,2407,
                1407,2408,1408,2409,409,2410,410,2411,411,412,2413,1415,2416,1416,2417,2418,2419,2420,421,
                422,423,2424,1424,2425,1425,425,2426,426,2427,427,2428,428,2429,429,2430,2433,1433,2434,2435,
                2436,436,2437,437,2438,438,439,440,441,1442,442,2443,2444,2445,2446,2448,1448,448,2449,1449,
                449,2450,1450,2451,1451,451,2452,452,2453,455,2456,1457,1458,1459,2460,2461,2462,1463,2464,
                1464,464,465,1467,1468,2470,1472,1473,473,2475,2476,1476,2477,1477,2478,2480,1485,1486,2488,
                2489,2493,1493,2494,1494,2495,1502,2505,2506,2507,1520,2521,1527,542,1545,1546,1309,1322,1354,
                1368,1369,375,1378,1387,388,1391,1392,1393,393,1396,1400,400,405,408,1409,1413,1414,420,1421,
                1422,1423,1426,1427,1428,1429,430,1432,1434,1435,435,1436,1437,1438,1439,1440,2441,1441,1446,
                446,1447,447,1452,1453,453,2454,1454,1455,1456,456,2459,1460,1461,1462,462,1465,466,1469,1470,
                1471,2474,1474,474,1478,482,483,1491,2496,498,499,1500,1505,506,1507,507,508,1509,1514,515,1516,
                516,517,518,519,1521,521,528,529,1534,2539,1543,1547,376,391,1397,401,402,403,1410,1411,2442,445,
                454,2457,463,2467,2468,
                468,469,471,472,
                //476,
                477,2487,495,2501,504,2511,1511,2520,532,538,540,1541,1556,2561,2565,2583,1585,1589,607,609,2718,2719,
                2720,470,497,2563,2581,1599,2608,1578,
                //467,2578
                //1647
                1365,1443,1501,1513,1515,534,1535,1540
                ,541,1553,553,566,567,568,586
                ,1588,2600,602,1604,1412,478,480,481,1496
                ,1497,505,2546,1574,1575
                ,2518
                //,407
                //,389//ok de les suppr : mirroir.
                //this is the real solution
                ,1419
                ,1551,587
        ));//
        remove.add(460);
        for(int i:remove){
            gub.removeNode(i);
        }
        gub.removeEdge(1341,432);
        gub.removeEdge(1341,433);
        gub.removeEdge(389,458);
        gub.removeEdge(416,2482);
        gub.removeEdge(1323,416);
        gub.removeEdge(1419,485);


        ArrayList<Integer> add = new ArrayList<Integer>(List.of(1083,174,2284,1367,458,527,2593,1366,2283,1352,444,513,2579,443,2554,
                175,2241,1324,415,484,2550,416,485,2596,1323,1082,148,2258,2257,1326,418,487,2598,417,2483,1552,432,2543
                ,1341,1340,432,431//,389
        ));
        //add.add(1368);
        for(int i:add){
            glb.addNode(i);
        }



        //glb.addNode(getNumberFromName("B82"));

    }

     */




    public void postConstraints(){
        //post 2 flow for fixed point.
        new Constraint("TriviumFlow1", new PropTriviumFlow(this)).post();
        new Constraint("TriviumFlow2", new PropTriviumFlow(this)).post();
        InitRIV();
        InitRIVSets();

        System.out.println("VAR only version :");
        new Constraint("RIVVAR", new PropRIV_VAR_alban(this)).post();
        //System.out.println("Var and SET version :");
        //new Constraint("RIVVAR", new PropRIV_VARandSet_alban(this)).post();
    }

    private void InitRIVSets(){
        RIVset = new SetVar[graph.getNbMaxNodes()];
        RIVset[0] = m.setVar("Getter org.chocosolver.solver.constraints.Propagator.<init>(Propagator.java:298)", -1);

        int[] lb = new int[]{};
        int[] ub = graph.getMandatoryPredecessorsOf(idxSink).toArray();
        for(int n:graph.getPotentialNodes()){
            String name = utilitaire.getNodeName(n);
            if(isNodeSink(n)) {
                RIVset[n] = m.setVar("ReachableSet1_"+name,ub);
            }else if(isNodeSource(n)){
                RIVset[n] = m.setVar("ReachableSet2_"+name,ub);
            }else if(graph.getPotentialPredecessorOf(idxSink).contains(n)){
                if(graph.getMandatoryPredecessorsOf(idxSink).contains(n)){
                    RIVset[n] = m.setVar("ReachableSet3_"+name,n);
                }else{
                    RIVset[n] = m.setVar("ReachableSet4_"+name,lb);
                }
            }else {
                //standard case :
                RIVset[n] = m.setVar("ReachableSet5_" + name, lb, ub);
            }
        }
    }
    private void InitRIV(){
        int NBTOREACH = graph.getMandatoryPredecessorsOf(idxSink).size();
        RIV = new IntVar[graph.getNbMaxNodes()];

        for(int n:graph.getPotentialNodes()){
            if(isNodeSink(n)) {
                RIV[n] = m.intVar("RIVsink",NBTOREACH);
            }else if(isNodeSource(n)){
                RIV[n] = m.intVar("RIVsource", NBTOREACH);
            }else if(graph.getPotentialPredecessorOf(idxSink).contains(n)) {
                if(graph.getMandatoryPredecessorsOf(idxSink).contains(n)) {
                    RIV[n] = m.intVar("RIV_IV" + n, 1);
                }else{
                    RIV[n] = m.intVar("RIV_nonIV" + n, 0);
                }
            }else {//regular case:
                RIV[n] = m.intVar("RIV_node" + n, 0, NBTOREACH);
            }
        }
        for(int i=0;i<RIV.length;i++){
            if(RIV[i] == null)
                RIV[i] = m.intVar("RIV_null_" + i, -1111);
        }
    }


    public static int GRAPHFROMMODEL=0;
    public static int GRAPHFROMEXPORTARC=1;

    public  void solveTrivium(){
        postConstraints();

        Solver solver = m.getSolver();
        solver.setSearch(new MyGraphSearch(graph,this));

        //solver.showDecisions(()->"");
        //solver.showSolutions(()->"");
        //solver.showContradiction();
        //solver.limitSearch(() -> solver.getMeasures().getNodeCount()>=217);
        try {
            solver.propagate();
            //utilitaire.graphVizExport(this); //to export the graph after the first (root) propagation
            startPrinting = false;
            //utilitaire.graphVizPrint(this);
            //utilitaire.graphVizExport(this);



            //graph.removeNode(460, new ICause(){});
            //solver.propagate();
            //utilitaire.graphVizExport(this);

            //printJavaCodeOfGraphVar(graph);
            //printJavaCodeOfSolutionFromGraphVar();

            //System.out.println(utilitaire.graphVizExport(this));

            //solveAndPrintSol(solver);
            //solver.printShortStatistics();


            //solver.solve();
            FindSuperPoly(solver);
            //solveAndPrintSolutions(solver);
            solver.printShortStatistics();
        } catch (ContradictionException e) {
            e.printStackTrace();
        }
    }

    public void solveAndPrintSolutions(Solver solver){
        while(solveAndPrintSolution(solver));
    }
    public boolean solveAndPrintSolution(Solver solver){
        if(solver.solve()){//if a solution has been found
            List<Integer> ivs = Arrays.stream(instance.iv).boxed().toList();
            String foundNothing = "one";
            for (int node : graph.getMandatoryPredecessorsOf(idxSink)) {
                if (!ivs.contains(node - nbInnerRound - nbMaxNodePerRegistre)) {
                    System.out.print(utilitaire.getNodeName(node) + " ");
                    foundNothing = "";
                }
            }
            System.out.println(foundNothing);
            //System.out.println("found solution"+(i++));
            //utilitaire.graphVizExport(this);
            //printJavaCodeOfGraphVar(graph);
            return true;
        }
        return false;
    }

    /**
     * Search for all solution, and print the superpoly at the end of search.
     * @param solver the current solver (should be outside ref?)
     */
    public void FindSuperPoly(Solver solver){
        int cpt=0;
        HashMap<String, Integer> map = new HashMap<>();
        while(solver.solve()){
            //solver.showSolutions();
            //exportArcFromSolution();
            //utilitaire.TikZexport(this);

            if(false){
                System.out.println();
                System.out.println("solution #"+(cpt++));
                System.out.println(LocalTime.now());
            }


            //utilitaire.graphVizExport(this);
            StringBuilder foundNothing = new StringBuilder();
            for(int node:graph.getMandatoryPredecessorsOf(idxSink)){
                if(isNodeRegisterA(node)) {
                    foundNothing.append(utilitaire.getNodeName(node));
                }
            }
            if(foundNothing.length()==0) foundNothing = new StringBuilder("One");
            //System.out.println(foundNothing);
            if(map.containsKey(foundNothing.toString())){
                map.replace(foundNothing.toString(),map.get(foundNothing.toString())+1);
            }else{
                map.put(foundNothing.toString(),1);
            }
        }
        //printListOfArc();

        System.out.println("SuperPoly:");
        for(Map.Entry<String, Integer> entry : map.entrySet()){
            if(entry.getValue()%2==1){
                System.out.println(entry.getValue()+"\t#"+entry.getKey());
            }
        }
        if(true) return;//set to false if you also want to see solutions found with over count.
        System.out.println("Non SuperPoly:");
        for(Map.Entry<String, Integer> entry : map.entrySet()){
            if(entry.getValue()%2==0){
                System.out.println(entry.getValue()+"\t#"+entry.getKey());
            }
        }
        printStats(map);
    }



}























