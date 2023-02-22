package utils;


import main.TriviumAlban;
import org.chocosolver.solver.variables.DirectedGraphVar;
import org.chocosolver.util.objects.setDataStructures.ISet;
import org.testng.internal.collections.Ints;
import propagators.PropRIV_VARandSet_alban;

import java.util.Comparator;
import java.util.List;


public class utilitaire {
    public static int tmp_nbMaxNodePerRegistre;
    public static int tmp_nbRound;
    public static int tmp_lastBit;
    public static int tmp_idxSource;
    public static int tmp_idxSink;
    public static TriviumAlban tmp_triv;
    public static DirectedGraphVar tmp_graph;
    public static PropRIV_VARandSet_alban propagRIV;
    public static int tmp_nbInnerProfondeur;



    /*
        utility fonction

     */
    public static String getNodeName(int node){

        String add="";//TO add RIV infos at the end if we have them.
        if(propagRIV!=null){
            add = "_"+propagRIV.getRIVLB(node)+"_"+propagRIV.getRIVUB(node);
        }
        if(node==tmp_idxSink) return "sink"+add;
        if(node==tmp_idxSource) return "source"+add;

        if(node<tmp_nbMaxNodePerRegistre){//registreA
            if(node<=tmp_nbInnerProfondeur) return "A"+node+add;
            return "x"+(node-tmp_nbInnerProfondeur)+add;
        }
        if(node<2*tmp_nbMaxNodePerRegistre){//registreB
            if(node<=tmp_nbMaxNodePerRegistre+tmp_nbInnerProfondeur)
                return "B"+(node-tmp_nbMaxNodePerRegistre)+add;
            return "iv"+((node-tmp_nbInnerProfondeur)-tmp_nbMaxNodePerRegistre)+add;

        }
        if(node<3*tmp_nbMaxNodePerRegistre){//registreC
            if(node<=2*tmp_nbMaxNodePerRegistre+tmp_nbInnerProfondeur)
                return "C"+(node-2*tmp_nbMaxNodePerRegistre)+add;
            return "z"+((node-tmp_nbInnerProfondeur)-2*tmp_nbMaxNodePerRegistre)+add;
        }
        return "getNodeName NOT FOUND";
    }

    /*
    used to set trivium var for local use : old way of doing things, should rework that
     */
    public static void setTriviumVar(TriviumAlban triv) {
        tmp_nbRound = triv.nbRound;
        tmp_nbMaxNodePerRegistre = triv.nbMaxNodePerRegistre;
        tmp_lastBit = triv.lastBit;
        tmp_nbInnerProfondeur = triv.nbInnerRound;
        tmp_graph = triv.graph;
        tmp_idxSink = triv.idxSink;
        tmp_idxSource = triv.idxSource;
        tmp_triv = triv;
    }

    /*
    * output the list of nodes in the round order (from round 0 (
    */
    public static List<Integer> roundCroissant(ISet myISet){
        Comparator<Integer> mycomparator = (a, b) -> {
            if (a==tmp_idxSource) return -1;
            if (b==tmp_idxSource) return 1;

            if (b==tmp_idxSink) return -1;
            if (a==tmp_idxSink) return 1;

            if ((a%tmp_nbMaxNodePerRegistre)<(b%tmp_nbMaxNodePerRegistre)) return -1;
            if ((a%tmp_nbMaxNodePerRegistre)>(b%tmp_nbMaxNodePerRegistre)) return 1;
            if (a>b) return -1;//put reg C before reg A.
            if (a<b) return 1;
            return 0;
        };
        List<Integer> l = Ints.asList(myISet.toArray());
        l.sort(mycomparator);
        return l;
    }

    public static List<Integer> roundDecroissant(ISet myISet){
        Comparator<Integer> mycomparator = (a, b) -> {
            if (a==tmp_idxSource) return 1;
            if (b==tmp_idxSource) return -1;

            if (b==tmp_idxSink) return 1;
            if (a==tmp_idxSink) return -1;

            if ((a%tmp_nbMaxNodePerRegistre)<(b%tmp_nbMaxNodePerRegistre)) return 1;
            if ((a%tmp_nbMaxNodePerRegistre)>(b%tmp_nbMaxNodePerRegistre)) return -1;
            if (a>b) return 1;//put reg A before reg C.
            if (a<b) return -1;
            return 0;
        };
        List<Integer> l = Ints.asList(myISet.toArray());
        l.sort(mycomparator);
        return l;
    }

    /*
Functions to export the graph to print it (in tikz, or graphviz)
 */


    public static void graphVizExport(TriviumAlban triv, PropRIV_VARandSet_alban propag) {
        propagRIV = propag;
        graphVizExport(triv);
    }
    public static void graphVizExport(TriviumAlban triv) {
        setTriviumVar(triv);
        System.out.println(graphVizExport());
    }
    public static void graphVizExport(TriviumAlban triv,DirectedGraphVar g) {
        setTriviumVar(triv);
        tmp_graph = g;
        System.out.println(graphVizExport());
    }

    static boolean extremit=false;
    static int nbCalling =0;
    private static StringBuilder graphVizExport(){
        StringBuilder sb = new StringBuilder();
        System.out.println("call"+(++nbCalling)+"\n");
        sb.append(extremit?"digraph Trivium{\n":"");
        sb.append(graphVizExportNodesLinear()).append("\n");
        sb.append(graphVizExportArcs());
        sb.append(extremit? "\n}\n":"\n");
        return sb;
    }
    public static int getModuloTroisOfNode(int node){
        return ((node+10*tmp_nbMaxNodePerRegistre)%1000)%3;
    }


    public static void TikZexport(TriviumAlban triv) {
        setTriviumVar(triv);
        System.out.println(TikZexport());
    }
    private static StringBuilder TikZexport(){
        StringBuilder sb = new StringBuilder();
        sb.append(extremit?"\\begin{figure}[H]\n\\centering\n\\begin{tikzpicture}[node distance=1cm,every text node part/.style={align=center}]":"");
        sb.append(TikzExportNodes()).append("\n\n");
        sb.append(TikzExportArcs());
        sb.append(extremit? "\\end{tikzpicture} \n\\end{figure}":"\n");
        return sb;
    }

    public static StringBuilder TikzExportArcs() {
        StringBuilder sb = new StringBuilder();
        sb.append(TikzExportArcsDouble());
        sb.append(TikzExportArcsLong());
        sb.append(TikzExportArcsShort());
        sb.append(TikzExportArcsSelf());
        return sb ;
    }
    public static StringBuilder TikzExportArcsDouble() {
        StringBuilder sb = new StringBuilder();
        boolean doneSomething = false;
        //arc double:
        sb.append("\\foreach \\from/\\to/\\arr in {");
        for(int node:tmp_graph.getMandatoryNodes()){
            ISet succs = tmp_graph.getMandatorySuccessorsOf(node);
            if(succs.size()==2){
                doneSomething = true;
                sb.append(node+"/"+succs.min()+"/,"+node+"/"+succs.max()+"/,");
            }
        }
        if(!doneSomething) return new StringBuilder();
        sb.deleteCharAt(sb.length()-1);//delete the last comma
        sb.append("}\n\\draw[tr] (\\from) -- (\\to)node[sloped,above,legende]{\\arr};\n");
        return sb ;
    }
    public static StringBuilder TikzExportArcsLong() {
        StringBuilder sb = new StringBuilder();
        boolean doneSomething = false;
        //arc double:
        sb.append("\\foreach \\from/\\to/\\arr in {");
        for(int node:tmp_graph.getMandatoryNodes()){
            ISet succs = tmp_graph.getMandatorySuccessorsOf(node);
            if(succs.size()==1){
                int succ = succs.min();
                if(tmp_triv.isArcLong(node, succ)){
                    doneSomething = true;
                    sb.append(node+"/"+succ+"/,");
                }
            }
        }
        if(!doneSomething) return new StringBuilder();
        sb.deleteCharAt(sb.length()-1);//delete the last comma
        sb.append("}\n\\draw[tv] (\\from) -- (\\to)node[sloped,above,legende]{\\arr};\n");
        return sb ;
    }
    public static StringBuilder TikzExportArcsShort() {
        StringBuilder sb = new StringBuilder();
        boolean doneSomething = false;
        //arc double:
        sb.append("\\foreach \\from/\\to/\\arr in {");
        for(int node:tmp_graph.getMandatoryNodes()){
            ISet succs = tmp_graph.getMandatorySuccessorsOf(node);
            if(succs.size()==1){
                int succ = succs.min();
                if(tmp_triv.isArcShort(node, succ)){
                    doneSomething = true;
                    sb.append(node+"/"+succ+"/,");
                }
            }
        }
        if(!doneSomething) return new StringBuilder();
        sb.deleteCharAt(sb.length()-1);//delete the last comma
        sb.append("}\n\\draw[tg] (\\from) -- (\\to)node[sloped,above,legende]{\\arr};\n");
        return sb ;
    }
    public static StringBuilder TikzExportArcsSelf() {
        StringBuilder sb = new StringBuilder();
        boolean doneSomething = false;
        //arc double:
        sb.append("\\foreach \\from/\\to/\\arr in {");
        for(int node:tmp_graph.getMandatoryNodes()){
            ISet succs = tmp_graph.getMandatorySuccessorsOf(node);
            if(succs.size()==1){
                int succ = succs.min();
                if(tmp_triv.isArcSelf(node, succ)){
                    doneSomething = true;
                    sb.append(node+"/"+succ+"/,");
                }
            }
        }
        if(!doneSomething) return new StringBuilder();
        sb.deleteCharAt(sb.length()-1);//delete the last comma
        sb.append("}\n\\draw[tb] (\\from) -- (\\to)node[sloped,above,legende]{\\arr};\n\n");
        return sb ;
    }


    public static StringBuilder getLatexName(int node){
        StringBuilder sb = new StringBuilder();
        if(node<tmp_nbMaxNodePerRegistre){//registreA
            return sb.append("\\regA_{"+(606-node%1000)+"}");
        }
        if(node<2*tmp_nbMaxNodePerRegistre){//registreB
            return sb.append("\\regB_{"+(606-node%1000)+"}");
        }
        if(node<3*tmp_nbMaxNodePerRegistre){//registreC
            return sb.append("\\regC_{"+(606-node%1000)+"}");
        }

        return sb.append("sink");
    }
    public static StringBuilder getLatexNameModulo3(int node){
        StringBuilder sb = new StringBuilder();
        if(node<tmp_nbMaxNodePerRegistre){//registreA
            return sb.append("\\regA_{"+(node%1000)%3+"}");
        }
        if(node<2*tmp_nbMaxNodePerRegistre){//registreB
            return sb.append("\\regB_{"+(node%1000)%3+"}");
        }
        if(node<3*tmp_nbMaxNodePerRegistre){//registreC
            return sb.append("\\regC_{"+(node%1000)%3+"}");
        }

        return sb.append("sink");
    }
    public static StringBuilder getLatexModulo3(int node){
        return new StringBuilder().append((node%1000)%3);
    }
    public static StringBuilder TikzExportNodes() {
        StringBuilder sb = new StringBuilder();
        tikzExportNodesRec(sb,tmp_idxSource,0);
        return sb ;
    }

    public static int tikzExportNodesRec( StringBuilder sb, int node, int idxrow){
        //+getLatexName(node)

        String add="";
        if(node%1000>606) {
            String color = tmp_triv.isNodeRegisterA(node)?"red":"cyan";
            add = " \\textcolor{"+color+"}{" + getNodeName(node) + "}";
        }
        sb.append("\\node[noeudFullGraph]("+node+") at ("+idxrow+",-"+(node%1000)/100.0+") {$"+getLatexModulo3(node)+"$"+add+"};");

        int nextIdx = -1;
        ISet succ = tmp_graph.getMandatorySuccessorsOf(node);
        if(succ.contains(tmp_idxSink)){
            //end of rec : the next node is sink, move to next row.
            nextIdx = idxrow+1;
        }else if(succ.size()==1){
            //if only 1 child : go down
            nextIdx = tikzExportNodesRec(sb, succ.min(),idxrow);
        }else if(succ.size()==2){
            nextIdx = tikzExportNodesRec(sb, succ.max(),idxrow);
            nextIdx = tikzExportNodesRec(sb, succ.min(),nextIdx);
        }


        return nextIdx;
    }

    public static StringBuilder graphVizExportNodes() {
        StringBuilder sb = new StringBuilder();
        sb.append("node [color = blue, fontcolor=blue];");
        for (int i : roundCroissant(tmp_graph.getMandatoryNodes())) {
            //if(!shouldWePrint(i)) continue;
            sb.append(getNodeName(i)).append(" ");
        }
        sb.append("\nnode [color = grey, fontcolor=black];");
        for (int i : roundCroissant(tmp_graph.getPotentialNodes())) {
            //if(!shouldWePrint(i)) continue;

            sb.append(getNodeName(i)).append(" ");
        }
        return sb.append(";") ;
    }
    public static StringBuilder graphVizExportNodesLinear() {
        StringBuilder sb = new StringBuilder();
        sb.append("\n{rank=same;");
        for (int i : roundCroissant(tmp_graph.getPotentialPredecessorOf(tmp_idxSink))) {
            //if(!shouldWePrint(i)) continue;
            sb.append(getNodeName(i)).append(" ");
        }
        sb.append("};");

        sb.append("\nnode [color = blue, fontcolor=blue];");
        for (int i : roundCroissant(tmp_graph.getMandatoryNodes())) {
            //if(!shouldWePrint(i)) continue;
            sb.append(getNodeName(i)).append(" ");
        }
        sb.append("\nnode [color = grey, fontcolor=black];");
        for (int i : roundCroissant(tmp_graph.getPotentialNodes())) {
            //if(!shouldWePrint(i)) continue;
            sb.append(getNodeName(i)).append(" ");
        }
        return sb.append(";") ;
    }
    public static StringBuilder graphVizExportArcs() {
        StringBuilder sb = new StringBuilder();
        for (int i : roundCroissant(tmp_graph.getPotentialNodes())) {
            String Node_i_name = getNodeName(i);
            for (int j : roundCroissant(tmp_graph.getPotentialSuccessorsOf(i))) {
                String Node_j_name = getNodeName(j);
                sb.append(Node_i_name+"->"+Node_j_name+"["+getArcColor(i, j)+getArcStyle(i, j)+"]; ");
            }
        }
        return sb;
    }
    public static StringBuilder graphVizLinearOutput() {
        StringBuilder sb = new StringBuilder();
        String Node_i_name;
        String Node_j_name = null;
        for (int i : roundCroissant(tmp_graph.getPotentialPredecessorOf(tmp_idxSink))) {
            Node_i_name = getNodeName(i);
            if(Node_j_name!=null){
                sb.append(Node_i_name+"->"+Node_j_name+"[style=invis];");
            }
            Node_j_name=Node_i_name;
        }
        return sb;
    }
    public static String getArcStyle(int from, int to){
        if(!tmp_graph.getMandatorySuccessorsOf(from).contains(to)){
            return " style=dashed";
        }
        return "";
    }
    public static String getArcColor(int from, int to){
        if(getNodeName(to).startsWith("sink")) return "color=grey";
        if(from<tmp_nbMaxNodePerRegistre){//registreA
            if(to-from == Shift.A_self) return "color=blue";
            if(to-from == Shift.A_short+2*tmp_nbMaxNodePerRegistre) return "color=grey";
            if(to-from == Shift.A_long+2*tmp_nbMaxNodePerRegistre) return "color=green";
            if(to-from == Shift.A_double1+2*tmp_nbMaxNodePerRegistre) return "color=red";
            if(to-from == Shift.A_double2+2*tmp_nbMaxNodePerRegistre) return "color=red";
        }
        if(from<2*tmp_nbMaxNodePerRegistre){//registreB
            if(to-from == Shift.B_self) return "color=blue";
            if(to-from == Shift.B_double1-tmp_nbMaxNodePerRegistre) return "color=red";
            if(to-from == Shift.B_double2-tmp_nbMaxNodePerRegistre) return "color=red";
            if(to-from == Shift.B_long-tmp_nbMaxNodePerRegistre) return "color=green";
            if(to-from == Shift.B_short-tmp_nbMaxNodePerRegistre) return "color=grey";
        }
        if(from<3*tmp_nbMaxNodePerRegistre){//registreC
            if(to-from == Shift.C_self) return "color=blue";
            if(to-from == Shift.C_double1-tmp_nbMaxNodePerRegistre) return "color=red";
            if(to-from == Shift.C_double2-tmp_nbMaxNodePerRegistre) return "color=red";
            if(to-from == Shift.C_long-tmp_nbMaxNodePerRegistre) return "color=green";
            if(to-from == Shift.C_short-tmp_nbMaxNodePerRegistre) return "color=grey";
        }
        return "color=black";
    }

}
