package utils;
import org.chocosolver.solver.variables.events.GraphEventType;
public class MyGraphEventType {

    public static GraphEventType VOID =  GraphEventType.VOID;
    public static GraphEventType REMOVE_NODE =  GraphEventType.REMOVE_NODE;
    public static GraphEventType ADD_NODE =  GraphEventType.ADD_NODE;
    public static GraphEventType REMOVE_EDGE =  GraphEventType.REMOVE_EDGE;
    public static GraphEventType ADD_EDGE =  GraphEventType.ADD_EDGE;
    public static int ALL_EVENTS =  GraphEventType.ALL_EVENTS;


    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************

    private final int mask;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************

    MyGraphEventType(int mask) {
        this.mask = mask;
    }
    MyGraphEventType() {
        this.mask = 0;
    }

    //***********************************************************************************
    // METHODS
    //***********************************************************************************

    public int getMask() {
        return mask;
    }
    public static boolean isAddNode(int mask) {
        return (mask & ADD_NODE.getMask()) != 0;
    }

    public static boolean isAddArc(int mask) {
        return (mask & ADD_EDGE.getMask()) != 0;
    }
    public static boolean isAddEdge(int mask) {
        return (mask & ADD_EDGE.getMask()) != 0;
    }

    public static boolean isRemNode(int mask) {
        return (mask & REMOVE_NODE.getMask()) != 0;
    }

    public static boolean isRemArc(int mask) {
        return (mask & REMOVE_EDGE.getMask()) != 0;
    }
    public static boolean isRemEdge(int mask) {
        return (mask & REMOVE_EDGE.getMask()) != 0;
    }

}
