package utils;


import main.TriviumAlban;

public class Shift {
    public TriviumAlban trivium;
    private int nbMaxNodePerRegistre;
    public final static int A_self = 69;
    public final static int A_short = 66;
    public final static int A_double1 = 109;
    public final static int A_double2 = 110;
    public final static int A_long = 111;

    public final static int B_self = 78;
    public final static int B_short = 66;
    public final static int B_double1 = 91;
    public final static int B_double2 = 92;
    public final static int B_long = 93;

    public final static int C_self = 87;
    public final static int C_short = 69;
    public final static int C_double1 = 82;
    public final static int C_double2 = 83;
    public final static int C_long = 84;

    public Shift(TriviumAlban triviumData) {
        this.trivium = triviumData;
        this.nbMaxNodePerRegistre = triviumData.nbMaxNodePerRegistre;
    }
    public int getShift_registerA_self(int round){return round+A_self;}
    public int getShift_registerA_short(int round){return round+Shift.A_short+2*nbMaxNodePerRegistre;}
    public int getShift_registerA_long(int round){return round+Shift.A_long+2*nbMaxNodePerRegistre;}
    public int getShift_registerA_double1(int round){return round+Shift.A_double1+2*nbMaxNodePerRegistre;}
    public int getShift_registerA_double2(int round){return round+Shift.A_double2+2*nbMaxNodePerRegistre;}

    public int getShift_registerB_self(int round){return round+Shift.B_self;}
    public int getShift_registerB_short(int round){return round+Shift.B_short-nbMaxNodePerRegistre;}
    public int getShift_registerB_long(int round){return round+Shift.B_long-nbMaxNodePerRegistre;}
    public int getShift_registerB_double1(int round){return round+Shift.B_double1-nbMaxNodePerRegistre;}
    public int getShift_registerB_double2(int round){return round+Shift.B_double2-nbMaxNodePerRegistre;}

    public int getShift_registerC_self(int round){return round+Shift.C_self;}
    public int getShift_registerC_short(int round){return round+Shift.C_short-nbMaxNodePerRegistre;}
    public int getShift_registerC_long(int round){return round+Shift.C_long-nbMaxNodePerRegistre;}
    public int getShift_registerC_double1(int round){return round+Shift.C_double1-nbMaxNodePerRegistre;}
    public int getShift_registerC_double2(int round){return round+Shift.C_double2-nbMaxNodePerRegistre;}


    public int shortSuccIndex(int idx){
        if(trivium.isNodeRegisterA(idx)) return idx+A_short+2*nbMaxNodePerRegistre;
        if(trivium.isNodeRegisterB(idx)) return idx+B_short-nbMaxNodePerRegistre;
        if(trivium.isNodeRegisterC(idx)) return idx+C_short-nbMaxNodePerRegistre;
        return -1;
    }
    public int longSuccIndex(int idx){
        if(trivium.isNodeRegisterA(idx)) return idx+A_long+2*nbMaxNodePerRegistre;
        if(trivium.isNodeRegisterB(idx)) return idx+B_long-nbMaxNodePerRegistre;
        if(trivium.isNodeRegisterC(idx)) return idx+C_long-nbMaxNodePerRegistre;
        return -1;
    }
    public int selfSuccIndex(int idx){
        if(trivium.isNodeRegisterA(idx)) return idx+A_self;
        if(trivium.isNodeRegisterB(idx)) return idx+B_self;
        if(trivium.isNodeRegisterC(idx)) return idx+C_self;
        return -1;
    }
    public int double1SuccIndex(int idx){
        if(trivium.isNodeRegisterA(idx)) return idx+A_double1+2*nbMaxNodePerRegistre;
        if(trivium.isNodeRegisterB(idx)) return idx+B_double1-nbMaxNodePerRegistre;
        if(trivium.isNodeRegisterC(idx)) return idx+C_double1-nbMaxNodePerRegistre;
        return -1;
    }
    public int double2SuccIndex(int idx){
        if(trivium.isNodeRegisterA(idx)) return idx+A_double2+2*nbMaxNodePerRegistre;
        if(trivium.isNodeRegisterB(idx)) return idx+B_double2-nbMaxNodePerRegistre;
        if(trivium.isNodeRegisterC(idx)) return idx+C_double2-nbMaxNodePerRegistre;
        return -1;
    }
}