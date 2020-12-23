%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0249+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:21 EST 2020

% Result     : Theorem 16.49s
% Output     : CNFRefutation 16.49s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 333 expanded)
%              Number of leaves         :   91 ( 162 expanded)
%              Depth                    :   18
%              Number of atoms          :  115 ( 453 expanded)
%              Number of equality atoms :   53 ( 227 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_26 > #skF_11 > #skF_41 > #skF_33 > #skF_18 > #skF_6 > #skF_44 > #skF_1 > #skF_17 > #skF_32 > #skF_31 > #skF_4 > #skF_36 > #skF_10 > #skF_47 > #skF_37 > #skF_12 > #skF_45 > #skF_28 > #skF_46 > #skF_35 > #skF_5 > #skF_19 > #skF_30 > #skF_27 > #skF_9 > #skF_7 > #skF_20 > #skF_24 > #skF_34 > #skF_23 > #skF_14 > #skF_3 > #skF_38 > #skF_2 > #skF_21 > #skF_40 > #skF_8 > #skF_25 > #skF_43 > #skF_29 > #skF_16 > #skF_22 > #skF_15 > #skF_42 > #skF_39

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_26',type,(
    '#skF_26': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_41',type,(
    '#skF_41': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_33',type,(
    '#skF_33': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_44',type,(
    '#skF_44': ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_32',type,(
    '#skF_32': ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_31',type,(
    '#skF_31': ( $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_36',type,(
    '#skF_36': ( $i * ( $i * $i ) ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_47',type,(
    '#skF_47': $i )).

tff('#skF_37',type,(
    '#skF_37': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_45',type,(
    '#skF_45': $i )).

tff('#skF_28',type,(
    '#skF_28': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_46',type,(
    '#skF_46': $i )).

tff('#skF_35',type,(
    '#skF_35': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_30',type,(
    '#skF_30': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_27',type,(
    '#skF_27': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff('#skF_24',type,(
    '#skF_24': ( $i * $i ) > $i )).

tff('#skF_34',type,(
    '#skF_34': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_23',type,(
    '#skF_23': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_38',type,(
    '#skF_38': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_21',type,(
    '#skF_21': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_40',type,(
    '#skF_40': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_25',type,(
    '#skF_25': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_43',type,(
    '#skF_43': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff('#skF_29',type,(
    '#skF_29': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff('#skF_42',type,(
    '#skF_42': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_39',type,(
    '#skF_39': ( $i * $i ) > $i )).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_661,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t6_boole)).

tff(f_509,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t37_xboole_1)).

tff(f_1480,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_234,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

tff(f_1402,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_354,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t10_xboole_1)).

tff(f_1484,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_387,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t11_xboole_1)).

tff(f_265,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

tff(f_473,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t28_xboole_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d4_xboole_0)).

tff(f_515,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t39_xboole_1)).

tff(f_539,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t45_xboole_1)).

tff(f_1232,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1233,plain,(
    ! [A_1128] :
      ( k1_xboole_0 = A_1128
      | ~ v1_xboole_0(A_1128) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1242,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_1233])).

tff(c_342,plain,(
    ! [A_238,B_239] :
      ( r1_tarski(A_238,B_239)
      | k4_xboole_0(A_238,B_239) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_509])).

tff(c_3214,plain,(
    ! [A_238,B_239] :
      ( r1_tarski(A_238,B_239)
      | k4_xboole_0(A_238,B_239) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_342])).

tff(c_1144,plain,(
    '#skF_47' != '#skF_46' ),
    inference(cnfTransformation,[status(thm)],[f_1480])).

tff(c_1140,plain,(
    k1_xboole_0 != '#skF_47' ),
    inference(cnfTransformation,[status(thm)],[f_1480])).

tff(c_1253,plain,(
    '#skF_47' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_1140])).

tff(c_190,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_2228,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | A_79 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_190])).

tff(c_1094,plain,(
    ! [A_1092,B_1093] :
      ( r1_tarski(k1_tarski(A_1092),B_1093)
      | ~ r2_hidden(A_1092,B_1093) ) ),
    inference(cnfTransformation,[status(thm)],[f_1402])).

tff(c_1146,plain,(
    k2_xboole_0('#skF_46','#skF_47') = k1_tarski('#skF_45') ),
    inference(cnfTransformation,[status(thm)],[f_1480])).

tff(c_12683,plain,(
    ! [A_1544,C_1545,B_1546] :
      ( r1_tarski(A_1544,k2_xboole_0(C_1545,B_1546))
      | ~ r1_tarski(A_1544,B_1546) ) ),
    inference(cnfTransformation,[status(thm)],[f_354])).

tff(c_12809,plain,(
    ! [A_1547] :
      ( r1_tarski(A_1547,k1_tarski('#skF_45'))
      | ~ r1_tarski(A_1547,'#skF_47') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1146,c_12683])).

tff(c_1148,plain,(
    ! [B_1112,A_1111] :
      ( B_1112 = A_1111
      | ~ r1_tarski(k1_tarski(A_1111),k1_tarski(B_1112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_1484])).

tff(c_12863,plain,(
    ! [A_1548] :
      ( A_1548 = '#skF_45'
      | ~ r1_tarski(k1_tarski(A_1548),'#skF_47') ) ),
    inference(resolution,[status(thm)],[c_12809,c_1148])).

tff(c_12877,plain,(
    ! [A_1549] :
      ( A_1549 = '#skF_45'
      | ~ r2_hidden(A_1549,'#skF_47') ) ),
    inference(resolution,[status(thm)],[c_1094,c_12863])).

tff(c_12885,plain,
    ( '#skF_18'('#skF_47') = '#skF_45'
    | '#skF_47' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2228,c_12877])).

tff(c_12893,plain,(
    '#skF_18'('#skF_47') = '#skF_45' ),
    inference(negUnitSimplification,[status(thm)],[c_1253,c_12885])).

tff(c_12901,plain,
    ( r2_hidden('#skF_45','#skF_47')
    | '#skF_47' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_12893,c_2228])).

tff(c_12905,plain,(
    r2_hidden('#skF_45','#skF_47') ),
    inference(negUnitSimplification,[status(thm)],[c_1253,c_12901])).

tff(c_7269,plain,(
    ! [A_1428,C_1429,B_1430] :
      ( r1_tarski(A_1428,C_1429)
      | ~ r1_tarski(k2_xboole_0(A_1428,B_1430),C_1429) ) ),
    inference(cnfTransformation,[status(thm)],[f_387])).

tff(c_7570,plain,(
    ! [C_1436] :
      ( r1_tarski('#skF_46',C_1436)
      | ~ r1_tarski(k1_tarski('#skF_45'),C_1436) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1146,c_7269])).

tff(c_7603,plain,(
    ! [B_1093] :
      ( r1_tarski('#skF_46',B_1093)
      | ~ r2_hidden('#skF_45',B_1093) ) ),
    inference(resolution,[status(thm)],[c_1094,c_7570])).

tff(c_12924,plain,(
    r1_tarski('#skF_46','#skF_47') ),
    inference(resolution,[status(thm)],[c_12905,c_7603])).

tff(c_15330,plain,(
    ! [B_1599,A_1600] :
      ( B_1599 = A_1600
      | ~ r1_tarski(B_1599,A_1600)
      | ~ r1_tarski(A_1600,B_1599) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_15350,plain,
    ( '#skF_47' = '#skF_46'
    | ~ r1_tarski('#skF_47','#skF_46') ),
    inference(resolution,[status(thm)],[c_12924,c_15330])).

tff(c_15416,plain,(
    ~ r1_tarski('#skF_47','#skF_46') ),
    inference(negUnitSimplification,[status(thm)],[c_1144,c_15350])).

tff(c_15458,plain,(
    k4_xboole_0('#skF_47','#skF_46') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_3214,c_15416])).

tff(c_1142,plain,(
    k1_xboole_0 != '#skF_46' ),
    inference(cnfTransformation,[status(thm)],[f_1480])).

tff(c_1254,plain,(
    '#skF_46' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_1142])).

tff(c_320,plain,(
    ! [A_211,B_212] :
      ( k3_xboole_0(A_211,B_212) = A_211
      | ~ r1_tarski(A_211,B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_473])).

tff(c_12946,plain,(
    k3_xboole_0('#skF_46','#skF_47') = '#skF_46' ),
    inference(resolution,[status(thm)],[c_12924,c_320])).

tff(c_22042,plain,(
    ! [D_1723,B_1724,A_1725] :
      ( r2_hidden(D_1723,B_1724)
      | ~ r2_hidden(D_1723,k3_xboole_0(A_1725,B_1724)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22223,plain,(
    ! [D_1727] :
      ( r2_hidden(D_1727,'#skF_47')
      | ~ r2_hidden(D_1727,'#skF_46') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12946,c_22042])).

tff(c_12875,plain,(
    ! [A_1092] :
      ( A_1092 = '#skF_45'
      | ~ r2_hidden(A_1092,'#skF_47') ) ),
    inference(resolution,[status(thm)],[c_1094,c_12863])).

tff(c_22347,plain,(
    ! [D_1728] :
      ( D_1728 = '#skF_45'
      | ~ r2_hidden(D_1728,'#skF_46') ) ),
    inference(resolution,[status(thm)],[c_22223,c_12875])).

tff(c_22371,plain,
    ( '#skF_18'('#skF_46') = '#skF_45'
    | '#skF_46' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2228,c_22347])).

tff(c_22384,plain,(
    '#skF_18'('#skF_46') = '#skF_45' ),
    inference(negUnitSimplification,[status(thm)],[c_1254,c_22371])).

tff(c_22503,plain,
    ( r2_hidden('#skF_45','#skF_46')
    | '#skF_46' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_22384,c_2228])).

tff(c_22507,plain,(
    r2_hidden('#skF_45','#skF_46') ),
    inference(negUnitSimplification,[status(thm)],[c_1254,c_22503])).

tff(c_348,plain,(
    ! [A_242,B_243] : k2_xboole_0(A_242,k4_xboole_0(B_243,A_242)) = k2_xboole_0(A_242,B_243) ),
    inference(cnfTransformation,[status(thm)],[f_515])).

tff(c_364,plain,(
    ! [A_260,B_261] :
      ( k2_xboole_0(A_260,k4_xboole_0(B_261,A_260)) = B_261
      | ~ r1_tarski(A_260,B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_539])).

tff(c_1177,plain,(
    ! [A_260,B_261] :
      ( k2_xboole_0(A_260,B_261) = B_261
      | ~ r1_tarski(A_260,B_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_364])).

tff(c_12945,plain,(
    k2_xboole_0('#skF_46','#skF_47') = '#skF_47' ),
    inference(resolution,[status(thm)],[c_12924,c_1177])).

tff(c_12948,plain,(
    k1_tarski('#skF_45') = '#skF_47' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12945,c_1146])).

tff(c_988,plain,(
    ! [A_1011,B_1012] :
      ( k4_xboole_0(k1_tarski(A_1011),B_1012) = k1_xboole_0
      | ~ r2_hidden(A_1011,B_1012) ) ),
    inference(cnfTransformation,[status(thm)],[f_1232])).

tff(c_16293,plain,(
    ! [A_1635,B_1636] :
      ( k4_xboole_0(k1_tarski(A_1635),B_1636) = '#skF_9'
      | ~ r2_hidden(A_1635,B_1636) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_988])).

tff(c_16430,plain,(
    ! [B_1636] :
      ( k4_xboole_0('#skF_47',B_1636) = '#skF_9'
      | ~ r2_hidden('#skF_45',B_1636) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12948,c_16293])).

tff(c_22526,plain,(
    k4_xboole_0('#skF_47','#skF_46') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_22507,c_16430])).

tff(c_22549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15458,c_22526])).
%------------------------------------------------------------------------------
