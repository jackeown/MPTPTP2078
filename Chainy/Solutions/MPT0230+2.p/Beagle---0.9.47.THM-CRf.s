%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0230+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:20 EST 2020

% Result     : Theorem 17.76s
% Output     : CNFRefutation 17.76s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 125 expanded)
%              Number of leaves         :   78 (  86 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 100 expanded)
%              Number of equality atoms :   31 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_26 > #skF_35 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_32 > #skF_38 > #skF_31 > #skF_4 > #skF_36 > #skF_37 > #skF_10 > #skF_34 > #skF_12 > #skF_28 > #skF_39 > #skF_33 > #skF_5 > #skF_19 > #skF_30 > #skF_27 > #skF_9 > #skF_7 > #skF_20 > #skF_24 > #skF_23 > #skF_14 > #skF_3 > #skF_2 > #skF_21 > #skF_8 > #skF_25 > #skF_29 > #skF_16 > #skF_22 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_26',type,(
    '#skF_26': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_35',type,(
    '#skF_35': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_32',type,(
    '#skF_32': ( $i * $i ) > $i )).

tff('#skF_38',type,(
    '#skF_38': $i )).

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

tff('#skF_37',type,(
    '#skF_37': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_34',type,(
    '#skF_34': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_28',type,(
    '#skF_28': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_39',type,(
    '#skF_39': $i )).

tff('#skF_33',type,(
    '#skF_33': ( $i * $i ) > $i )).

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

tff('#skF_23',type,(
    '#skF_23': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_21',type,(
    '#skF_21': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_25',type,(
    '#skF_25': ( $i * ( $i * $i ) ) > $i )).

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

tff(f_127,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_661,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t6_boole)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_1244,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_234,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

tff(f_1286,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_1190,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_849,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',commutativity_k2_tarski)).

tff(f_473,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t28_xboole_1)).

tff(f_199,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t4_xboole_0)).

tff(f_880,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',d2_tarski)).

tff(c_106,plain,(
    ! [A_46] : k3_xboole_0(A_46,A_46) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1171,plain,(
    ! [A_1031] :
      ( k1_xboole_0 = A_1031
      | ~ v1_xboole_0(A_1031) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1180,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_1171])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4038,plain,(
    ! [A_1210,B_1211] :
      ( r1_xboole_0(A_1210,B_1211)
      | k3_xboole_0(A_1210,B_1211) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_82])).

tff(c_976,plain,(
    ! [B_988] : ~ r1_xboole_0(k1_tarski(B_988),k1_tarski(B_988)) ),
    inference(cnfTransformation,[status(thm)],[f_1244])).

tff(c_4050,plain,(
    ! [B_988] : k3_xboole_0(k1_tarski(B_988),k1_tarski(B_988)) != '#skF_9' ),
    inference(resolution,[status(thm)],[c_4038,c_976])).

tff(c_4056,plain,(
    ! [B_988] : k1_tarski(B_988) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_4050])).

tff(c_190,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_2279,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | A_79 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_190])).

tff(c_998,plain,(
    '#skF_37' != '#skF_39' ),
    inference(cnfTransformation,[status(thm)],[f_1286])).

tff(c_1000,plain,(
    '#skF_38' != '#skF_37' ),
    inference(cnfTransformation,[status(thm)],[f_1286])).

tff(c_940,plain,(
    ! [A_962,B_963] :
      ( r1_xboole_0(k1_tarski(A_962),B_963)
      | r2_hidden(A_962,B_963) ) ),
    inference(cnfTransformation,[status(thm)],[f_1190])).

tff(c_504,plain,(
    ! [B_420,A_419] : k2_tarski(B_420,A_419) = k2_tarski(A_419,B_420) ),
    inference(cnfTransformation,[status(thm)],[f_849])).

tff(c_1002,plain,(
    r1_tarski(k1_tarski('#skF_37'),k2_tarski('#skF_38','#skF_39')) ),
    inference(cnfTransformation,[status(thm)],[f_1286])).

tff(c_1019,plain,(
    r1_tarski(k1_tarski('#skF_37'),k2_tarski('#skF_39','#skF_38')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_1002])).

tff(c_2968,plain,(
    ! [A_1182,B_1183] :
      ( k3_xboole_0(A_1182,B_1183) = A_1182
      | ~ r1_tarski(A_1182,B_1183) ) ),
    inference(cnfTransformation,[status(thm)],[f_473])).

tff(c_3010,plain,(
    k3_xboole_0(k1_tarski('#skF_37'),k2_tarski('#skF_39','#skF_38')) = k1_tarski('#skF_37') ),
    inference(resolution,[status(thm)],[c_1019,c_2968])).

tff(c_5327,plain,(
    ! [A_1271,B_1272,C_1273] :
      ( ~ r1_xboole_0(A_1271,B_1272)
      | ~ r2_hidden(C_1273,k3_xboole_0(A_1271,B_1272)) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_5339,plain,(
    ! [C_1273] :
      ( ~ r1_xboole_0(k1_tarski('#skF_37'),k2_tarski('#skF_39','#skF_38'))
      | ~ r2_hidden(C_1273,k1_tarski('#skF_37')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3010,c_5327])).

tff(c_6002,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_37'),k2_tarski('#skF_39','#skF_38')) ),
    inference(splitLeft,[status(thm)],[c_5339])).

tff(c_6045,plain,(
    r2_hidden('#skF_37',k2_tarski('#skF_39','#skF_38')) ),
    inference(resolution,[status(thm)],[c_940,c_6002])).

tff(c_29842,plain,(
    ! [D_1900,B_1901,A_1902] :
      ( D_1900 = B_1901
      | D_1900 = A_1902
      | ~ r2_hidden(D_1900,k2_tarski(A_1902,B_1901)) ) ),
    inference(cnfTransformation,[status(thm)],[f_880])).

tff(c_29860,plain,
    ( '#skF_38' = '#skF_37'
    | '#skF_37' = '#skF_39' ),
    inference(resolution,[status(thm)],[c_6045,c_29842])).

tff(c_29895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_998,c_1000,c_29860])).

tff(c_29898,plain,(
    ! [C_1903] : ~ r2_hidden(C_1903,k1_tarski('#skF_37')) ),
    inference(splitRight,[status(thm)],[c_5339])).

tff(c_29906,plain,(
    k1_tarski('#skF_37') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2279,c_29898])).

tff(c_29918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4056,c_29906])).
%------------------------------------------------------------------------------
