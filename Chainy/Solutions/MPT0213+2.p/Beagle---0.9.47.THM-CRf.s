%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0213+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:19 EST 2020

% Result     : Theorem 18.13s
% Output     : CNFRefutation 18.13s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 112 expanded)
%              Number of leaves         :   74 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  76 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_26 > #skF_35 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_32 > #skF_31 > #skF_4 > #skF_36 > #skF_10 > #skF_34 > #skF_12 > #skF_28 > #skF_33 > #skF_5 > #skF_19 > #skF_30 > #skF_27 > #skF_9 > #skF_7 > #skF_20 > #skF_24 > #skF_23 > #skF_14 > #skF_3 > #skF_2 > #skF_21 > #skF_8 > #skF_25 > #skF_29 > #skF_16 > #skF_22 > #skF_15

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

tff('#skF_34',type,(
    '#skF_34': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_28',type,(
    '#skF_28': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

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

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_661,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t6_boole)).

tff(f_1172,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_234,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

tff(f_1166,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_864,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',d1_enumset1)).

tff(f_505,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t36_xboole_1)).

tff(f_515,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t39_xboole_1)).

tff(f_539,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t45_xboole_1)).

tff(f_541,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t46_xboole_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d5_xboole_0)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1013,plain,(
    ! [A_964] :
      ( k1_xboole_0 = A_964
      | ~ v1_xboole_0(A_964) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_1022,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_1013])).

tff(c_934,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_1172])).

tff(c_1029,plain,(
    k3_tarski('#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_1022,c_934])).

tff(c_190,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_1749,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | A_79 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_190])).

tff(c_34790,plain,(
    ! [A_1978,C_1979] :
      ( r2_hidden('#skF_36'(A_1978,k3_tarski(A_1978),C_1979),A_1978)
      | ~ r2_hidden(C_1979,k3_tarski(A_1978)) ) ),
    inference(cnfTransformation,[status(thm)],[f_1166])).

tff(c_512,plain,(
    ! [E_427,B_422,C_423] : r2_hidden(E_427,k1_enumset1(E_427,B_422,C_423)) ),
    inference(cnfTransformation,[status(thm)],[f_864])).

tff(c_340,plain,(
    ! [A_236,B_237] : r1_tarski(k4_xboole_0(A_236,B_237),A_236) ),
    inference(cnfTransformation,[status(thm)],[f_505])).

tff(c_348,plain,(
    ! [A_242,B_243] : k2_xboole_0(A_242,k4_xboole_0(B_243,A_242)) = k2_xboole_0(A_242,B_243) ),
    inference(cnfTransformation,[status(thm)],[f_515])).

tff(c_364,plain,(
    ! [A_260,B_261] :
      ( k2_xboole_0(A_260,k4_xboole_0(B_261,A_260)) = B_261
      | ~ r1_tarski(A_260,B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_539])).

tff(c_3405,plain,(
    ! [A_1144,B_1145] :
      ( k2_xboole_0(A_1144,B_1145) = B_1145
      | ~ r1_tarski(A_1144,B_1145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_364])).

tff(c_3444,plain,(
    ! [A_1146,B_1147] : k2_xboole_0(k4_xboole_0(A_1146,B_1147),A_1146) = A_1146 ),
    inference(resolution,[status(thm)],[c_340,c_3405])).

tff(c_366,plain,(
    ! [A_262,B_263] : k4_xboole_0(A_262,k2_xboole_0(A_262,B_263)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_541])).

tff(c_1639,plain,(
    ! [A_262,B_263] : k4_xboole_0(A_262,k2_xboole_0(A_262,B_263)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_366])).

tff(c_3471,plain,(
    ! [A_1146,B_1147] : k4_xboole_0(k4_xboole_0(A_1146,B_1147),A_1146) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_3444,c_1639])).

tff(c_8808,plain,(
    ! [D_1343,B_1344,A_1345] :
      ( ~ r2_hidden(D_1343,B_1344)
      | ~ r2_hidden(D_1343,k4_xboole_0(A_1345,B_1344)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8867,plain,(
    ! [D_1346,A_1347] :
      ( ~ r2_hidden(D_1346,A_1347)
      | ~ r2_hidden(D_1346,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3471,c_8808])).

tff(c_8903,plain,(
    ! [E_427] : ~ r2_hidden(E_427,'#skF_9') ),
    inference(resolution,[status(thm)],[c_512,c_8867])).

tff(c_34887,plain,(
    ! [C_1980] : ~ r2_hidden(C_1980,k3_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_34790,c_8903])).

tff(c_34915,plain,(
    k3_tarski('#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1749,c_34887])).

tff(c_34925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1029,c_34915])).
%------------------------------------------------------------------------------
