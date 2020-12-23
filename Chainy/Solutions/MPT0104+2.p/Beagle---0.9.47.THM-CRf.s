%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0104+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:14 EST 2020

% Result     : Theorem 53.74s
% Output     : CNFRefutation 53.74s
% Verified   : 
% Statistics : Number of formulae       :   72 (  74 expanded)
%              Number of leaves         :   48 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  48 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_23 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_22',type,(
    '#skF_22': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_23',type,(
    '#skF_23': $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k5_xboole_0)).

tff(f_706,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k4_xboole_0(A,B),C)
          & r1_tarski(k4_xboole_0(B,A),C) )
       => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

tff(f_270,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_454,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_364,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_406,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_430,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_348,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

tff(f_309,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_10,plain,(
    ! [B_10,A_9] : k5_xboole_0(B_10,A_9) = k5_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_438,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_21','#skF_22'),'#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_706])).

tff(c_459,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_22','#skF_21'),'#skF_23') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_438])).

tff(c_212,plain,(
    ! [A_97,B_98] : k4_xboole_0(k2_xboole_0(A_97,B_98),k3_xboole_0(A_97,B_98)) = k5_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_330,plain,(
    ! [A_234,B_235] : k4_xboole_0(k2_xboole_0(A_234,B_235),k3_xboole_0(A_234,B_235)) = k2_xboole_0(k4_xboole_0(A_234,B_235),k4_xboole_0(B_235,A_234)) ),
    inference(cnfTransformation,[status(thm)],[f_454])).

tff(c_453,plain,(
    ! [A_234,B_235] : k2_xboole_0(k4_xboole_0(A_234,B_235),k4_xboole_0(B_235,A_234)) = k5_xboole_0(A_234,B_235) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_330])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_440,plain,(
    r1_tarski(k4_xboole_0('#skF_22','#skF_21'),'#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_706])).

tff(c_1565,plain,(
    ! [A_441,B_442] :
      ( k3_xboole_0(A_441,B_442) = A_441
      | ~ r1_tarski(A_441,B_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_364])).

tff(c_1602,plain,(
    k3_xboole_0(k4_xboole_0('#skF_22','#skF_21'),'#skF_23') = k4_xboole_0('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_440,c_1565])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2465,plain,(
    k3_xboole_0('#skF_23',k4_xboole_0('#skF_22','#skF_21')) = k4_xboole_0('#skF_22','#skF_21') ),
    inference(superposition,[status(thm),theory(equality)],[c_1602,c_8])).

tff(c_442,plain,(
    r1_tarski(k4_xboole_0('#skF_21','#skF_22'),'#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_706])).

tff(c_290,plain,(
    ! [A_187,B_188] : k2_xboole_0(A_187,k4_xboole_0(B_188,A_187)) = k2_xboole_0(A_187,B_188) ),
    inference(cnfTransformation,[status(thm)],[f_406])).

tff(c_306,plain,(
    ! [A_205,B_206] :
      ( k2_xboole_0(A_205,k4_xboole_0(B_206,A_205)) = B_206
      | ~ r1_tarski(A_205,B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_430])).

tff(c_2636,plain,(
    ! [A_472,B_473] :
      ( k2_xboole_0(A_472,B_473) = B_473
      | ~ r1_tarski(A_472,B_473) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_306])).

tff(c_2672,plain,(
    k2_xboole_0(k4_xboole_0('#skF_21','#skF_22'),'#skF_23') = '#skF_23' ),
    inference(resolution,[status(thm)],[c_442,c_2636])).

tff(c_53991,plain,(
    ! [A_1386,B_1387,C_1388] : k3_xboole_0(k2_xboole_0(A_1386,B_1387),k2_xboole_0(A_1386,C_1388)) = k2_xboole_0(A_1386,k3_xboole_0(B_1387,C_1388)) ),
    inference(cnfTransformation,[status(thm)],[f_348])).

tff(c_232,plain,(
    ! [A_120,B_121] : r1_tarski(k3_xboole_0(A_120,B_121),A_120) ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_172054,plain,(
    ! [A_2330,B_2331,C_2332] : r1_tarski(k2_xboole_0(A_2330,k3_xboole_0(B_2331,C_2332)),k2_xboole_0(A_2330,B_2331)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53991,c_232])).

tff(c_172633,plain,(
    ! [C_2335] : r1_tarski(k2_xboole_0(k4_xboole_0('#skF_21','#skF_22'),k3_xboole_0('#skF_23',C_2335)),'#skF_23') ),
    inference(superposition,[status(thm),theory(equality)],[c_2672,c_172054])).

tff(c_172724,plain,(
    r1_tarski(k2_xboole_0(k4_xboole_0('#skF_21','#skF_22'),k4_xboole_0('#skF_22','#skF_21')),'#skF_23') ),
    inference(superposition,[status(thm),theory(equality)],[c_2465,c_172633])).

tff(c_172819,plain,(
    r1_tarski(k5_xboole_0('#skF_22','#skF_21'),'#skF_23') ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_6,c_172724])).

tff(c_172821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_172819])).
%------------------------------------------------------------------------------
