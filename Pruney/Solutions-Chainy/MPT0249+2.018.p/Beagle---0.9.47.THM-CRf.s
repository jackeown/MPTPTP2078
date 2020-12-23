%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:26 EST 2020

% Result     : Theorem 8.80s
% Output     : CNFRefutation 9.03s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 647 expanded)
%              Number of leaves         :   44 ( 240 expanded)
%              Depth                    :   19
%              Number of atoms          :  124 ( 984 expanded)
%              Number of equality atoms :   77 ( 787 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_64,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_70,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_124,plain,(
    '#skF_11' != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_187,plain,(
    ! [B_147,A_148] : k5_xboole_0(B_147,A_148) = k5_xboole_0(A_148,B_147) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_203,plain,(
    ! [A_148] : k5_xboole_0(k1_xboole_0,A_148) = A_148 ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_40])).

tff(c_46,plain,(
    ! [A_31] : k5_xboole_0(A_31,A_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2644,plain,(
    ! [A_247,B_248,C_249] : k5_xboole_0(k5_xboole_0(A_247,B_248),C_249) = k5_xboole_0(A_247,k5_xboole_0(B_248,C_249)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2708,plain,(
    ! [A_31,C_249] : k5_xboole_0(A_31,k5_xboole_0(A_31,C_249)) = k5_xboole_0(k1_xboole_0,C_249) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2644])).

tff(c_2775,plain,(
    ! [A_251,C_252] : k5_xboole_0(A_251,k5_xboole_0(A_251,C_252)) = C_252 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_2708])).

tff(c_2818,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2775])).

tff(c_122,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_637,plain,(
    ! [B_189,A_190] :
      ( k3_xboole_0(B_189,k1_tarski(A_190)) = k1_tarski(A_190)
      | ~ r2_hidden(A_190,B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_748,plain,(
    ! [B_195,A_196] :
      ( k2_xboole_0(B_195,k1_tarski(A_196)) = B_195
      | ~ r2_hidden(A_196,B_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_36])).

tff(c_126,plain,(
    k2_xboole_0('#skF_11','#skF_12') = k1_tarski('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_438,plain,(
    ! [A_176,B_177] : k2_xboole_0(A_176,k2_xboole_0(A_176,B_177)) = k2_xboole_0(A_176,B_177) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_465,plain,(
    k2_xboole_0('#skF_11',k1_tarski('#skF_10')) = k2_xboole_0('#skF_11','#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_438])).

tff(c_476,plain,(
    k2_xboole_0('#skF_11',k1_tarski('#skF_10')) = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_465])).

tff(c_754,plain,
    ( k1_tarski('#skF_10') = '#skF_11'
    | ~ r2_hidden('#skF_10','#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_476])).

tff(c_784,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_754])).

tff(c_26,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1133,plain,(
    ! [A_210,B_211,C_212] : k5_xboole_0(k5_xboole_0(A_210,B_211),C_212) = k5_xboole_0(A_210,k5_xboole_0(B_211,C_212)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1224,plain,(
    ! [A_31,C_212] : k5_xboole_0(A_31,k5_xboole_0(A_31,C_212)) = k5_xboole_0(k1_xboole_0,C_212) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1133])).

tff(c_1238,plain,(
    ! [A_31,C_212] : k5_xboole_0(A_31,k5_xboole_0(A_31,C_212)) = C_212 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_1224])).

tff(c_1239,plain,(
    ! [A_213,C_214] : k5_xboole_0(A_213,k5_xboole_0(A_213,C_214)) = C_214 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_1224])).

tff(c_1316,plain,(
    ! [A_215,B_216] : k5_xboole_0(A_215,k5_xboole_0(B_216,A_215)) = B_216 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1239])).

tff(c_1352,plain,(
    ! [A_31,C_212] : k5_xboole_0(k5_xboole_0(A_31,C_212),C_212) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_1238,c_1316])).

tff(c_802,plain,(
    ! [A_203,B_204] : k5_xboole_0(k5_xboole_0(A_203,B_204),k2_xboole_0(A_203,B_204)) = k3_xboole_0(A_203,B_204) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_835,plain,(
    k5_xboole_0(k5_xboole_0('#skF_11',k1_tarski('#skF_10')),k1_tarski('#skF_10')) = k3_xboole_0('#skF_11',k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_802])).

tff(c_2333,plain,(
    k3_xboole_0('#skF_11',k1_tarski('#skF_10')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1352,c_835])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2454,plain,(
    ! [D_242] :
      ( r2_hidden(D_242,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_242,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2333,c_6])).

tff(c_50,plain,(
    ! [C_38,A_34] :
      ( C_38 = A_34
      | ~ r2_hidden(C_38,k1_tarski(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2463,plain,(
    ! [D_243] :
      ( D_243 = '#skF_10'
      | ~ r2_hidden(D_243,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_2454,c_50])).

tff(c_2471,plain,
    ( '#skF_3'('#skF_11') = '#skF_10'
    | k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_26,c_2463])).

tff(c_2475,plain,(
    '#skF_3'('#skF_11') = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_2471])).

tff(c_2479,plain,
    ( r2_hidden('#skF_10','#skF_11')
    | k1_xboole_0 = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_2475,c_26])).

tff(c_2483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_784,c_2479])).

tff(c_2484,plain,(
    k1_tarski('#skF_10') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_754])).

tff(c_2545,plain,(
    k2_xboole_0('#skF_11','#skF_12') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2484,c_126])).

tff(c_3190,plain,(
    ! [A_265,B_266] : k5_xboole_0(k5_xboole_0(A_265,B_266),k2_xboole_0(A_265,B_266)) = k3_xboole_0(A_265,B_266) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3248,plain,(
    k5_xboole_0(k5_xboole_0('#skF_11','#skF_12'),'#skF_11') = k3_xboole_0('#skF_11','#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_2545,c_3190])).

tff(c_3296,plain,(
    k3_xboole_0('#skF_11','#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2818,c_2,c_2,c_3248])).

tff(c_2485,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_754])).

tff(c_6922,plain,(
    ! [A_378,B_379,C_380] :
      ( r2_hidden('#skF_1'(A_378,B_379,C_380),A_378)
      | r2_hidden('#skF_2'(A_378,B_379,C_380),C_380)
      | k3_xboole_0(A_378,B_379) = C_380 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11918,plain,(
    ! [A_532,B_533] :
      ( r2_hidden('#skF_2'(A_532,B_533,A_532),A_532)
      | k3_xboole_0(A_532,B_533) = A_532 ) ),
    inference(resolution,[status(thm)],[c_6922,c_16])).

tff(c_2577,plain,(
    ! [C_38] :
      ( C_38 = '#skF_10'
      | ~ r2_hidden(C_38,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2484,c_50])).

tff(c_12023,plain,(
    ! [B_534] :
      ( '#skF_2'('#skF_11',B_534,'#skF_11') = '#skF_10'
      | k3_xboole_0('#skF_11',B_534) = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_11918,c_2577])).

tff(c_12065,plain,
    ( '#skF_11' = '#skF_12'
    | '#skF_2'('#skF_11','#skF_12','#skF_11') = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_12023,c_3296])).

tff(c_12128,plain,(
    '#skF_2'('#skF_11','#skF_12','#skF_11') = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_12065])).

tff(c_120,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3489,plain,(
    ! [D_271] :
      ( r2_hidden(D_271,'#skF_11')
      | ~ r2_hidden(D_271,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3296,c_8])).

tff(c_3510,plain,(
    ! [D_272] :
      ( D_272 = '#skF_10'
      | ~ r2_hidden(D_272,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_3489,c_2577])).

tff(c_3514,plain,
    ( '#skF_3'('#skF_12') = '#skF_10'
    | k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_26,c_3510])).

tff(c_3517,plain,(
    '#skF_3'('#skF_12') = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_3514])).

tff(c_3521,plain,
    ( r2_hidden('#skF_10','#skF_12')
    | k1_xboole_0 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_3517,c_26])).

tff(c_3524,plain,(
    r2_hidden('#skF_10','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_3521])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12144,plain,
    ( r2_hidden('#skF_1'('#skF_11','#skF_12','#skF_11'),'#skF_11')
    | ~ r2_hidden('#skF_10','#skF_12')
    | ~ r2_hidden('#skF_2'('#skF_11','#skF_12','#skF_11'),'#skF_11')
    | k3_xboole_0('#skF_11','#skF_12') = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_12128,c_14])).

tff(c_12155,plain,
    ( r2_hidden('#skF_1'('#skF_11','#skF_12','#skF_11'),'#skF_11')
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3296,c_2485,c_12128,c_3524,c_12144])).

tff(c_12156,plain,(
    r2_hidden('#skF_1'('#skF_11','#skF_12','#skF_11'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_12155])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12163,plain,
    ( ~ r2_hidden('#skF_2'('#skF_11','#skF_12','#skF_11'),'#skF_12')
    | ~ r2_hidden('#skF_2'('#skF_11','#skF_12','#skF_11'),'#skF_11')
    | k3_xboole_0('#skF_11','#skF_12') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_12156,c_10])).

tff(c_12177,plain,(
    '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3296,c_2485,c_12128,c_3524,c_12128,c_12163])).

tff(c_12179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_12177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:39:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.80/3.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.03/3.02  
% 9.03/3.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.03/3.02  %$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5 > #skF_12 > #skF_4
% 9.03/3.02  
% 9.03/3.02  %Foreground sorts:
% 9.03/3.02  
% 9.03/3.02  
% 9.03/3.02  %Background operators:
% 9.03/3.02  
% 9.03/3.02  
% 9.03/3.02  %Foreground operators:
% 9.03/3.02  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 9.03/3.02  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.03/3.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.03/3.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.03/3.02  tff('#skF_11', type, '#skF_11': $i).
% 9.03/3.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.03/3.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.03/3.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.03/3.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.03/3.02  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.03/3.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.03/3.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.03/3.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.03/3.02  tff('#skF_10', type, '#skF_10': $i).
% 9.03/3.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.03/3.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.03/3.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.03/3.02  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 9.03/3.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.03/3.02  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 9.03/3.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.03/3.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.03/3.02  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.03/3.02  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.03/3.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.03/3.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.03/3.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.03/3.02  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 9.03/3.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.03/3.02  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.03/3.02  tff('#skF_12', type, '#skF_12': $i).
% 9.03/3.02  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.03/3.02  
% 9.03/3.03  tff(f_145, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 9.03/3.03  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.03/3.03  tff(f_64, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 9.03/3.03  tff(f_70, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.03/3.03  tff(f_68, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.03/3.03  tff(f_119, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 9.03/3.03  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 9.03/3.03  tff(f_66, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 9.03/3.03  tff(f_48, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.03/3.03  tff(f_72, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 9.03/3.03  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.03/3.03  tff(f_79, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 9.03/3.03  tff(c_124, plain, ('#skF_11'!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.03/3.03  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.03/3.03  tff(c_187, plain, (![B_147, A_148]: (k5_xboole_0(B_147, A_148)=k5_xboole_0(A_148, B_147))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.03/3.03  tff(c_40, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.03/3.03  tff(c_203, plain, (![A_148]: (k5_xboole_0(k1_xboole_0, A_148)=A_148)), inference(superposition, [status(thm), theory('equality')], [c_187, c_40])).
% 9.03/3.03  tff(c_46, plain, (![A_31]: (k5_xboole_0(A_31, A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.03/3.03  tff(c_2644, plain, (![A_247, B_248, C_249]: (k5_xboole_0(k5_xboole_0(A_247, B_248), C_249)=k5_xboole_0(A_247, k5_xboole_0(B_248, C_249)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.03/3.03  tff(c_2708, plain, (![A_31, C_249]: (k5_xboole_0(A_31, k5_xboole_0(A_31, C_249))=k5_xboole_0(k1_xboole_0, C_249))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2644])).
% 9.03/3.03  tff(c_2775, plain, (![A_251, C_252]: (k5_xboole_0(A_251, k5_xboole_0(A_251, C_252))=C_252)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_2708])).
% 9.03/3.03  tff(c_2818, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2775])).
% 9.03/3.03  tff(c_122, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.03/3.03  tff(c_637, plain, (![B_189, A_190]: (k3_xboole_0(B_189, k1_tarski(A_190))=k1_tarski(A_190) | ~r2_hidden(A_190, B_189))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.03/3.03  tff(c_36, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k3_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.03/3.03  tff(c_748, plain, (![B_195, A_196]: (k2_xboole_0(B_195, k1_tarski(A_196))=B_195 | ~r2_hidden(A_196, B_195))), inference(superposition, [status(thm), theory('equality')], [c_637, c_36])).
% 9.03/3.03  tff(c_126, plain, (k2_xboole_0('#skF_11', '#skF_12')=k1_tarski('#skF_10')), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.03/3.03  tff(c_438, plain, (![A_176, B_177]: (k2_xboole_0(A_176, k2_xboole_0(A_176, B_177))=k2_xboole_0(A_176, B_177))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.03/3.03  tff(c_465, plain, (k2_xboole_0('#skF_11', k1_tarski('#skF_10'))=k2_xboole_0('#skF_11', '#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_126, c_438])).
% 9.03/3.03  tff(c_476, plain, (k2_xboole_0('#skF_11', k1_tarski('#skF_10'))=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_465])).
% 9.03/3.03  tff(c_754, plain, (k1_tarski('#skF_10')='#skF_11' | ~r2_hidden('#skF_10', '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_748, c_476])).
% 9.03/3.03  tff(c_784, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(splitLeft, [status(thm)], [c_754])).
% 9.03/3.03  tff(c_26, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.03/3.03  tff(c_1133, plain, (![A_210, B_211, C_212]: (k5_xboole_0(k5_xboole_0(A_210, B_211), C_212)=k5_xboole_0(A_210, k5_xboole_0(B_211, C_212)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.03/3.03  tff(c_1224, plain, (![A_31, C_212]: (k5_xboole_0(A_31, k5_xboole_0(A_31, C_212))=k5_xboole_0(k1_xboole_0, C_212))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1133])).
% 9.03/3.03  tff(c_1238, plain, (![A_31, C_212]: (k5_xboole_0(A_31, k5_xboole_0(A_31, C_212))=C_212)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_1224])).
% 9.03/3.03  tff(c_1239, plain, (![A_213, C_214]: (k5_xboole_0(A_213, k5_xboole_0(A_213, C_214))=C_214)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_1224])).
% 9.03/3.03  tff(c_1316, plain, (![A_215, B_216]: (k5_xboole_0(A_215, k5_xboole_0(B_216, A_215))=B_216)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1239])).
% 9.03/3.03  tff(c_1352, plain, (![A_31, C_212]: (k5_xboole_0(k5_xboole_0(A_31, C_212), C_212)=A_31)), inference(superposition, [status(thm), theory('equality')], [c_1238, c_1316])).
% 9.03/3.03  tff(c_802, plain, (![A_203, B_204]: (k5_xboole_0(k5_xboole_0(A_203, B_204), k2_xboole_0(A_203, B_204))=k3_xboole_0(A_203, B_204))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.03/3.03  tff(c_835, plain, (k5_xboole_0(k5_xboole_0('#skF_11', k1_tarski('#skF_10')), k1_tarski('#skF_10'))=k3_xboole_0('#skF_11', k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_476, c_802])).
% 9.03/3.03  tff(c_2333, plain, (k3_xboole_0('#skF_11', k1_tarski('#skF_10'))='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_1352, c_835])).
% 9.03/3.03  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.03/3.03  tff(c_2454, plain, (![D_242]: (r2_hidden(D_242, k1_tarski('#skF_10')) | ~r2_hidden(D_242, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_2333, c_6])).
% 9.03/3.03  tff(c_50, plain, (![C_38, A_34]: (C_38=A_34 | ~r2_hidden(C_38, k1_tarski(A_34)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.03/3.03  tff(c_2463, plain, (![D_243]: (D_243='#skF_10' | ~r2_hidden(D_243, '#skF_11'))), inference(resolution, [status(thm)], [c_2454, c_50])).
% 9.03/3.03  tff(c_2471, plain, ('#skF_3'('#skF_11')='#skF_10' | k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_26, c_2463])).
% 9.03/3.03  tff(c_2475, plain, ('#skF_3'('#skF_11')='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_122, c_2471])).
% 9.03/3.03  tff(c_2479, plain, (r2_hidden('#skF_10', '#skF_11') | k1_xboole_0='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_2475, c_26])).
% 9.03/3.03  tff(c_2483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_784, c_2479])).
% 9.03/3.03  tff(c_2484, plain, (k1_tarski('#skF_10')='#skF_11'), inference(splitRight, [status(thm)], [c_754])).
% 9.03/3.03  tff(c_2545, plain, (k2_xboole_0('#skF_11', '#skF_12')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_2484, c_126])).
% 9.03/3.03  tff(c_3190, plain, (![A_265, B_266]: (k5_xboole_0(k5_xboole_0(A_265, B_266), k2_xboole_0(A_265, B_266))=k3_xboole_0(A_265, B_266))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.03/3.03  tff(c_3248, plain, (k5_xboole_0(k5_xboole_0('#skF_11', '#skF_12'), '#skF_11')=k3_xboole_0('#skF_11', '#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_2545, c_3190])).
% 9.03/3.03  tff(c_3296, plain, (k3_xboole_0('#skF_11', '#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2818, c_2, c_2, c_3248])).
% 9.03/3.03  tff(c_2485, plain, (r2_hidden('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_754])).
% 9.03/3.03  tff(c_6922, plain, (![A_378, B_379, C_380]: (r2_hidden('#skF_1'(A_378, B_379, C_380), A_378) | r2_hidden('#skF_2'(A_378, B_379, C_380), C_380) | k3_xboole_0(A_378, B_379)=C_380)), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.03/3.03  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.03/3.03  tff(c_11918, plain, (![A_532, B_533]: (r2_hidden('#skF_2'(A_532, B_533, A_532), A_532) | k3_xboole_0(A_532, B_533)=A_532)), inference(resolution, [status(thm)], [c_6922, c_16])).
% 9.03/3.03  tff(c_2577, plain, (![C_38]: (C_38='#skF_10' | ~r2_hidden(C_38, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_2484, c_50])).
% 9.03/3.03  tff(c_12023, plain, (![B_534]: ('#skF_2'('#skF_11', B_534, '#skF_11')='#skF_10' | k3_xboole_0('#skF_11', B_534)='#skF_11')), inference(resolution, [status(thm)], [c_11918, c_2577])).
% 9.03/3.03  tff(c_12065, plain, ('#skF_11'='#skF_12' | '#skF_2'('#skF_11', '#skF_12', '#skF_11')='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_12023, c_3296])).
% 9.03/3.03  tff(c_12128, plain, ('#skF_2'('#skF_11', '#skF_12', '#skF_11')='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_124, c_12065])).
% 9.03/3.03  tff(c_120, plain, (k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.03/3.03  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.03/3.03  tff(c_3489, plain, (![D_271]: (r2_hidden(D_271, '#skF_11') | ~r2_hidden(D_271, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_3296, c_8])).
% 9.03/3.03  tff(c_3510, plain, (![D_272]: (D_272='#skF_10' | ~r2_hidden(D_272, '#skF_12'))), inference(resolution, [status(thm)], [c_3489, c_2577])).
% 9.03/3.03  tff(c_3514, plain, ('#skF_3'('#skF_12')='#skF_10' | k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_26, c_3510])).
% 9.03/3.03  tff(c_3517, plain, ('#skF_3'('#skF_12')='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_120, c_3514])).
% 9.03/3.03  tff(c_3521, plain, (r2_hidden('#skF_10', '#skF_12') | k1_xboole_0='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_3517, c_26])).
% 9.03/3.03  tff(c_3524, plain, (r2_hidden('#skF_10', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_120, c_3521])).
% 9.03/3.03  tff(c_14, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.03/3.03  tff(c_12144, plain, (r2_hidden('#skF_1'('#skF_11', '#skF_12', '#skF_11'), '#skF_11') | ~r2_hidden('#skF_10', '#skF_12') | ~r2_hidden('#skF_2'('#skF_11', '#skF_12', '#skF_11'), '#skF_11') | k3_xboole_0('#skF_11', '#skF_12')='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_12128, c_14])).
% 9.03/3.03  tff(c_12155, plain, (r2_hidden('#skF_1'('#skF_11', '#skF_12', '#skF_11'), '#skF_11') | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3296, c_2485, c_12128, c_3524, c_12144])).
% 9.03/3.03  tff(c_12156, plain, (r2_hidden('#skF_1'('#skF_11', '#skF_12', '#skF_11'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_124, c_12155])).
% 9.03/3.03  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.03/3.03  tff(c_12163, plain, (~r2_hidden('#skF_2'('#skF_11', '#skF_12', '#skF_11'), '#skF_12') | ~r2_hidden('#skF_2'('#skF_11', '#skF_12', '#skF_11'), '#skF_11') | k3_xboole_0('#skF_11', '#skF_12')='#skF_11'), inference(resolution, [status(thm)], [c_12156, c_10])).
% 9.03/3.03  tff(c_12177, plain, ('#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3296, c_2485, c_12128, c_3524, c_12128, c_12163])).
% 9.03/3.03  tff(c_12179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_12177])).
% 9.03/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.03/3.03  
% 9.03/3.03  Inference rules
% 9.03/3.03  ----------------------
% 9.03/3.03  #Ref     : 0
% 9.03/3.03  #Sup     : 2923
% 9.03/3.03  #Fact    : 0
% 9.03/3.03  #Define  : 0
% 9.03/3.03  #Split   : 8
% 9.03/3.03  #Chain   : 0
% 9.03/3.03  #Close   : 0
% 9.03/3.03  
% 9.03/3.03  Ordering : KBO
% 9.03/3.03  
% 9.03/3.03  Simplification rules
% 9.03/3.03  ----------------------
% 9.03/3.03  #Subsume      : 343
% 9.03/3.03  #Demod        : 2274
% 9.03/3.03  #Tautology    : 1616
% 9.03/3.03  #SimpNegUnit  : 181
% 9.03/3.03  #BackRed      : 45
% 9.03/3.03  
% 9.03/3.03  #Partial instantiations: 0
% 9.03/3.03  #Strategies tried      : 1
% 9.03/3.03  
% 9.03/3.03  Timing (in seconds)
% 9.03/3.03  ----------------------
% 9.03/3.04  Preprocessing        : 0.41
% 9.03/3.04  Parsing              : 0.21
% 9.03/3.04  CNF conversion       : 0.03
% 9.03/3.04  Main loop            : 1.84
% 9.03/3.04  Inferencing          : 0.51
% 9.03/3.04  Reduction            : 0.82
% 9.03/3.04  Demodulation         : 0.66
% 9.03/3.04  BG Simplification    : 0.07
% 9.03/3.04  Subsumption          : 0.33
% 9.03/3.04  Abstraction          : 0.08
% 9.03/3.04  MUC search           : 0.00
% 9.03/3.04  Cooper               : 0.00
% 9.03/3.04  Total                : 2.29
% 9.03/3.04  Index Insertion      : 0.00
% 9.03/3.04  Index Deletion       : 0.00
% 9.03/3.04  Index Matching       : 0.00
% 9.03/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
