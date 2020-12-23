%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:20 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :  275 ( 827 expanded)
%              Number of leaves         :   33 ( 255 expanded)
%              Depth                    :   11
%              Number of atoms          :  344 (1668 expanded)
%              Number of equality atoms :  278 (1533 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_26,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10791,plain,(
    ! [A_386,B_387] : k5_xboole_0(A_386,k3_xboole_0(A_386,B_387)) = k4_xboole_0(A_386,B_387) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10826,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_10791])).

tff(c_10838,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10826])).

tff(c_8931,plain,(
    ! [A_309,B_310] : k5_xboole_0(A_309,k3_xboole_0(A_309,B_310)) = k4_xboole_0(A_309,B_310) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8966,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8931])).

tff(c_8978,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8966])).

tff(c_62,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_146,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_58,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_369,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_255,plain,(
    k1_tarski('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_510,plain,(
    k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_148,plain,(
    ! [B_47,A_48] : k5_xboole_0(B_47,A_48) = k5_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_164,plain,(
    ! [A_48] : k5_xboole_0(k1_xboole_0,A_48) = A_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_20])).

tff(c_4820,plain,(
    ! [A_185,B_186,C_187] : k5_xboole_0(k5_xboole_0(A_185,B_186),C_187) = k5_xboole_0(A_185,k5_xboole_0(B_186,C_187)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4897,plain,(
    ! [A_21,C_187] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_187)) = k5_xboole_0(k1_xboole_0,C_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4820])).

tff(c_4911,plain,(
    ! [A_188,C_189] : k5_xboole_0(A_188,k5_xboole_0(A_188,C_189)) = C_189 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_4897])).

tff(c_4982,plain,(
    ! [A_190,B_191] : k5_xboole_0(A_190,k5_xboole_0(B_191,A_190)) = B_191 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4911])).

tff(c_4960,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4911])).

tff(c_4985,plain,(
    ! [B_191,A_190] : k5_xboole_0(k5_xboole_0(B_191,A_190),B_191) = A_190 ),
    inference(superposition,[status(thm),theory(equality)],[c_4982,c_4960])).

tff(c_371,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_397,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_371])).

tff(c_406,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_397])).

tff(c_1122,plain,(
    ! [A_116,B_117,C_118] : k5_xboole_0(k5_xboole_0(A_116,B_117),C_118) = k5_xboole_0(A_116,k5_xboole_0(B_117,C_118)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1212,plain,(
    ! [A_21,C_118] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_118)) = k5_xboole_0(k1_xboole_0,C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1122])).

tff(c_1226,plain,(
    ! [A_119,C_120] : k5_xboole_0(A_119,k5_xboole_0(A_119,C_120)) = C_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_1212])).

tff(c_1305,plain,(
    ! [A_121,B_122] : k5_xboole_0(A_121,k5_xboole_0(B_122,A_121)) = B_122 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1226])).

tff(c_1281,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1226])).

tff(c_1308,plain,(
    ! [B_122,A_121] : k5_xboole_0(k5_xboole_0(B_122,A_121),B_122) = A_121 ),
    inference(superposition,[status(thm),theory(equality)],[c_1305,c_1281])).

tff(c_68,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1741,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1271,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1226])).

tff(c_1745,plain,(
    k3_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1741,c_1271])).

tff(c_1748,plain,(
    k3_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1745])).

tff(c_28,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k3_xboole_0(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1753,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')),'#skF_4') = k2_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1748,c_28])).

tff(c_1759,plain,(
    k2_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1308,c_1753])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3047,plain,(
    r1_tarski('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1759,c_22])).

tff(c_36,plain,(
    ! [B_30,C_31,A_29] :
      ( k2_tarski(B_30,C_31) = A_29
      | k1_tarski(C_31) = A_29
      | k1_tarski(B_30) = A_29
      | k1_xboole_0 = A_29
      | ~ r1_tarski(A_29,k2_tarski(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3058,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3047,c_36])).

tff(c_3070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_369,c_255,c_510,c_3058])).

tff(c_3071,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_3354,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3071])).

tff(c_66,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_667,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_3355,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3354,c_667])).

tff(c_3358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_3355])).

tff(c_3359,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3071])).

tff(c_3361,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3359])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_558,plain,(
    ! [A_86,B_87] : k5_xboole_0(k5_xboole_0(A_86,B_87),k3_xboole_0(A_86,B_87)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_612,plain,(
    ! [A_15] : k5_xboole_0(A_15,k3_xboole_0(A_15,k1_xboole_0)) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_558])).

tff(c_627,plain,(
    ! [A_88] : k2_xboole_0(A_88,k1_xboole_0) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_612])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,k2_xboole_0(C_11,B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_662,plain,(
    ! [A_89,A_90] :
      ( r1_tarski(A_89,A_90)
      | ~ r1_tarski(A_89,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_14])).

tff(c_670,plain,(
    ! [A_91] : r1_tarski(k1_xboole_0,A_91) ),
    inference(resolution,[status(thm)],[c_10,c_662])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_682,plain,(
    ! [A_91] : k3_xboole_0(k1_xboole_0,A_91) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_670,c_16])).

tff(c_394,plain,(
    ! [B_70] : k4_xboole_0(k1_xboole_0,B_70) = k3_xboole_0(k1_xboole_0,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_371])).

tff(c_683,plain,(
    ! [B_70] : k4_xboole_0(k1_xboole_0,B_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_394])).

tff(c_3372,plain,(
    ! [B_70] : k4_xboole_0('#skF_1',B_70) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3361,c_3361,c_683])).

tff(c_3370,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3361,c_667])).

tff(c_3878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3372,c_3370])).

tff(c_3879,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3359])).

tff(c_3881,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3879])).

tff(c_40,plain,(
    ! [C_31,B_30] : r1_tarski(k1_tarski(C_31),k2_tarski(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_256,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_823,plain,(
    ! [C_96,B_97] : k3_xboole_0(k1_tarski(C_96),k2_tarski(B_97,C_96)) = k1_tarski(C_96) ),
    inference(resolution,[status(thm)],[c_40,c_256])).

tff(c_836,plain,(
    ! [C_96,B_97] : k5_xboole_0(k1_tarski(C_96),k1_tarski(C_96)) = k4_xboole_0(k1_tarski(C_96),k2_tarski(B_97,C_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_823,c_12])).

tff(c_849,plain,(
    ! [C_96,B_97] : k4_xboole_0(k1_tarski(C_96),k2_tarski(B_97,C_96)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_836])).

tff(c_3885,plain,(
    ! [B_97] : k4_xboole_0('#skF_1',k2_tarski(B_97,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3881,c_849])).

tff(c_4447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3885,c_667])).

tff(c_4448,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3879])).

tff(c_42,plain,(
    ! [B_30,C_31] : r1_tarski(k1_tarski(B_30),k2_tarski(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_275,plain,(
    ! [B_30,C_31] : k3_xboole_0(k1_tarski(B_30),k2_tarski(B_30,C_31)) = k1_tarski(B_30) ),
    inference(resolution,[status(thm)],[c_42,c_256])).

tff(c_4462,plain,(
    ! [C_31] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_31)) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4448,c_275])).

tff(c_4527,plain,(
    ! [C_175] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_175)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4448,c_4462])).

tff(c_4544,plain,(
    ! [C_175] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_175)) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4527,c_12])).

tff(c_4554,plain,(
    ! [C_175] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_175)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4544])).

tff(c_4624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4554,c_667])).

tff(c_4625,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5421,plain,(
    ! [A_200,B_201] : k5_xboole_0(A_200,k4_xboole_0(A_200,B_201)) = k3_xboole_0(A_200,B_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4911])).

tff(c_5466,plain,(
    k3_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4625,c_5421])).

tff(c_5494,plain,(
    k3_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5466])).

tff(c_5505,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')),'#skF_4') = k2_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5494,c_28])).

tff(c_5511,plain,(
    k2_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4985,c_5505])).

tff(c_6092,plain,(
    r1_tarski('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5511,c_22])).

tff(c_6101,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6092,c_36])).

tff(c_6110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_369,c_255,c_510,c_6101])).

tff(c_6111,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6112,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6581,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6112,c_52])).

tff(c_6582,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6581])).

tff(c_6607,plain,(
    ! [A_15] : k5_xboole_0(A_15,'#skF_1') = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6582,c_20])).

tff(c_6420,plain,(
    ! [A_229,B_230] : k5_xboole_0(k5_xboole_0(A_229,B_230),k3_xboole_0(A_229,B_230)) = k2_xboole_0(A_229,B_230) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6495,plain,(
    ! [A_15] : k5_xboole_0(A_15,k3_xboole_0(A_15,k1_xboole_0)) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6420])).

tff(c_6518,plain,(
    ! [A_231] : k2_xboole_0(A_231,k1_xboole_0) = A_231 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_6495])).

tff(c_6530,plain,(
    ! [A_9,A_231] :
      ( r1_tarski(A_9,A_231)
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6518,c_14])).

tff(c_7195,plain,(
    ! [A_255,A_256] :
      ( r1_tarski(A_255,A_256)
      | ~ r1_tarski(A_255,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6582,c_6530])).

tff(c_7237,plain,(
    ! [A_259] : r1_tarski('#skF_1',A_259) ),
    inference(resolution,[status(thm)],[c_10,c_7195])).

tff(c_7267,plain,(
    ! [A_260] : k3_xboole_0('#skF_1',A_260) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_7237,c_16])).

tff(c_7278,plain,(
    ! [A_260] : k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1',A_260) ),
    inference(superposition,[status(thm),theory(equality)],[c_7267,c_12])).

tff(c_7303,plain,(
    ! [A_260] : k4_xboole_0('#skF_1',A_260) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6607,c_7278])).

tff(c_6113,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_6592,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6582,c_6113])).

tff(c_7408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7303,c_6592])).

tff(c_7409,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6581])).

tff(c_7856,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7409])).

tff(c_7857,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7856,c_6113])).

tff(c_7860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_7857])).

tff(c_7861,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7409])).

tff(c_7863,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7861])).

tff(c_6384,plain,(
    ! [B_225,C_226] : k3_xboole_0(k1_tarski(B_225),k2_tarski(B_225,C_226)) = k1_tarski(B_225) ),
    inference(resolution,[status(thm)],[c_42,c_256])).

tff(c_6390,plain,(
    ! [B_225,C_226] : k5_xboole_0(k1_tarski(B_225),k1_tarski(B_225)) = k4_xboole_0(k1_tarski(B_225),k2_tarski(B_225,C_226)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6384,c_12])).

tff(c_6401,plain,(
    ! [B_225,C_226] : k4_xboole_0(k1_tarski(B_225),k2_tarski(B_225,C_226)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6390])).

tff(c_7867,plain,(
    ! [C_226] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_226)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7863,c_6401])).

tff(c_8272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7867,c_6113])).

tff(c_8273,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7861])).

tff(c_8349,plain,(
    ! [B_293] : r1_tarski('#skF_1',k2_tarski(B_293,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8273,c_40])).

tff(c_8419,plain,(
    ! [B_296] : k3_xboole_0('#skF_1',k2_tarski(B_296,'#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_8349,c_16])).

tff(c_8430,plain,(
    ! [B_296] : k4_xboole_0('#skF_1',k2_tarski(B_296,'#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8419,c_12])).

tff(c_8442,plain,(
    ! [B_296] : k4_xboole_0('#skF_1',k2_tarski(B_296,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8430])).

tff(c_8734,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8442,c_6113])).

tff(c_8736,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_8828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6111,c_8736])).

tff(c_8830,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_60,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_9489,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8830,c_60])).

tff(c_9490,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9489])).

tff(c_9128,plain,(
    ! [A_323,B_324] : k5_xboole_0(k5_xboole_0(A_323,B_324),k3_xboole_0(A_323,B_324)) = k2_xboole_0(A_323,B_324) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_9188,plain,(
    ! [A_15] : k5_xboole_0(A_15,k3_xboole_0(A_15,k1_xboole_0)) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_9128])).

tff(c_9204,plain,(
    ! [A_325] : k2_xboole_0(A_325,k1_xboole_0) = A_325 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_9188])).

tff(c_9258,plain,(
    ! [A_326,A_327] :
      ( r1_tarski(A_326,A_327)
      | ~ r1_tarski(A_326,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9204,c_14])).

tff(c_9266,plain,(
    ! [A_328] : r1_tarski(k1_xboole_0,A_328) ),
    inference(resolution,[status(thm)],[c_10,c_9258])).

tff(c_9278,plain,(
    ! [A_328] : k3_xboole_0(k1_xboole_0,A_328) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9266,c_16])).

tff(c_8963,plain,(
    ! [B_310] : k4_xboole_0(k1_xboole_0,B_310) = k3_xboole_0(k1_xboole_0,B_310) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_8931])).

tff(c_9279,plain,(
    ! [B_310] : k4_xboole_0(k1_xboole_0,B_310) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9278,c_8963])).

tff(c_9493,plain,(
    ! [B_310] : k4_xboole_0('#skF_1',B_310) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9490,c_9490,c_9279])).

tff(c_8829,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_9502,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9490,c_8829])).

tff(c_9776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9493,c_9502])).

tff(c_9777,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9489])).

tff(c_10311,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9777])).

tff(c_10312,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10311,c_8829])).

tff(c_10315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8978,c_10312])).

tff(c_10316,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9777])).

tff(c_10318,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10316])).

tff(c_10338,plain,(
    ! [C_356] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_356)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10318,c_42])).

tff(c_10364,plain,(
    ! [C_358] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_358)) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10338,c_16])).

tff(c_10372,plain,(
    ! [C_358] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_358)) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10364,c_12])).

tff(c_10381,plain,(
    ! [C_358] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_358)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10372])).

tff(c_10465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10381,c_8829])).

tff(c_10466,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10316])).

tff(c_10487,plain,(
    ! [B_363] : r1_tarski('#skF_1',k2_tarski(B_363,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10466,c_40])).

tff(c_10513,plain,(
    ! [B_365] : k3_xboole_0('#skF_1',k2_tarski(B_365,'#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10487,c_16])).

tff(c_10521,plain,(
    ! [B_365] : k4_xboole_0('#skF_1',k2_tarski(B_365,'#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10513,c_12])).

tff(c_10530,plain,(
    ! [B_365] : k4_xboole_0('#skF_1',k2_tarski(B_365,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10521])).

tff(c_10614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10530,c_8829])).

tff(c_10616,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_56,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_11504,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10616,c_56])).

tff(c_11505,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_11504])).

tff(c_11531,plain,(
    ! [A_15] : k5_xboole_0(A_15,'#skF_1') = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11505,c_20])).

tff(c_11330,plain,(
    ! [A_420,B_421] : k5_xboole_0(k5_xboole_0(A_420,B_421),k3_xboole_0(A_420,B_421)) = k2_xboole_0(A_420,B_421) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_11408,plain,(
    ! [A_15] : k5_xboole_0(A_15,k3_xboole_0(A_15,k1_xboole_0)) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_11330])).

tff(c_11432,plain,(
    ! [A_422] : k2_xboole_0(A_422,k1_xboole_0) = A_422 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_11408])).

tff(c_11445,plain,(
    ! [A_9,A_422] :
      ( r1_tarski(A_9,A_422)
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11432,c_14])).

tff(c_12065,plain,(
    ! [A_444,A_445] :
      ( r1_tarski(A_444,A_445)
      | ~ r1_tarski(A_444,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11505,c_11445])).

tff(c_12073,plain,(
    ! [A_446] : r1_tarski('#skF_1',A_446) ),
    inference(resolution,[status(thm)],[c_10,c_12065])).

tff(c_12129,plain,(
    ! [A_450] : k3_xboole_0('#skF_1',A_450) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12073,c_16])).

tff(c_12140,plain,(
    ! [A_450] : k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1',A_450) ),
    inference(superposition,[status(thm),theory(equality)],[c_12129,c_12])).

tff(c_12165,plain,(
    ! [A_450] : k4_xboole_0('#skF_1',A_450) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11531,c_12140])).

tff(c_10615,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_11525,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11505,c_10615])).

tff(c_12221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12165,c_11525])).

tff(c_12222,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11504])).

tff(c_12682,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12222])).

tff(c_12683,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12682,c_10615])).

tff(c_12686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10838,c_12683])).

tff(c_12687,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12222])).

tff(c_12689,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12687])).

tff(c_10649,plain,(
    ! [A_372,B_373] :
      ( k3_xboole_0(A_372,B_373) = A_372
      | ~ r1_tarski(A_372,B_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10680,plain,(
    ! [B_30,C_31] : k3_xboole_0(k1_tarski(B_30),k2_tarski(B_30,C_31)) = k1_tarski(B_30) ),
    inference(resolution,[status(thm)],[c_42,c_10649])).

tff(c_12709,plain,(
    ! [C_31] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_31)) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12689,c_10680])).

tff(c_12824,plain,(
    ! [C_473] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_473)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12689,c_12709])).

tff(c_12835,plain,(
    ! [C_473] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_473)) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12824,c_12])).

tff(c_12847,plain,(
    ! [C_473] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_473)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12835])).

tff(c_13098,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12847,c_10615])).

tff(c_13099,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12687])).

tff(c_10681,plain,(
    ! [C_31,B_30] : k3_xboole_0(k1_tarski(C_31),k2_tarski(B_30,C_31)) = k1_tarski(C_31) ),
    inference(resolution,[status(thm)],[c_40,c_10649])).

tff(c_13107,plain,(
    ! [B_30] : k3_xboole_0('#skF_1',k2_tarski(B_30,'#skF_3')) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13099,c_10681])).

tff(c_13185,plain,(
    ! [B_483] : k3_xboole_0('#skF_1',k2_tarski(B_483,'#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13099,c_13107])).

tff(c_13196,plain,(
    ! [B_483] : k4_xboole_0('#skF_1',k2_tarski(B_483,'#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13185,c_12])).

tff(c_13208,plain,(
    ! [B_483] : k4_xboole_0('#skF_1',k2_tarski(B_483,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_13196])).

tff(c_13509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13208,c_10615])).

tff(c_13511,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_13515,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13511,c_26])).

tff(c_13806,plain,(
    ! [A_523,B_524] : k5_xboole_0(A_523,k3_xboole_0(A_523,B_524)) = k4_xboole_0(A_523,B_524) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13835,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_13806])).

tff(c_13842,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13515,c_13835])).

tff(c_44,plain,(
    ! [B_30,C_31] : r1_tarski(k1_xboole_0,k2_tarski(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_13512,plain,(
    ! [B_30,C_31] : r1_tarski('#skF_4',k2_tarski(B_30,C_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13511,c_44])).

tff(c_13676,plain,(
    ! [A_505,B_506] :
      ( k3_xboole_0(A_505,B_506) = A_505
      | ~ r1_tarski(A_505,B_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13697,plain,(
    ! [B_30,C_31] : k3_xboole_0('#skF_4',k2_tarski(B_30,C_31)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13512,c_13676])).

tff(c_13582,plain,(
    ! [B_502,A_503] : k5_xboole_0(B_502,A_503) = k5_xboole_0(A_503,B_502) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_13513,plain,(
    ! [A_15] : k5_xboole_0(A_15,'#skF_4') = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13511,c_20])).

tff(c_13598,plain,(
    ! [A_503] : k5_xboole_0('#skF_4',A_503) = A_503 ),
    inference(superposition,[status(thm),theory(equality)],[c_13582,c_13513])).

tff(c_13829,plain,(
    ! [B_524] : k4_xboole_0('#skF_4',B_524) = k3_xboole_0('#skF_4',B_524) ),
    inference(superposition,[status(thm),theory(equality)],[c_13598,c_13806])).

tff(c_64,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14446,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13511,c_13511,c_64])).

tff(c_14447,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14446])).

tff(c_13510,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_13576,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13511,c_13510])).

tff(c_14448,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14447,c_13576])).

tff(c_14451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13697,c_13829,c_14448])).

tff(c_14452,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14446])).

tff(c_14475,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14452])).

tff(c_14476,plain,(
    k4_xboole_0('#skF_1','#skF_1') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14475,c_13576])).

tff(c_14479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13842,c_14476])).

tff(c_14480,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14452])).

tff(c_14576,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14480])).

tff(c_14607,plain,(
    ! [C_553] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_553)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14576,c_42])).

tff(c_14638,plain,(
    ! [C_555] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_555)) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14607,c_16])).

tff(c_14646,plain,(
    ! [C_555] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_555)) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14638,c_12])).

tff(c_14658,plain,(
    ! [C_555] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_555)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13515,c_14646])).

tff(c_14963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14658,c_13576])).

tff(c_14964,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14480])).

tff(c_14985,plain,(
    ! [B_562] : r1_tarski('#skF_1',k2_tarski(B_562,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14964,c_40])).

tff(c_15184,plain,(
    ! [B_568] : k3_xboole_0('#skF_1',k2_tarski(B_568,'#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14985,c_16])).

tff(c_15195,plain,(
    ! [B_568] : k4_xboole_0('#skF_1',k2_tarski(B_568,'#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15184,c_12])).

tff(c_15208,plain,(
    ! [B_568] : k4_xboole_0('#skF_1',k2_tarski(B_568,'#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13515,c_15195])).

tff(c_15354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15208,c_13576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.84/2.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.84/2.77  
% 7.84/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.84/2.77  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.84/2.77  
% 7.84/2.77  %Foreground sorts:
% 7.84/2.77  
% 7.84/2.77  
% 7.84/2.77  %Background operators:
% 7.84/2.77  
% 7.84/2.77  
% 7.84/2.77  %Foreground operators:
% 7.84/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.84/2.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.84/2.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.84/2.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.84/2.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.84/2.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.84/2.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.84/2.77  tff('#skF_5', type, '#skF_5': $i).
% 7.84/2.77  tff('#skF_6', type, '#skF_6': $i).
% 7.84/2.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.84/2.77  tff('#skF_2', type, '#skF_2': $i).
% 7.84/2.77  tff('#skF_3', type, '#skF_3': $i).
% 7.84/2.77  tff('#skF_1', type, '#skF_1': $i).
% 7.84/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.84/2.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.84/2.77  tff('#skF_4', type, '#skF_4': $i).
% 7.84/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.84/2.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.84/2.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.84/2.77  
% 8.08/2.80  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.08/2.80  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.08/2.80  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.08/2.80  tff(f_98, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 8.08/2.80  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.08/2.80  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.08/2.80  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.08/2.80  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.08/2.80  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.08/2.80  tff(f_78, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 8.08/2.80  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.08/2.80  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.08/2.80  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 8.08/2.80  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.08/2.80  tff(c_26, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.08/2.80  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.08/2.80  tff(c_10791, plain, (![A_386, B_387]: (k5_xboole_0(A_386, k3_xboole_0(A_386, B_387))=k4_xboole_0(A_386, B_387))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.08/2.80  tff(c_10826, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_10791])).
% 8.08/2.80  tff(c_10838, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10826])).
% 8.08/2.80  tff(c_8931, plain, (![A_309, B_310]: (k5_xboole_0(A_309, k3_xboole_0(A_309, B_310))=k4_xboole_0(A_309, B_310))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.08/2.80  tff(c_8966, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8931])).
% 8.08/2.80  tff(c_8978, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8966])).
% 8.08/2.80  tff(c_62, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.80  tff(c_146, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_62])).
% 8.08/2.80  tff(c_58, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.80  tff(c_369, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_58])).
% 8.08/2.80  tff(c_54, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.80  tff(c_255, plain, (k1_tarski('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_54])).
% 8.08/2.80  tff(c_50, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.80  tff(c_510, plain, (k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_50])).
% 8.08/2.80  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.08/2.80  tff(c_148, plain, (![B_47, A_48]: (k5_xboole_0(B_47, A_48)=k5_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.08/2.80  tff(c_20, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.08/2.80  tff(c_164, plain, (![A_48]: (k5_xboole_0(k1_xboole_0, A_48)=A_48)), inference(superposition, [status(thm), theory('equality')], [c_148, c_20])).
% 8.08/2.80  tff(c_4820, plain, (![A_185, B_186, C_187]: (k5_xboole_0(k5_xboole_0(A_185, B_186), C_187)=k5_xboole_0(A_185, k5_xboole_0(B_186, C_187)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.08/2.80  tff(c_4897, plain, (![A_21, C_187]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_187))=k5_xboole_0(k1_xboole_0, C_187))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4820])).
% 8.08/2.80  tff(c_4911, plain, (![A_188, C_189]: (k5_xboole_0(A_188, k5_xboole_0(A_188, C_189))=C_189)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_4897])).
% 8.08/2.80  tff(c_4982, plain, (![A_190, B_191]: (k5_xboole_0(A_190, k5_xboole_0(B_191, A_190))=B_191)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4911])).
% 8.08/2.80  tff(c_4960, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4911])).
% 8.08/2.80  tff(c_4985, plain, (![B_191, A_190]: (k5_xboole_0(k5_xboole_0(B_191, A_190), B_191)=A_190)), inference(superposition, [status(thm), theory('equality')], [c_4982, c_4960])).
% 8.08/2.80  tff(c_371, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.08/2.80  tff(c_397, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_371])).
% 8.08/2.80  tff(c_406, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_397])).
% 8.08/2.80  tff(c_1122, plain, (![A_116, B_117, C_118]: (k5_xboole_0(k5_xboole_0(A_116, B_117), C_118)=k5_xboole_0(A_116, k5_xboole_0(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.08/2.80  tff(c_1212, plain, (![A_21, C_118]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_118))=k5_xboole_0(k1_xboole_0, C_118))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1122])).
% 8.08/2.80  tff(c_1226, plain, (![A_119, C_120]: (k5_xboole_0(A_119, k5_xboole_0(A_119, C_120))=C_120)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_1212])).
% 8.08/2.80  tff(c_1305, plain, (![A_121, B_122]: (k5_xboole_0(A_121, k5_xboole_0(B_122, A_121))=B_122)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1226])).
% 8.08/2.80  tff(c_1281, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1226])).
% 8.08/2.80  tff(c_1308, plain, (![B_122, A_121]: (k5_xboole_0(k5_xboole_0(B_122, A_121), B_122)=A_121)), inference(superposition, [status(thm), theory('equality')], [c_1305, c_1281])).
% 8.08/2.80  tff(c_68, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.80  tff(c_1741, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_68])).
% 8.08/2.80  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.08/2.80  tff(c_1271, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1226])).
% 8.08/2.80  tff(c_1745, plain, (k3_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1741, c_1271])).
% 8.08/2.80  tff(c_1748, plain, (k3_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1745])).
% 8.08/2.80  tff(c_28, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k3_xboole_0(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.08/2.80  tff(c_1753, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6')), '#skF_4')=k2_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1748, c_28])).
% 8.08/2.80  tff(c_1759, plain, (k2_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1308, c_1753])).
% 8.08/2.80  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.08/2.80  tff(c_3047, plain, (r1_tarski('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1759, c_22])).
% 8.08/2.80  tff(c_36, plain, (![B_30, C_31, A_29]: (k2_tarski(B_30, C_31)=A_29 | k1_tarski(C_31)=A_29 | k1_tarski(B_30)=A_29 | k1_xboole_0=A_29 | ~r1_tarski(A_29, k2_tarski(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.08/2.80  tff(c_3058, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3047, c_36])).
% 8.08/2.80  tff(c_3070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_369, c_255, c_510, c_3058])).
% 8.08/2.80  tff(c_3071, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_68])).
% 8.08/2.80  tff(c_3354, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_3071])).
% 8.08/2.80  tff(c_66, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.80  tff(c_667, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 8.08/2.80  tff(c_3355, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3354, c_667])).
% 8.08/2.80  tff(c_3358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_406, c_3355])).
% 8.08/2.80  tff(c_3359, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_3071])).
% 8.08/2.80  tff(c_3361, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_3359])).
% 8.08/2.80  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.08/2.80  tff(c_18, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.08/2.80  tff(c_558, plain, (![A_86, B_87]: (k5_xboole_0(k5_xboole_0(A_86, B_87), k3_xboole_0(A_86, B_87))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.08/2.80  tff(c_612, plain, (![A_15]: (k5_xboole_0(A_15, k3_xboole_0(A_15, k1_xboole_0))=k2_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_558])).
% 8.08/2.80  tff(c_627, plain, (![A_88]: (k2_xboole_0(A_88, k1_xboole_0)=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_612])).
% 8.08/2.80  tff(c_14, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, k2_xboole_0(C_11, B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.08/2.80  tff(c_662, plain, (![A_89, A_90]: (r1_tarski(A_89, A_90) | ~r1_tarski(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_627, c_14])).
% 8.08/2.80  tff(c_670, plain, (![A_91]: (r1_tarski(k1_xboole_0, A_91))), inference(resolution, [status(thm)], [c_10, c_662])).
% 8.08/2.80  tff(c_16, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.08/2.80  tff(c_682, plain, (![A_91]: (k3_xboole_0(k1_xboole_0, A_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_670, c_16])).
% 8.08/2.80  tff(c_394, plain, (![B_70]: (k4_xboole_0(k1_xboole_0, B_70)=k3_xboole_0(k1_xboole_0, B_70))), inference(superposition, [status(thm), theory('equality')], [c_164, c_371])).
% 8.08/2.80  tff(c_683, plain, (![B_70]: (k4_xboole_0(k1_xboole_0, B_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_682, c_394])).
% 8.08/2.80  tff(c_3372, plain, (![B_70]: (k4_xboole_0('#skF_1', B_70)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3361, c_3361, c_683])).
% 8.08/2.80  tff(c_3370, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3361, c_667])).
% 8.08/2.80  tff(c_3878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3372, c_3370])).
% 8.08/2.80  tff(c_3879, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_3359])).
% 8.08/2.80  tff(c_3881, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_3879])).
% 8.08/2.80  tff(c_40, plain, (![C_31, B_30]: (r1_tarski(k1_tarski(C_31), k2_tarski(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.08/2.80  tff(c_256, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.08/2.80  tff(c_823, plain, (![C_96, B_97]: (k3_xboole_0(k1_tarski(C_96), k2_tarski(B_97, C_96))=k1_tarski(C_96))), inference(resolution, [status(thm)], [c_40, c_256])).
% 8.08/2.80  tff(c_836, plain, (![C_96, B_97]: (k5_xboole_0(k1_tarski(C_96), k1_tarski(C_96))=k4_xboole_0(k1_tarski(C_96), k2_tarski(B_97, C_96)))), inference(superposition, [status(thm), theory('equality')], [c_823, c_12])).
% 8.08/2.80  tff(c_849, plain, (![C_96, B_97]: (k4_xboole_0(k1_tarski(C_96), k2_tarski(B_97, C_96))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_836])).
% 8.08/2.80  tff(c_3885, plain, (![B_97]: (k4_xboole_0('#skF_1', k2_tarski(B_97, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3881, c_849])).
% 8.08/2.80  tff(c_4447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3885, c_667])).
% 8.08/2.80  tff(c_4448, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_3879])).
% 8.08/2.80  tff(c_42, plain, (![B_30, C_31]: (r1_tarski(k1_tarski(B_30), k2_tarski(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.08/2.80  tff(c_275, plain, (![B_30, C_31]: (k3_xboole_0(k1_tarski(B_30), k2_tarski(B_30, C_31))=k1_tarski(B_30))), inference(resolution, [status(thm)], [c_42, c_256])).
% 8.08/2.80  tff(c_4462, plain, (![C_31]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_31))=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4448, c_275])).
% 8.08/2.80  tff(c_4527, plain, (![C_175]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_175))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4448, c_4462])).
% 8.08/2.80  tff(c_4544, plain, (![C_175]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_175))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4527, c_12])).
% 8.08/2.80  tff(c_4554, plain, (![C_175]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_175))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4544])).
% 8.08/2.80  tff(c_4624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4554, c_667])).
% 8.08/2.80  tff(c_4625, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 8.08/2.80  tff(c_5421, plain, (![A_200, B_201]: (k5_xboole_0(A_200, k4_xboole_0(A_200, B_201))=k3_xboole_0(A_200, B_201))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4911])).
% 8.08/2.80  tff(c_5466, plain, (k3_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4625, c_5421])).
% 8.08/2.80  tff(c_5494, plain, (k3_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5466])).
% 8.08/2.80  tff(c_5505, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6')), '#skF_4')=k2_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5494, c_28])).
% 8.08/2.80  tff(c_5511, plain, (k2_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4985, c_5505])).
% 8.08/2.80  tff(c_6092, plain, (r1_tarski('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5511, c_22])).
% 8.08/2.80  tff(c_6101, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6092, c_36])).
% 8.08/2.80  tff(c_6110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_369, c_255, c_510, c_6101])).
% 8.08/2.80  tff(c_6111, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 8.08/2.80  tff(c_6112, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 8.08/2.80  tff(c_52, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.80  tff(c_6581, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6112, c_52])).
% 8.08/2.80  tff(c_6582, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_6581])).
% 8.08/2.80  tff(c_6607, plain, (![A_15]: (k5_xboole_0(A_15, '#skF_1')=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_6582, c_20])).
% 8.08/2.80  tff(c_6420, plain, (![A_229, B_230]: (k5_xboole_0(k5_xboole_0(A_229, B_230), k3_xboole_0(A_229, B_230))=k2_xboole_0(A_229, B_230))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.08/2.80  tff(c_6495, plain, (![A_15]: (k5_xboole_0(A_15, k3_xboole_0(A_15, k1_xboole_0))=k2_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_6420])).
% 8.08/2.80  tff(c_6518, plain, (![A_231]: (k2_xboole_0(A_231, k1_xboole_0)=A_231)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_6495])).
% 8.08/2.80  tff(c_6530, plain, (![A_9, A_231]: (r1_tarski(A_9, A_231) | ~r1_tarski(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6518, c_14])).
% 8.08/2.80  tff(c_7195, plain, (![A_255, A_256]: (r1_tarski(A_255, A_256) | ~r1_tarski(A_255, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6582, c_6530])).
% 8.08/2.80  tff(c_7237, plain, (![A_259]: (r1_tarski('#skF_1', A_259))), inference(resolution, [status(thm)], [c_10, c_7195])).
% 8.08/2.80  tff(c_7267, plain, (![A_260]: (k3_xboole_0('#skF_1', A_260)='#skF_1')), inference(resolution, [status(thm)], [c_7237, c_16])).
% 8.08/2.80  tff(c_7278, plain, (![A_260]: (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', A_260))), inference(superposition, [status(thm), theory('equality')], [c_7267, c_12])).
% 8.08/2.80  tff(c_7303, plain, (![A_260]: (k4_xboole_0('#skF_1', A_260)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6607, c_7278])).
% 8.08/2.80  tff(c_6113, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 8.08/2.80  tff(c_6592, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6582, c_6113])).
% 8.08/2.80  tff(c_7408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7303, c_6592])).
% 8.08/2.80  tff(c_7409, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_6581])).
% 8.08/2.80  tff(c_7856, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_7409])).
% 8.08/2.80  tff(c_7857, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7856, c_6113])).
% 8.08/2.80  tff(c_7860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_406, c_7857])).
% 8.08/2.80  tff(c_7861, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_7409])).
% 8.08/2.80  tff(c_7863, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_7861])).
% 8.08/2.80  tff(c_6384, plain, (![B_225, C_226]: (k3_xboole_0(k1_tarski(B_225), k2_tarski(B_225, C_226))=k1_tarski(B_225))), inference(resolution, [status(thm)], [c_42, c_256])).
% 8.08/2.80  tff(c_6390, plain, (![B_225, C_226]: (k5_xboole_0(k1_tarski(B_225), k1_tarski(B_225))=k4_xboole_0(k1_tarski(B_225), k2_tarski(B_225, C_226)))), inference(superposition, [status(thm), theory('equality')], [c_6384, c_12])).
% 8.08/2.80  tff(c_6401, plain, (![B_225, C_226]: (k4_xboole_0(k1_tarski(B_225), k2_tarski(B_225, C_226))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6390])).
% 8.08/2.80  tff(c_7867, plain, (![C_226]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_226))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7863, c_6401])).
% 8.08/2.80  tff(c_8272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7867, c_6113])).
% 8.08/2.80  tff(c_8273, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_7861])).
% 8.08/2.80  tff(c_8349, plain, (![B_293]: (r1_tarski('#skF_1', k2_tarski(B_293, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8273, c_40])).
% 8.08/2.80  tff(c_8419, plain, (![B_296]: (k3_xboole_0('#skF_1', k2_tarski(B_296, '#skF_3'))='#skF_1')), inference(resolution, [status(thm)], [c_8349, c_16])).
% 8.08/2.80  tff(c_8430, plain, (![B_296]: (k4_xboole_0('#skF_1', k2_tarski(B_296, '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8419, c_12])).
% 8.08/2.80  tff(c_8442, plain, (![B_296]: (k4_xboole_0('#skF_1', k2_tarski(B_296, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8430])).
% 8.08/2.80  tff(c_8734, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8442, c_6113])).
% 8.08/2.80  tff(c_8736, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 8.08/2.80  tff(c_8828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6111, c_8736])).
% 8.08/2.80  tff(c_8830, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 8.08/2.80  tff(c_60, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.80  tff(c_9489, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8830, c_60])).
% 8.08/2.80  tff(c_9490, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_9489])).
% 8.08/2.80  tff(c_9128, plain, (![A_323, B_324]: (k5_xboole_0(k5_xboole_0(A_323, B_324), k3_xboole_0(A_323, B_324))=k2_xboole_0(A_323, B_324))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.08/2.80  tff(c_9188, plain, (![A_15]: (k5_xboole_0(A_15, k3_xboole_0(A_15, k1_xboole_0))=k2_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_9128])).
% 8.08/2.80  tff(c_9204, plain, (![A_325]: (k2_xboole_0(A_325, k1_xboole_0)=A_325)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_9188])).
% 8.08/2.80  tff(c_9258, plain, (![A_326, A_327]: (r1_tarski(A_326, A_327) | ~r1_tarski(A_326, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9204, c_14])).
% 8.08/2.80  tff(c_9266, plain, (![A_328]: (r1_tarski(k1_xboole_0, A_328))), inference(resolution, [status(thm)], [c_10, c_9258])).
% 8.08/2.80  tff(c_9278, plain, (![A_328]: (k3_xboole_0(k1_xboole_0, A_328)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9266, c_16])).
% 8.08/2.80  tff(c_8963, plain, (![B_310]: (k4_xboole_0(k1_xboole_0, B_310)=k3_xboole_0(k1_xboole_0, B_310))), inference(superposition, [status(thm), theory('equality')], [c_164, c_8931])).
% 8.08/2.80  tff(c_9279, plain, (![B_310]: (k4_xboole_0(k1_xboole_0, B_310)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9278, c_8963])).
% 8.08/2.80  tff(c_9493, plain, (![B_310]: (k4_xboole_0('#skF_1', B_310)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9490, c_9490, c_9279])).
% 8.08/2.80  tff(c_8829, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 8.08/2.80  tff(c_9502, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9490, c_8829])).
% 8.08/2.80  tff(c_9776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9493, c_9502])).
% 8.08/2.80  tff(c_9777, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_9489])).
% 8.08/2.80  tff(c_10311, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_9777])).
% 8.08/2.80  tff(c_10312, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10311, c_8829])).
% 8.08/2.80  tff(c_10315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8978, c_10312])).
% 8.08/2.80  tff(c_10316, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_9777])).
% 8.08/2.80  tff(c_10318, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_10316])).
% 8.08/2.80  tff(c_10338, plain, (![C_356]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_356)))), inference(superposition, [status(thm), theory('equality')], [c_10318, c_42])).
% 8.08/2.80  tff(c_10364, plain, (![C_358]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_358))='#skF_1')), inference(resolution, [status(thm)], [c_10338, c_16])).
% 8.08/2.80  tff(c_10372, plain, (![C_358]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_358))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10364, c_12])).
% 8.08/2.80  tff(c_10381, plain, (![C_358]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_358))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10372])).
% 8.08/2.80  tff(c_10465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10381, c_8829])).
% 8.08/2.80  tff(c_10466, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_10316])).
% 8.08/2.80  tff(c_10487, plain, (![B_363]: (r1_tarski('#skF_1', k2_tarski(B_363, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10466, c_40])).
% 8.08/2.80  tff(c_10513, plain, (![B_365]: (k3_xboole_0('#skF_1', k2_tarski(B_365, '#skF_3'))='#skF_1')), inference(resolution, [status(thm)], [c_10487, c_16])).
% 8.08/2.80  tff(c_10521, plain, (![B_365]: (k4_xboole_0('#skF_1', k2_tarski(B_365, '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10513, c_12])).
% 8.08/2.80  tff(c_10530, plain, (![B_365]: (k4_xboole_0('#skF_1', k2_tarski(B_365, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10521])).
% 8.08/2.80  tff(c_10614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10530, c_8829])).
% 8.08/2.80  tff(c_10616, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_54])).
% 8.08/2.80  tff(c_56, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.80  tff(c_11504, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10616, c_56])).
% 8.08/2.80  tff(c_11505, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_11504])).
% 8.08/2.80  tff(c_11531, plain, (![A_15]: (k5_xboole_0(A_15, '#skF_1')=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_11505, c_20])).
% 8.08/2.80  tff(c_11330, plain, (![A_420, B_421]: (k5_xboole_0(k5_xboole_0(A_420, B_421), k3_xboole_0(A_420, B_421))=k2_xboole_0(A_420, B_421))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.08/2.80  tff(c_11408, plain, (![A_15]: (k5_xboole_0(A_15, k3_xboole_0(A_15, k1_xboole_0))=k2_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_11330])).
% 8.08/2.80  tff(c_11432, plain, (![A_422]: (k2_xboole_0(A_422, k1_xboole_0)=A_422)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_11408])).
% 8.08/2.80  tff(c_11445, plain, (![A_9, A_422]: (r1_tarski(A_9, A_422) | ~r1_tarski(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11432, c_14])).
% 8.08/2.80  tff(c_12065, plain, (![A_444, A_445]: (r1_tarski(A_444, A_445) | ~r1_tarski(A_444, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11505, c_11445])).
% 8.08/2.80  tff(c_12073, plain, (![A_446]: (r1_tarski('#skF_1', A_446))), inference(resolution, [status(thm)], [c_10, c_12065])).
% 8.08/2.80  tff(c_12129, plain, (![A_450]: (k3_xboole_0('#skF_1', A_450)='#skF_1')), inference(resolution, [status(thm)], [c_12073, c_16])).
% 8.08/2.80  tff(c_12140, plain, (![A_450]: (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', A_450))), inference(superposition, [status(thm), theory('equality')], [c_12129, c_12])).
% 8.08/2.80  tff(c_12165, plain, (![A_450]: (k4_xboole_0('#skF_1', A_450)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11531, c_12140])).
% 8.08/2.80  tff(c_10615, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 8.08/2.80  tff(c_11525, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11505, c_10615])).
% 8.08/2.80  tff(c_12221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12165, c_11525])).
% 8.08/2.80  tff(c_12222, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_11504])).
% 8.08/2.80  tff(c_12682, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_12222])).
% 8.08/2.80  tff(c_12683, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12682, c_10615])).
% 8.08/2.80  tff(c_12686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10838, c_12683])).
% 8.08/2.80  tff(c_12687, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_12222])).
% 8.08/2.80  tff(c_12689, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_12687])).
% 8.08/2.80  tff(c_10649, plain, (![A_372, B_373]: (k3_xboole_0(A_372, B_373)=A_372 | ~r1_tarski(A_372, B_373))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.08/2.80  tff(c_10680, plain, (![B_30, C_31]: (k3_xboole_0(k1_tarski(B_30), k2_tarski(B_30, C_31))=k1_tarski(B_30))), inference(resolution, [status(thm)], [c_42, c_10649])).
% 8.08/2.80  tff(c_12709, plain, (![C_31]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_31))=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12689, c_10680])).
% 8.08/2.80  tff(c_12824, plain, (![C_473]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_473))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12689, c_12709])).
% 8.08/2.80  tff(c_12835, plain, (![C_473]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_473))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12824, c_12])).
% 8.08/2.80  tff(c_12847, plain, (![C_473]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_473))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12835])).
% 8.08/2.80  tff(c_13098, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12847, c_10615])).
% 8.08/2.80  tff(c_13099, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_12687])).
% 8.08/2.80  tff(c_10681, plain, (![C_31, B_30]: (k3_xboole_0(k1_tarski(C_31), k2_tarski(B_30, C_31))=k1_tarski(C_31))), inference(resolution, [status(thm)], [c_40, c_10649])).
% 8.08/2.80  tff(c_13107, plain, (![B_30]: (k3_xboole_0('#skF_1', k2_tarski(B_30, '#skF_3'))=k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13099, c_10681])).
% 8.08/2.80  tff(c_13185, plain, (![B_483]: (k3_xboole_0('#skF_1', k2_tarski(B_483, '#skF_3'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13099, c_13107])).
% 8.08/2.80  tff(c_13196, plain, (![B_483]: (k4_xboole_0('#skF_1', k2_tarski(B_483, '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_13185, c_12])).
% 8.08/2.80  tff(c_13208, plain, (![B_483]: (k4_xboole_0('#skF_1', k2_tarski(B_483, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_13196])).
% 8.08/2.80  tff(c_13509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13208, c_10615])).
% 8.08/2.80  tff(c_13511, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_62])).
% 8.08/2.80  tff(c_13515, plain, (![A_21]: (k5_xboole_0(A_21, A_21)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13511, c_26])).
% 8.08/2.80  tff(c_13806, plain, (![A_523, B_524]: (k5_xboole_0(A_523, k3_xboole_0(A_523, B_524))=k4_xboole_0(A_523, B_524))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.08/2.80  tff(c_13835, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_13806])).
% 8.08/2.80  tff(c_13842, plain, (![A_3]: (k4_xboole_0(A_3, A_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13515, c_13835])).
% 8.08/2.80  tff(c_44, plain, (![B_30, C_31]: (r1_tarski(k1_xboole_0, k2_tarski(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.08/2.80  tff(c_13512, plain, (![B_30, C_31]: (r1_tarski('#skF_4', k2_tarski(B_30, C_31)))), inference(demodulation, [status(thm), theory('equality')], [c_13511, c_44])).
% 8.08/2.80  tff(c_13676, plain, (![A_505, B_506]: (k3_xboole_0(A_505, B_506)=A_505 | ~r1_tarski(A_505, B_506))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.08/2.80  tff(c_13697, plain, (![B_30, C_31]: (k3_xboole_0('#skF_4', k2_tarski(B_30, C_31))='#skF_4')), inference(resolution, [status(thm)], [c_13512, c_13676])).
% 8.08/2.80  tff(c_13582, plain, (![B_502, A_503]: (k5_xboole_0(B_502, A_503)=k5_xboole_0(A_503, B_502))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.08/2.80  tff(c_13513, plain, (![A_15]: (k5_xboole_0(A_15, '#skF_4')=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_13511, c_20])).
% 8.08/2.80  tff(c_13598, plain, (![A_503]: (k5_xboole_0('#skF_4', A_503)=A_503)), inference(superposition, [status(thm), theory('equality')], [c_13582, c_13513])).
% 8.08/2.80  tff(c_13829, plain, (![B_524]: (k4_xboole_0('#skF_4', B_524)=k3_xboole_0('#skF_4', B_524))), inference(superposition, [status(thm), theory('equality')], [c_13598, c_13806])).
% 8.08/2.80  tff(c_64, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.08/2.80  tff(c_14446, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13511, c_13511, c_64])).
% 8.08/2.80  tff(c_14447, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_14446])).
% 8.08/2.80  tff(c_13510, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 8.08/2.80  tff(c_13576, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13511, c_13510])).
% 8.08/2.80  tff(c_14448, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_2', '#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14447, c_13576])).
% 8.08/2.80  tff(c_14451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13697, c_13829, c_14448])).
% 8.08/2.80  tff(c_14452, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_14446])).
% 8.08/2.80  tff(c_14475, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_14452])).
% 8.08/2.80  tff(c_14476, plain, (k4_xboole_0('#skF_1', '#skF_1')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14475, c_13576])).
% 8.08/2.80  tff(c_14479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13842, c_14476])).
% 8.08/2.80  tff(c_14480, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_14452])).
% 8.08/2.80  tff(c_14576, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_14480])).
% 8.08/2.80  tff(c_14607, plain, (![C_553]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_553)))), inference(superposition, [status(thm), theory('equality')], [c_14576, c_42])).
% 8.08/2.80  tff(c_14638, plain, (![C_555]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_555))='#skF_1')), inference(resolution, [status(thm)], [c_14607, c_16])).
% 8.08/2.80  tff(c_14646, plain, (![C_555]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_555))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_14638, c_12])).
% 8.08/2.80  tff(c_14658, plain, (![C_555]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_555))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13515, c_14646])).
% 8.08/2.80  tff(c_14963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14658, c_13576])).
% 8.08/2.80  tff(c_14964, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_14480])).
% 8.08/2.80  tff(c_14985, plain, (![B_562]: (r1_tarski('#skF_1', k2_tarski(B_562, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_14964, c_40])).
% 8.08/2.80  tff(c_15184, plain, (![B_568]: (k3_xboole_0('#skF_1', k2_tarski(B_568, '#skF_3'))='#skF_1')), inference(resolution, [status(thm)], [c_14985, c_16])).
% 8.08/2.80  tff(c_15195, plain, (![B_568]: (k4_xboole_0('#skF_1', k2_tarski(B_568, '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_15184, c_12])).
% 8.08/2.80  tff(c_15208, plain, (![B_568]: (k4_xboole_0('#skF_1', k2_tarski(B_568, '#skF_3'))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13515, c_15195])).
% 8.08/2.80  tff(c_15354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15208, c_13576])).
% 8.08/2.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.08/2.80  
% 8.08/2.80  Inference rules
% 8.08/2.80  ----------------------
% 8.08/2.80  #Ref     : 0
% 8.08/2.80  #Sup     : 3754
% 8.08/2.80  #Fact    : 0
% 8.08/2.80  #Define  : 0
% 8.08/2.80  #Split   : 28
% 8.08/2.80  #Chain   : 0
% 8.08/2.80  #Close   : 0
% 8.08/2.80  
% 8.08/2.80  Ordering : KBO
% 8.08/2.80  
% 8.08/2.80  Simplification rules
% 8.08/2.80  ----------------------
% 8.08/2.80  #Subsume      : 122
% 8.08/2.80  #Demod        : 2635
% 8.08/2.80  #Tautology    : 2520
% 8.08/2.80  #SimpNegUnit  : 64
% 8.08/2.80  #BackRed      : 134
% 8.08/2.80  
% 8.08/2.80  #Partial instantiations: 0
% 8.08/2.80  #Strategies tried      : 1
% 8.08/2.80  
% 8.08/2.80  Timing (in seconds)
% 8.08/2.80  ----------------------
% 8.08/2.80  Preprocessing        : 0.33
% 8.08/2.80  Parsing              : 0.17
% 8.08/2.80  CNF conversion       : 0.02
% 8.08/2.81  Main loop            : 1.67
% 8.08/2.81  Inferencing          : 0.51
% 8.08/2.81  Reduction            : 0.73
% 8.08/2.81  Demodulation         : 0.59
% 8.08/2.81  BG Simplification    : 0.06
% 8.08/2.81  Subsumption          : 0.24
% 8.08/2.81  Abstraction          : 0.08
% 8.08/2.81  MUC search           : 0.00
% 8.08/2.81  Cooper               : 0.00
% 8.08/2.81  Total                : 2.07
% 8.08/2.81  Index Insertion      : 0.00
% 8.08/2.81  Index Deletion       : 0.00
% 8.08/2.81  Index Matching       : 0.00
% 8.08/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
