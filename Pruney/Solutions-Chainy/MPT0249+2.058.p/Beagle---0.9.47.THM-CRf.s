%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:31 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 656 expanded)
%              Number of leaves         :   32 ( 234 expanded)
%              Depth                    :   20
%              Number of atoms          :   79 ( 702 expanded)
%              Number of equality atoms :   67 ( 674 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_255,plain,(
    ! [B_77,A_78] :
      ( k1_tarski(B_77) = A_78
      | k1_xboole_0 = A_78
      | ~ r1_tarski(A_78,k1_tarski(B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_274,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_98,c_255])).

tff(c_283,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_274])).

tff(c_285,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_48])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_717,plain,(
    ! [A_93,B_94,C_95] : k5_xboole_0(k5_xboole_0(A_93,B_94),C_95) = k5_xboole_0(A_93,k5_xboole_0(B_94,C_95)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_162,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_150])).

tff(c_165,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_162])).

tff(c_178,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_196,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_178])).

tff(c_199,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_196])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_159,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_150])).

tff(c_237,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_159])).

tff(c_1500,plain,(
    ! [A_119,B_120] : k5_xboole_0(A_119,k5_xboole_0(B_120,k5_xboole_0(A_119,B_120))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_237])).

tff(c_1110,plain,(
    ! [A_106,C_107] : k5_xboole_0(A_106,k5_xboole_0(A_106,C_107)) = k5_xboole_0(k1_xboole_0,C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_717])).

tff(c_1197,plain,(
    ! [A_1] : k5_xboole_0(k1_xboole_0,A_1) = k5_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_1110])).

tff(c_1221,plain,(
    ! [A_1] : k5_xboole_0(k1_xboole_0,A_1) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1197])).

tff(c_766,plain,(
    ! [A_1,C_95] : k5_xboole_0(A_1,k5_xboole_0(A_1,C_95)) = k5_xboole_0(k1_xboole_0,C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_717])).

tff(c_1223,plain,(
    ! [A_1,C_95] : k5_xboole_0(A_1,k5_xboole_0(A_1,C_95)) = C_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1221,c_766])).

tff(c_1508,plain,(
    ! [B_120,A_119] : k5_xboole_0(B_120,k5_xboole_0(A_119,B_120)) = k5_xboole_0(A_119,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1500,c_1223])).

tff(c_1597,plain,(
    ! [B_120,A_119] : k5_xboole_0(B_120,k5_xboole_0(A_119,B_120)) = A_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1508])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] : k5_xboole_0(k5_xboole_0(A_13,B_14),C_15) = k5_xboole_0(A_13,k5_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1615,plain,(
    ! [B_121,A_122] : k5_xboole_0(B_121,k5_xboole_0(A_122,B_121)) = A_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1508])).

tff(c_1692,plain,(
    ! [A_3,B_4] : k5_xboole_0(k3_xboole_0(A_3,B_4),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1615])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(k5_xboole_0(A_16,B_17),k3_xboole_0(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4752,plain,(
    ! [A_195,B_196,C_197] : k5_xboole_0(k5_xboole_0(A_195,B_196),k5_xboole_0(k3_xboole_0(A_195,B_196),C_197)) = k5_xboole_0(k2_xboole_0(A_195,B_196),C_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_717])).

tff(c_4860,plain,(
    ! [A_3,B_4] : k5_xboole_0(k2_xboole_0(A_3,B_4),k4_xboole_0(A_3,B_4)) = k5_xboole_0(k5_xboole_0(A_3,B_4),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_1692,c_4752])).

tff(c_5019,plain,(
    ! [A_198,B_199] : k5_xboole_0(k2_xboole_0(A_198,B_199),k4_xboole_0(A_198,B_199)) = B_199 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1597,c_16,c_4860])).

tff(c_5097,plain,(
    k5_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_5019])).

tff(c_1360,plain,(
    ! [A_116,C_117] : k5_xboole_0(A_116,k5_xboole_0(A_116,C_117)) = C_117 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1221,c_766])).

tff(c_1420,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1360])).

tff(c_5136,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5097,c_1420])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_187,plain,(
    ! [A_69,B_70] : r1_tarski(k3_xboole_0(A_69,B_70),A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_8])).

tff(c_34,plain,(
    ! [B_47,A_46] :
      ( k1_tarski(B_47) = A_46
      | k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,k1_tarski(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_290,plain,(
    ! [A_46] :
      ( k1_tarski('#skF_1') = A_46
      | k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_34])).

tff(c_317,plain,(
    ! [A_79] :
      ( A_79 = '#skF_2'
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_290])).

tff(c_334,plain,(
    ! [B_70] :
      ( k3_xboole_0('#skF_2',B_70) = '#skF_2'
      | k3_xboole_0('#skF_2',B_70) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_187,c_317])).

tff(c_5217,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5136,c_334])).

tff(c_5235,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5136,c_5217])).

tff(c_5237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_46,c_5235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.88  
% 4.55/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.89  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.55/1.89  
% 4.55/1.89  %Foreground sorts:
% 4.55/1.89  
% 4.55/1.89  
% 4.55/1.89  %Background operators:
% 4.55/1.89  
% 4.55/1.89  
% 4.55/1.89  %Foreground operators:
% 4.55/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.55/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.55/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/1.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.55/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.55/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.55/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.55/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.55/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.55/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.55/1.89  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.89  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.89  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.55/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.55/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.55/1.89  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.89  
% 4.55/1.90  tff(f_78, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 4.55/1.90  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.55/1.90  tff(f_63, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.55/1.90  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.55/1.90  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.55/1.90  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.55/1.90  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.55/1.90  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.55/1.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.55/1.90  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.55/1.90  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.55/1.90  tff(c_42, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.55/1.90  tff(c_46, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.55/1.90  tff(c_44, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.55/1.90  tff(c_48, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.55/1.90  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.55/1.90  tff(c_98, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_14])).
% 4.55/1.90  tff(c_255, plain, (![B_77, A_78]: (k1_tarski(B_77)=A_78 | k1_xboole_0=A_78 | ~r1_tarski(A_78, k1_tarski(B_77)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.55/1.90  tff(c_274, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_98, c_255])).
% 4.55/1.90  tff(c_283, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_274])).
% 4.55/1.90  tff(c_285, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_48])).
% 4.55/1.90  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.55/1.90  tff(c_717, plain, (![A_93, B_94, C_95]: (k5_xboole_0(k5_xboole_0(A_93, B_94), C_95)=k5_xboole_0(A_93, k5_xboole_0(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.55/1.90  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.55/1.90  tff(c_150, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.55/1.90  tff(c_162, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_150])).
% 4.55/1.90  tff(c_165, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_162])).
% 4.55/1.90  tff(c_178, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.90  tff(c_196, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_178])).
% 4.55/1.90  tff(c_199, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_196])).
% 4.55/1.90  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.55/1.90  tff(c_159, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_150])).
% 4.55/1.90  tff(c_237, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_199, c_159])).
% 4.55/1.90  tff(c_1500, plain, (![A_119, B_120]: (k5_xboole_0(A_119, k5_xboole_0(B_120, k5_xboole_0(A_119, B_120)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_717, c_237])).
% 4.55/1.90  tff(c_1110, plain, (![A_106, C_107]: (k5_xboole_0(A_106, k5_xboole_0(A_106, C_107))=k5_xboole_0(k1_xboole_0, C_107))), inference(superposition, [status(thm), theory('equality')], [c_237, c_717])).
% 4.55/1.90  tff(c_1197, plain, (![A_1]: (k5_xboole_0(k1_xboole_0, A_1)=k5_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_237, c_1110])).
% 4.55/1.90  tff(c_1221, plain, (![A_1]: (k5_xboole_0(k1_xboole_0, A_1)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1197])).
% 4.55/1.90  tff(c_766, plain, (![A_1, C_95]: (k5_xboole_0(A_1, k5_xboole_0(A_1, C_95))=k5_xboole_0(k1_xboole_0, C_95))), inference(superposition, [status(thm), theory('equality')], [c_237, c_717])).
% 4.55/1.90  tff(c_1223, plain, (![A_1, C_95]: (k5_xboole_0(A_1, k5_xboole_0(A_1, C_95))=C_95)), inference(demodulation, [status(thm), theory('equality')], [c_1221, c_766])).
% 4.55/1.90  tff(c_1508, plain, (![B_120, A_119]: (k5_xboole_0(B_120, k5_xboole_0(A_119, B_120))=k5_xboole_0(A_119, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1500, c_1223])).
% 4.55/1.90  tff(c_1597, plain, (![B_120, A_119]: (k5_xboole_0(B_120, k5_xboole_0(A_119, B_120))=A_119)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1508])).
% 4.55/1.90  tff(c_16, plain, (![A_13, B_14, C_15]: (k5_xboole_0(k5_xboole_0(A_13, B_14), C_15)=k5_xboole_0(A_13, k5_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.55/1.90  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.55/1.90  tff(c_1615, plain, (![B_121, A_122]: (k5_xboole_0(B_121, k5_xboole_0(A_122, B_121))=A_122)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1508])).
% 4.55/1.90  tff(c_1692, plain, (![A_3, B_4]: (k5_xboole_0(k3_xboole_0(A_3, B_4), k4_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1615])).
% 4.55/1.90  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(k5_xboole_0(A_16, B_17), k3_xboole_0(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.55/1.90  tff(c_4752, plain, (![A_195, B_196, C_197]: (k5_xboole_0(k5_xboole_0(A_195, B_196), k5_xboole_0(k3_xboole_0(A_195, B_196), C_197))=k5_xboole_0(k2_xboole_0(A_195, B_196), C_197))), inference(superposition, [status(thm), theory('equality')], [c_18, c_717])).
% 4.55/1.90  tff(c_4860, plain, (![A_3, B_4]: (k5_xboole_0(k2_xboole_0(A_3, B_4), k4_xboole_0(A_3, B_4))=k5_xboole_0(k5_xboole_0(A_3, B_4), A_3))), inference(superposition, [status(thm), theory('equality')], [c_1692, c_4752])).
% 4.55/1.90  tff(c_5019, plain, (![A_198, B_199]: (k5_xboole_0(k2_xboole_0(A_198, B_199), k4_xboole_0(A_198, B_199))=B_199)), inference(demodulation, [status(thm), theory('equality')], [c_1597, c_16, c_4860])).
% 4.55/1.90  tff(c_5097, plain, (k5_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_285, c_5019])).
% 4.55/1.90  tff(c_1360, plain, (![A_116, C_117]: (k5_xboole_0(A_116, k5_xboole_0(A_116, C_117))=C_117)), inference(demodulation, [status(thm), theory('equality')], [c_1221, c_766])).
% 4.55/1.90  tff(c_1420, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1360])).
% 4.55/1.90  tff(c_5136, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5097, c_1420])).
% 4.55/1.90  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.55/1.90  tff(c_187, plain, (![A_69, B_70]: (r1_tarski(k3_xboole_0(A_69, B_70), A_69))), inference(superposition, [status(thm), theory('equality')], [c_178, c_8])).
% 4.55/1.90  tff(c_34, plain, (![B_47, A_46]: (k1_tarski(B_47)=A_46 | k1_xboole_0=A_46 | ~r1_tarski(A_46, k1_tarski(B_47)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.55/1.90  tff(c_290, plain, (![A_46]: (k1_tarski('#skF_1')=A_46 | k1_xboole_0=A_46 | ~r1_tarski(A_46, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_283, c_34])).
% 4.55/1.90  tff(c_317, plain, (![A_79]: (A_79='#skF_2' | k1_xboole_0=A_79 | ~r1_tarski(A_79, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_290])).
% 4.55/1.90  tff(c_334, plain, (![B_70]: (k3_xboole_0('#skF_2', B_70)='#skF_2' | k3_xboole_0('#skF_2', B_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_187, c_317])).
% 4.55/1.90  tff(c_5217, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5136, c_334])).
% 4.55/1.90  tff(c_5235, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5136, c_5217])).
% 4.55/1.90  tff(c_5237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_46, c_5235])).
% 4.55/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.90  
% 4.55/1.90  Inference rules
% 4.55/1.90  ----------------------
% 4.55/1.90  #Ref     : 0
% 4.55/1.90  #Sup     : 1254
% 4.55/1.90  #Fact    : 3
% 4.55/1.90  #Define  : 0
% 4.55/1.90  #Split   : 1
% 4.55/1.90  #Chain   : 0
% 4.55/1.90  #Close   : 0
% 4.55/1.90  
% 4.55/1.90  Ordering : KBO
% 4.55/1.90  
% 4.55/1.90  Simplification rules
% 4.55/1.90  ----------------------
% 4.55/1.90  #Subsume      : 88
% 4.55/1.90  #Demod        : 1176
% 4.55/1.90  #Tautology    : 793
% 4.55/1.90  #SimpNegUnit  : 30
% 4.55/1.90  #BackRed      : 17
% 4.55/1.90  
% 4.55/1.90  #Partial instantiations: 0
% 4.55/1.90  #Strategies tried      : 1
% 4.55/1.90  
% 4.55/1.90  Timing (in seconds)
% 4.55/1.90  ----------------------
% 4.55/1.90  Preprocessing        : 0.31
% 4.55/1.90  Parsing              : 0.17
% 4.55/1.90  CNF conversion       : 0.02
% 4.55/1.90  Main loop            : 0.83
% 4.55/1.90  Inferencing          : 0.27
% 4.55/1.90  Reduction            : 0.36
% 4.55/1.90  Demodulation         : 0.29
% 4.55/1.90  BG Simplification    : 0.04
% 4.55/1.90  Subsumption          : 0.11
% 4.55/1.90  Abstraction          : 0.05
% 4.55/1.90  MUC search           : 0.00
% 4.55/1.90  Cooper               : 0.00
% 4.55/1.90  Total                : 1.17
% 4.55/1.90  Index Insertion      : 0.00
% 4.55/1.90  Index Deletion       : 0.00
% 4.55/1.90  Index Matching       : 0.00
% 4.55/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
