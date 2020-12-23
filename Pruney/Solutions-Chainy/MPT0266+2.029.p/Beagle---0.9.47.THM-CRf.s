%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:30 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 136 expanded)
%              Number of leaves         :   33 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :   54 ( 120 expanded)
%              Number of equality atoms :   42 ( 107 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_44,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_202,plain,(
    ! [A_89,B_90] : k5_xboole_0(k5_xboole_0(A_89,B_90),k2_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_235,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_202])).

tff(c_241,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12,c_235])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1093,plain,(
    ! [A_124,B_125,C_126,D_127] : k2_xboole_0(k2_tarski(A_124,B_125),k2_tarski(C_126,D_127)) = k2_enumset1(A_124,B_125,C_126,D_127) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1121,plain,(
    ! [C_128,D_129] : k2_enumset1(C_128,D_129,C_128,D_129) = k2_tarski(C_128,D_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_4])).

tff(c_18,plain,(
    ! [D_22,C_21,B_20,A_19] : k2_enumset1(D_22,C_21,B_20,A_19) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1174,plain,(
    ! [D_131,C_132] : k2_enumset1(D_131,C_132,D_131,C_132) = k2_tarski(C_132,D_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_1121,c_18])).

tff(c_1103,plain,(
    ! [C_126,D_127] : k2_enumset1(C_126,D_127,C_126,D_127) = k2_tarski(C_126,D_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_4])).

tff(c_1226,plain,(
    ! [D_138,C_139] : k2_tarski(D_138,C_139) = k2_tarski(C_139,D_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_1174,c_1103])).

tff(c_36,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1317,plain,(
    ! [D_140,C_141] : k3_tarski(k2_tarski(D_140,C_141)) = k2_xboole_0(C_141,D_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_1226,c_36])).

tff(c_1323,plain,(
    ! [D_140,C_141] : k2_xboole_0(D_140,C_141) = k2_xboole_0(C_141,D_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_1317,c_36])).

tff(c_331,plain,(
    ! [A_93,B_94,C_95] : k5_xboole_0(k5_xboole_0(A_93,B_94),C_95) = k5_xboole_0(A_93,k5_xboole_0(B_94,C_95)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_397,plain,(
    ! [A_12,C_95] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_95)) = k5_xboole_0(k1_xboole_0,C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_331])).

tff(c_410,plain,(
    ! [A_12,C_95] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_95)) = C_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_397])).

tff(c_413,plain,(
    ! [A_96,C_97] : k5_xboole_0(A_96,k5_xboole_0(A_96,C_97)) = C_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_397])).

tff(c_528,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k5_xboole_0(B_103,A_102)) = B_103 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_413])).

tff(c_564,plain,(
    ! [A_12,C_95] : k5_xboole_0(k5_xboole_0(A_12,C_95),C_95) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_528])).

tff(c_46,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6355,plain,(
    ! [A_226,B_227] : k5_xboole_0(k5_xboole_0(A_226,B_227),k2_xboole_0(B_227,A_226)) = k3_xboole_0(B_227,A_226) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_202])).

tff(c_9724,plain,(
    ! [A_248,B_249] : k5_xboole_0(k5_xboole_0(A_248,B_249),k3_xboole_0(B_249,A_248)) = k2_xboole_0(B_249,A_248) ),
    inference(superposition,[status(thm),theory(equality)],[c_6355,c_410])).

tff(c_10000,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),k2_tarski('#skF_1','#skF_2')) = k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_9724])).

tff(c_10061,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1323,c_564,c_10000])).

tff(c_14,plain,(
    ! [A_13,B_14] : k5_xboole_0(k5_xboole_0(A_13,B_14),k2_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3321,plain,(
    ! [B_203,A_204,C_205] : k5_xboole_0(k5_xboole_0(B_203,A_204),C_205) = k5_xboole_0(A_204,k5_xboole_0(B_203,C_205)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_331])).

tff(c_3544,plain,(
    ! [B_14,A_13] : k5_xboole_0(B_14,k5_xboole_0(A_13,k2_xboole_0(A_13,B_14))) = k3_xboole_0(A_13,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3321])).

tff(c_10067,plain,(
    k5_xboole_0(k2_tarski('#skF_1','#skF_2'),k5_xboole_0('#skF_3','#skF_3')) = k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10061,c_3544])).

tff(c_10082,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_2,c_12,c_10067])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10094,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10082,c_8])).

tff(c_42,plain,(
    ! [A_56,C_58,B_57] :
      ( r2_hidden(A_56,C_58)
      | ~ r1_tarski(k2_tarski(A_56,B_57),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10655,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_10094,c_42])).

tff(c_10660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_10655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.82/3.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/3.01  
% 7.82/3.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/3.01  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.82/3.01  
% 7.82/3.01  %Foreground sorts:
% 7.82/3.01  
% 7.82/3.01  
% 7.82/3.01  %Background operators:
% 7.82/3.01  
% 7.82/3.01  
% 7.82/3.01  %Foreground operators:
% 7.82/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.82/3.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.82/3.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.82/3.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.82/3.01  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.82/3.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.82/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.82/3.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.82/3.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.82/3.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.82/3.01  tff('#skF_2', type, '#skF_2': $i).
% 7.82/3.01  tff('#skF_3', type, '#skF_3': $i).
% 7.82/3.01  tff('#skF_1', type, '#skF_1': $i).
% 7.82/3.01  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.82/3.01  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.82/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.82/3.01  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.82/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.82/3.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.82/3.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.82/3.01  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.82/3.01  
% 7.82/3.03  tff(f_72, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 7.82/3.03  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.82/3.03  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.82/3.03  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.82/3.03  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.82/3.03  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.82/3.03  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 7.82/3.03  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 7.82/3.03  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.82/3.03  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.82/3.03  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.82/3.03  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 7.82/3.03  tff(c_44, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.82/3.03  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.82/3.03  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.82/3.03  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.82/3.03  tff(c_202, plain, (![A_89, B_90]: (k5_xboole_0(k5_xboole_0(A_89, B_90), k2_xboole_0(A_89, B_90))=k3_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.82/3.03  tff(c_235, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_202])).
% 7.82/3.03  tff(c_241, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12, c_235])).
% 7.82/3.03  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.82/3.03  tff(c_1093, plain, (![A_124, B_125, C_126, D_127]: (k2_xboole_0(k2_tarski(A_124, B_125), k2_tarski(C_126, D_127))=k2_enumset1(A_124, B_125, C_126, D_127))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.82/3.03  tff(c_1121, plain, (![C_128, D_129]: (k2_enumset1(C_128, D_129, C_128, D_129)=k2_tarski(C_128, D_129))), inference(superposition, [status(thm), theory('equality')], [c_1093, c_4])).
% 7.82/3.03  tff(c_18, plain, (![D_22, C_21, B_20, A_19]: (k2_enumset1(D_22, C_21, B_20, A_19)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.82/3.03  tff(c_1174, plain, (![D_131, C_132]: (k2_enumset1(D_131, C_132, D_131, C_132)=k2_tarski(C_132, D_131))), inference(superposition, [status(thm), theory('equality')], [c_1121, c_18])).
% 7.82/3.03  tff(c_1103, plain, (![C_126, D_127]: (k2_enumset1(C_126, D_127, C_126, D_127)=k2_tarski(C_126, D_127))), inference(superposition, [status(thm), theory('equality')], [c_1093, c_4])).
% 7.82/3.03  tff(c_1226, plain, (![D_138, C_139]: (k2_tarski(D_138, C_139)=k2_tarski(C_139, D_138))), inference(superposition, [status(thm), theory('equality')], [c_1174, c_1103])).
% 7.82/3.03  tff(c_36, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.82/3.03  tff(c_1317, plain, (![D_140, C_141]: (k3_tarski(k2_tarski(D_140, C_141))=k2_xboole_0(C_141, D_140))), inference(superposition, [status(thm), theory('equality')], [c_1226, c_36])).
% 7.82/3.03  tff(c_1323, plain, (![D_140, C_141]: (k2_xboole_0(D_140, C_141)=k2_xboole_0(C_141, D_140))), inference(superposition, [status(thm), theory('equality')], [c_1317, c_36])).
% 7.82/3.03  tff(c_331, plain, (![A_93, B_94, C_95]: (k5_xboole_0(k5_xboole_0(A_93, B_94), C_95)=k5_xboole_0(A_93, k5_xboole_0(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.82/3.03  tff(c_397, plain, (![A_12, C_95]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_95))=k5_xboole_0(k1_xboole_0, C_95))), inference(superposition, [status(thm), theory('equality')], [c_12, c_331])).
% 7.82/3.03  tff(c_410, plain, (![A_12, C_95]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_95))=C_95)), inference(demodulation, [status(thm), theory('equality')], [c_241, c_397])).
% 7.82/3.03  tff(c_413, plain, (![A_96, C_97]: (k5_xboole_0(A_96, k5_xboole_0(A_96, C_97))=C_97)), inference(demodulation, [status(thm), theory('equality')], [c_241, c_397])).
% 7.82/3.03  tff(c_528, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k5_xboole_0(B_103, A_102))=B_103)), inference(superposition, [status(thm), theory('equality')], [c_2, c_413])).
% 7.82/3.03  tff(c_564, plain, (![A_12, C_95]: (k5_xboole_0(k5_xboole_0(A_12, C_95), C_95)=A_12)), inference(superposition, [status(thm), theory('equality')], [c_410, c_528])).
% 7.82/3.03  tff(c_46, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.82/3.03  tff(c_6355, plain, (![A_226, B_227]: (k5_xboole_0(k5_xboole_0(A_226, B_227), k2_xboole_0(B_227, A_226))=k3_xboole_0(B_227, A_226))), inference(superposition, [status(thm), theory('equality')], [c_2, c_202])).
% 7.82/3.03  tff(c_9724, plain, (![A_248, B_249]: (k5_xboole_0(k5_xboole_0(A_248, B_249), k3_xboole_0(B_249, A_248))=k2_xboole_0(B_249, A_248))), inference(superposition, [status(thm), theory('equality')], [c_6355, c_410])).
% 7.82/3.03  tff(c_10000, plain, (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_1', '#skF_2'))=k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46, c_9724])).
% 7.82/3.03  tff(c_10061, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1323, c_564, c_10000])).
% 7.82/3.03  tff(c_14, plain, (![A_13, B_14]: (k5_xboole_0(k5_xboole_0(A_13, B_14), k2_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.82/3.03  tff(c_3321, plain, (![B_203, A_204, C_205]: (k5_xboole_0(k5_xboole_0(B_203, A_204), C_205)=k5_xboole_0(A_204, k5_xboole_0(B_203, C_205)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_331])).
% 7.82/3.03  tff(c_3544, plain, (![B_14, A_13]: (k5_xboole_0(B_14, k5_xboole_0(A_13, k2_xboole_0(A_13, B_14)))=k3_xboole_0(A_13, B_14))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3321])).
% 7.82/3.03  tff(c_10067, plain, (k5_xboole_0(k2_tarski('#skF_1', '#skF_2'), k5_xboole_0('#skF_3', '#skF_3'))=k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10061, c_3544])).
% 7.82/3.03  tff(c_10082, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_2, c_12, c_10067])).
% 7.82/3.03  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.82/3.03  tff(c_10094, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10082, c_8])).
% 7.82/3.03  tff(c_42, plain, (![A_56, C_58, B_57]: (r2_hidden(A_56, C_58) | ~r1_tarski(k2_tarski(A_56, B_57), C_58))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.82/3.03  tff(c_10655, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_10094, c_42])).
% 7.82/3.03  tff(c_10660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_10655])).
% 7.82/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/3.03  
% 7.82/3.03  Inference rules
% 7.82/3.03  ----------------------
% 7.82/3.03  #Ref     : 0
% 7.82/3.03  #Sup     : 2670
% 7.82/3.03  #Fact    : 0
% 7.82/3.03  #Define  : 0
% 7.82/3.03  #Split   : 0
% 7.82/3.03  #Chain   : 0
% 7.82/3.03  #Close   : 0
% 7.82/3.03  
% 7.82/3.03  Ordering : KBO
% 7.82/3.03  
% 7.82/3.03  Simplification rules
% 7.82/3.03  ----------------------
% 7.82/3.03  #Subsume      : 154
% 7.82/3.03  #Demod        : 2672
% 7.82/3.03  #Tautology    : 1284
% 7.82/3.03  #SimpNegUnit  : 1
% 7.82/3.03  #BackRed      : 1
% 7.82/3.03  
% 7.82/3.03  #Partial instantiations: 0
% 7.82/3.03  #Strategies tried      : 1
% 7.82/3.03  
% 7.82/3.03  Timing (in seconds)
% 7.82/3.03  ----------------------
% 7.82/3.03  Preprocessing        : 0.32
% 7.82/3.03  Parsing              : 0.17
% 7.82/3.03  CNF conversion       : 0.02
% 7.82/3.03  Main loop            : 1.95
% 7.82/3.03  Inferencing          : 0.43
% 7.82/3.03  Reduction            : 1.13
% 7.82/3.03  Demodulation         : 1.02
% 7.82/3.03  BG Simplification    : 0.06
% 7.82/3.03  Subsumption          : 0.25
% 7.82/3.03  Abstraction          : 0.09
% 7.82/3.03  MUC search           : 0.00
% 7.82/3.03  Cooper               : 0.00
% 7.82/3.03  Total                : 2.31
% 7.82/3.03  Index Insertion      : 0.00
% 7.82/3.03  Index Deletion       : 0.00
% 7.82/3.03  Index Matching       : 0.00
% 7.82/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
